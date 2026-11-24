//! Static size bounds. The verifier encodes a list or map exactly only up to its declared
//! `max_length`, and a split only up to a bound on its pieces; past that it can refute but
//! not prove. So the subset admits a list or map only where a bound is known statically:
//! literals, values built from bounded parts, and fields and variables that declare
//! `max_length` (their items, through `items` constraints).

use crate::encode::MAX_SLOTS;
use celspresso_check::{CelType, CheckedExpr, Constraints, Reference};
use celspresso_syntax::ast::{ops, Expr, ExprId, ExprKind, Literal};
use std::collections::{HashMap, HashSet};

/// Most elements a declared `max_length` may allow and still be encoded exactly.
pub const MAX_ELEMENTS: u64 = MAX_SLOTS as u64;

/// Most pieces a split may produce (each piece is a string variable; more is slow).
pub const MAX_PIECES: u64 = 32;

/// Longest `string(int)` (`-9223372036854775808`) and `string(bool)` (`false`).
const INT_CHARS: u64 = 20;

/// The declared constraints of the values an expression reads. An expression with an entry
/// comes from a declared input (a variable, a field or an element of one) and is encoded
/// with those constraints; one without an entry has unknown provenance.
pub struct Sizes<'a> {
    c: &'a CheckedExpr,
    cons: HashMap<ExprId, Constraints>,
    /// Reads of comprehension accumulators, which hold what the comprehension built, and
    /// of fields of structs the expression built: values made of parts checked where they
    /// appear.
    accus: HashSet<ExprId>,
    /// Expressions that give a struct the expression itself builds (a literal, a choice
    /// between such, or a `cel.bind` variable holding one).
    built: HashSet<ExprId>,
}

/// A name in scope: its constraints, whether it's an accumulator, and whether it holds a
/// struct the expression built.
type Scope = Vec<(String, Option<Constraints>, bool, bool)>;

/// `t` without nullable and optional wrappers.
fn strip(t: &CelType) -> &CelType {
    match t {
        CelType::Nullable(a) | CelType::Optional(a) => strip(a),
        t => t,
    }
}

/// Whether a value of type `t` is a list or map (possibly nullable or optional).
pub fn is_collection(t: &CelType) -> bool {
    matches!(strip(t), CelType::List(_) | CelType::Map(..))
}

fn children(e: &Expr) -> Vec<&Expr> {
    match &e.kind {
        ExprKind::Literal(_) | ExprKind::Ident(_) => Vec::new(),
        ExprKind::Select { operand, .. } => vec![&**operand],
        ExprKind::Call { target, args, .. } => target.iter().map(|t| &**t).chain(args).collect(),
        ExprKind::List(items) => items.iter().collect(),
        ExprKind::Map(entries) => entries.iter().flat_map(|(k, v)| [k, v]).collect(),
        ExprKind::Struct { fields, .. } => fields.iter().map(|(_, v)| v).collect(),
        ExprKind::Comprehension(c) => vec![&c.iter_range, &c.accu_init, &c.loop_condition, &c.loop_step, &c.result],
    }
}

/// Why `cons` (on a list or map) doesn't bound it, if it doesn't.
fn missing(cons: Option<&Constraints>) -> Option<String> {
    match cons.and_then(|c| c.max_length) {
        None => Some("it has no max_length".into()),
        Some(m) if m > MAX_ELEMENTS => Some(format!("its max_length {m} is above {MAX_ELEMENTS}")),
        Some(_) => None,
    }
}

/// Constraints that hold of a value meeting either `a` or `b`: the larger length, and the
/// join of the items. Everything else is dropped (no claim is safer than a wrong one).
fn join(a: &Constraints, b: &Constraints) -> Constraints {
    let items = match (&a.items, &b.items) {
        (Some(x), Some(y)) => Some(Box::new(join(x, y))),
        _ => None,
    };
    Constraints { max_length: a.max_length.zip(b.max_length).map(|(x, y)| x.max(y)), items, ..Default::default() }
}

impl<'a> Sizes<'a> {
    pub fn new(c: &'a CheckedExpr) -> Self {
        let mut s = Sizes { c, cons: HashMap::new(), accus: HashSet::new(), built: HashSet::new() };
        s.visit(&c.expr, &mut Vec::new());
        s
    }

    fn visit(&mut self, e: &Expr, scope: &mut Scope) {
        if let ExprKind::Ident(n) = &e.kind {
            if let Some((_, _, accu, built)) = scope.iter().rev().find(|(m, ..)| m == n) {
                if *accu {
                    self.accus.insert(e.id);
                }
                if *built {
                    self.built.insert(e.id);
                }
            }
        }
        if let ExprKind::Comprehension(k) = &e.kind {
            self.visit(&k.iter_range, scope);
            self.visit(&k.accu_init, scope);
            // the element (or map value) variable reads the range's items, a map key its keys
            let range = self.cons.get(&k.iter_range.id);
            let items = range.map(|c| c.items.as_deref().cloned().unwrap_or_default());
            let keys = range.map(|c| c.keys.as_deref().cloned().unwrap_or_default());
            let is_map = matches!(strip(self.c.type_of(k.iter_range.id)), CelType::Map(..));
            let (first, second) = match &k.iter_var2 {
                None if is_map => (keys, None),
                None => (items, None),
                Some(_) if is_map => (keys, items),
                Some(_) => (None, items),
            };
            let depth = scope.len();
            scope.push((k.iter_var.clone(), first, false, false));
            if let Some(v2) = &k.iter_var2 {
                scope.push((v2.clone(), second, false, false));
            }
            // `cel.bind` (and an expanded definition) is a comprehension that never loops: its
            // variable is its initial value
            let binds = matches!(k.loop_condition.kind, ExprKind::Literal(Literal::Bool(false)));
            let init = if binds { self.cons.get(&k.accu_init.id).cloned() } else { None };
            let built = binds && self.built.contains(&k.accu_init.id);
            scope.push((k.accu_var.clone(), init, true, built));
            for x in [&k.loop_condition, &k.loop_step, &k.result] {
                self.visit(x, scope);
            }
            scope.truncate(depth);
        } else {
            for k in children(e) {
                self.visit(k, scope);
            }
        }
        match &e.kind {
            ExprKind::Struct { .. } => {
                self.built.insert(e.id);
            }
            ExprKind::Call { target: None, function, args } if function == ops::CONDITIONAL => {
                if let [_, a, b] = args.as_slice() {
                    if self.built.contains(&a.id) && self.built.contains(&b.id) {
                        self.built.insert(e.id);
                    }
                }
            }
            // a field of a built struct holds a value checked where the struct was built
            ExprKind::Select { operand, test_only: false, .. } if self.built.contains(&operand.id) => {
                self.accus.insert(e.id);
            }
            _ => {}
        }
        if let Some(c) = self.own(e, scope) {
            self.cons.insert(e.id, c);
        }
    }

    /// Constraints of `x`'s items (list elements or map values), when `x` is a declared input.
    fn items(&self, x: &Expr) -> Option<Constraints> {
        self.cons.get(&x.id).map(|c| c.items.as_deref().cloned().unwrap_or_default())
    }

    /// Constraints of field `field` of `x`, when `x` is a declared input.
    fn field(&self, x: &Expr, field: &str) -> Option<Constraints> {
        match strip(self.c.type_of(x.id)) {
            CelType::Struct(s) if self.cons.contains_key(&x.id) => {
                self.c.schema.structs.get(s)?.field(field).map(|f| f.constraints.clone())
            }
            CelType::Map(..) => self.items(x),
            _ => None,
        }
    }

    fn own(&self, e: &Expr, scope: &Scope) -> Option<Constraints> {
        // a qualified name (`a.b`) can resolve to a variable at a Select node
        if let Some(Reference::Var(v)) = self.c.refs.get(&e.id) {
            return self.c.schema.vars.get(v).map(|d| d.constraints.clone());
        }
        match &e.kind {
            ExprKind::Ident(n) => scope.iter().rev().find(|(m, ..)| m == n).and_then(|(_, c, ..)| c.clone()),
            ExprKind::Select { operand, field, test_only: false } => self.field(operand, field),
            ExprKind::Call { target: None, function, args } => match (function.as_str(), args.as_slice()) {
                (ops::INDEX | ops::OPT_INDEX, [x, _]) => self.items(x),
                (ops::OPT_SELECT, [x, f]) => match &f.kind {
                    ExprKind::Literal(Literal::String(f)) => self.field(x, f),
                    _ => None,
                },
                _ => None,
            },
            // a split's pieces are no longer than the string
            ExprKind::Call { target: Some(t), function, args } if function == "split" => {
                let piece = Constraints { max_length: Some(self.str_len(t)?), ..Default::default() };
                let n = self.pieces(t, args.first()?)?;
                Some(Constraints { max_length: Some(n), items: Some(Box::new(piece)), ..Default::default() })
            }
            // an optional's value is the value it wraps
            ExprKind::Call { target: Some(t), function, args } if function == "value" && args.is_empty() => {
                matches!(self.c.type_of(t.id), CelType::Optional(_)).then(|| self.cons.get(&t.id).cloned()).flatten()
            }
            // ... or else the default: bounded by whichever is longer
            ExprKind::Call { target: Some(t), function, args } if function == "orValue" => {
                if !matches!(self.c.type_of(t.id), CelType::Optional(_)) {
                    return None;
                }
                let [d] = args.as_slice() else { return None };
                let default = match strip(self.c.type_of(d.id)) {
                    CelType::String => Constraints { max_length: Some(self.str_len(d)?), ..Default::default() },
                    _ => self.cons.get(&d.id)?.clone(),
                };
                Some(join(self.cons.get(&t.id)?, &default))
            }
            _ => None,
        }
    }

    /// Why the list or map `e` evaluates to may be longer than the verifier encodes, if it
    /// may. Values built from parts (literals, `+`, comprehensions, `?:`) are bounded when
    /// their parts are, which are checked where they appear.
    pub fn unbounded(&self, e: &Expr) -> Option<String> {
        let built = match &e.kind {
            ExprKind::List(_) | ExprKind::Map(_) | ExprKind::Comprehension(_) => true,
            ExprKind::Call { function, .. } => matches!(
                function.as_str(),
                ops::ADD
                    | ops::CONDITIONAL
                    | ops::MAP_INSERT
                    | "optional.of"
                    | "optional.ofNonZeroValue"
                    | "optional.none"
                    | "or"
                    | "value"
                    | "orValue"
            ),
            _ => false,
        };
        if built || self.accus.contains(&e.id) {
            return None;
        }
        if let ExprKind::Call { function, target: Some(s), args } = &e.kind {
            if function == "split" {
                return match self.pieces(s, args.first()?) {
                    Some(n) if n <= MAX_PIECES => None,
                    Some(n) => Some(format!(
                        "this split can give up to {n} pieces, more than the {MAX_PIECES} the verifier encodes; \
                         declare a smaller max_length on the string"
                    )),
                    None => Some(
                        "the string being split has no max_length, so its pieces are unbounded; \
                         declare max_length on it"
                            .into(),
                    ),
                };
            }
        }
        let what = describe(e);
        match self.cons.get(&e.id) {
            Some(c) => missing(Some(c)).map(|why| format!("{what}: {why}; declare a max_length of at most {MAX_ELEMENTS}")),
            None => Some(format!(
                "{what} comes from a value the verifier can't bound (only literals and declared fields \
                 or variables with max_length are bounded)"
            )),
        }
    }

    /// Why a comparison of the whole value `e` would compare unbounded lists or maps inside
    /// it (struct fields, nested elements), if it would. `e` itself is checked where it appears.
    pub fn unbounded_inside(&self, e: &Expr) -> Option<String> {
        match &e.kind {
            // a literal's elements are expressions of their own, checked where they appear
            ExprKind::List(items) => items.iter().find_map(|x| self.unbounded_inside(x)),
            ExprKind::Map(entries) => entries.iter().find_map(|(_, v)| self.unbounded_inside(v)),
            _ => inside(self.c, self.c.type_of(e.id), self.cons.get(&e.id), &describe(e), &mut Vec::new()),
        }
    }

    /// Most characters the string `e` may have.
    pub fn str_len(&self, e: &Expr) -> Option<u64> {
        if let Some(c) = self.cons.get(&e.id) {
            let from_options = c.one_of.as_ref().and_then(|opts| {
                opts.iter()
                    .map(|l| match l {
                        Literal::String(s) => Some(s.chars().count() as u64),
                        _ => None,
                    })
                    .try_fold(0u64, |m, n| n.map(|n| m.max(n)))
            });
            if let Some(n) = c.max_length.into_iter().chain(from_options).min() {
                return Some(n);
            }
        }
        let ExprKind::Call { target, function, args } = &e.kind else {
            return match &e.kind {
                ExprKind::Literal(Literal::String(s)) => Some(s.chars().count() as u64),
                _ => None,
            };
        };
        let id = self.c.overload(e.id).unwrap_or("");
        match (function.as_str(), target.as_deref(), args.as_slice()) {
            (ops::ADD, None, [a, b]) if id == "add_string" => self.str_len(a)?.checked_add(self.str_len(b)?),
            (ops::CONDITIONAL, None, [_, a, b]) => Some(self.str_len(a)?.max(self.str_len(b)?)),
            ("substring" | "lowerAscii" | "upperAscii", Some(s), _) => self.str_len(s),
            ("charAt", Some(_), _) => Some(1),
            ("join", Some(xs), _) => {
                let sep = match args.first().map(|a| &a.kind) {
                    None => 0,
                    Some(ExprKind::Literal(Literal::String(t))) => t.chars().count() as u64,
                    Some(_) => self.str_len(&args[0])?,
                };
                let (n, item) = match &xs.kind {
                    ExprKind::List(items) => {
                        let lens: Option<Vec<u64>> = items.iter().map(|x| self.str_len(x)).collect();
                        (items.len() as u64, lens?.into_iter().max().unwrap_or(0))
                    }
                    _ => {
                        let c = self.cons.get(&xs.id)?;
                        (c.max_length?, c.items.as_ref()?.max_length?)
                    }
                };
                n.checked_mul(item)?.checked_add(n.saturating_sub(1).checked_mul(sep)?)
            }
            ("string", None, [_]) if matches!(id, "int64_to_string" | "uint64_to_string" | "bool_to_string") => Some(INT_CHARS),
            ("string", None, [a]) if id == "string_to_string" => self.str_len(a),
            _ => None,
        }
    }

    /// Most pieces `s.split(sep)` may give (a literal separator).
    pub fn pieces(&self, s: &Expr, sep: &Expr) -> Option<u64> {
        let ExprKind::Literal(Literal::String(sep)) = &sep.kind else { return None };
        let m = sep.chars().count() as u64;
        (m > 0).then_some(())?;
        Some(self.str_len(s)? / m + 1)
    }
}

/// `o.xs`-style text for a path, for messages.
fn describe(e: &Expr) -> String {
    fn path(e: &Expr) -> Option<String> {
        match &e.kind {
            ExprKind::Ident(n) => Some(n.clone()),
            ExprKind::Select { operand, field, .. } => Some(format!("{}.{field}", path(operand)?)),
            ExprKind::Call { target: None, function, args } if function == ops::INDEX && args.len() == 2 => {
                Some(format!("{}[..]", path(&args[0])?))
            }
            _ => None,
        }
    }
    match path(e) {
        Some(p) => format!("'{p}'"),
        None => "this list or map".into(),
    }
}

/// Unbounded lists or maps inside a value of type `t` (its elements, map values and struct
/// fields), given the value's constraints.
fn inside(c: &CheckedExpr, t: &CelType, cons: Option<&Constraints>, what: &str, seen: &mut Vec<String>) -> Option<String> {
    let items = cons.and_then(|c| c.items.as_deref());
    let check = |t: &CelType, cons: Option<&Constraints>, what: String, seen: &mut Vec<String>| -> Option<String> {
        if is_collection(t) {
            if let Some(why) = missing(cons) {
                return Some(format!("{what}: {why}; declare a max_length of at most {MAX_ELEMENTS}"));
            }
        }
        inside(c, t, cons, &what, seen)
    };
    match strip(t) {
        CelType::List(a) | CelType::Map(_, a) => check(a, items, format!("the items of {what}"), seen),
        CelType::Struct(n) if !seen.contains(n) => {
            seen.push(n.clone());
            let decl = c.schema.structs.get(n)?;
            let r = decl.fields.iter().find_map(|f| check(&f.ty, Some(&f.constraints), format!("field '{n}.{}'", f.name), seen));
            seen.pop();
            r
        }
        _ => None,
    }
}
