//! Translate checked CEL expressions into Z3 terms.

use crate::sym::*;
use crate::zutil;
use celspresso_check::{CelType, CheckedExpr, Constraints, Reference, Schema};
use celspresso_eval::time::{MAX_DUR, MAX_TS, MIN_TS, NANOS};
use celspresso_eval::{date, Key, StructValue, Value};
use celspresso_syntax::ast::{ops, Expr, ExprKind, Literal};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::sync::Arc;
use z3::ast::{Ast, Bool, Dynamic, Float, Int, Int as ZInt, RoundingMode, String as ZStr};
use z3::{FuncDecl, Model, Sort};

pub const MAX_SLOTS: usize = 64;
const I64_MIN: i64 = i64::MIN;
const I64_MAX: i64 = i64::MAX;

pub struct Encoder {
    schema: Arc<Schema>,
    pub unroll: usize,
    pub schema_constraints: bool,
    /// Root variables (built lazily on first reference).
    pub vars: BTreeMap<String, Sym>,
    /// Facts about inputs: type ranges and schema constraints.
    pub assumptions: Vec<Bool>,
    /// Soft preferences for readable witnesses.
    pub soft: Vec<Bool>,
    /// Some consumed list may have been truncated at the unroll bound.
    pub bounded: bool,
    /// Places where the encoding over-approximates (named in UNKNOWN reasons).
    pub approximations: BTreeSet<String>,
    locals: Vec<(String, SV)>,
    funcs: HashMap<String, (FuncDecl, FuncDecl)>,
    /// CEL function name -> (overload id, arity) of uninterpreted functions in use.
    func_overloads: HashMap<String, Vec<(String, usize)>>,
    /// Host functions the encoding treats as opaque (named in UNKNOWN reasons).
    opaque_host: BTreeSet<String>,
    /// Standard-library functions the verifier doesn't model yet.
    unmodeled_builtins: BTreeSet<String>,
    /// Whether the answer depends on `dyn` values (from `Any`), which are opaque.
    reads_dyn: bool,
    fresh: u32,
    /// The first date input, which later dates prefer to stay near (readable witnesses).
    first_date: Option<Int>,
    /// (haystack, needle, result, is_last) of every indexOf(s, t) / lastIndexOf(s, t), to relate them.
    index_terms: Vec<(ZStr, ZStr, ZInt, bool)>,
}

/// Days since 1970-01-01 today (UTC). Only steers *preferences*, never verdicts.
fn today_days() -> i64 {
    std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map(|d| (d.as_secs() / 86_400) as i64).unwrap_or(0)
}

fn int_range(x: &Int, lo: i64, hi: i64) -> Bool {
    and(&[&x.ge(Int::from_i64(lo)), &x.le(Int::from_i64(hi))])
}
fn big(n: i128) -> Int {
    n.to_string().parse().expect("integer literal")
}
fn ts_range(x: &Int) -> Bool {
    and(&[&x.ge(big(MIN_TS)), &x.le(big(MAX_TS))])
}
fn dur_range(x: &Int) -> Bool {
    and(&[&x.ge(big(-MAX_DUR)), &x.le(big(MAX_DUR))])
}
fn uint_range(x: &Int) -> Bool {
    and(&[&x.ge(Int::from_i64(0)), &x.le(Int::from_u64(u64::MAX))])
}

impl Encoder {
    pub fn new(schema: Arc<Schema>, unroll: usize, schema_constraints: bool) -> Encoder {
        Encoder {
            schema,
            unroll,
            schema_constraints,
            vars: BTreeMap::new(),
            assumptions: Vec::new(),
            soft: Vec::new(),
            bounded: false,
            approximations: BTreeSet::new(),
            locals: Vec::new(),
            funcs: HashMap::new(),
            func_overloads: HashMap::new(),
            opaque_host: BTreeSet::new(),
            unmodeled_builtins: BTreeSet::new(),
            reads_dyn: false,
            fresh: 0,
            first_date: None,
            index_terms: Vec::new(),
        }
    }

    fn fresh_name(&mut self, prefix: &str) -> String {
        self.fresh += 1;
        format!("{prefix}!{}", self.fresh)
    }

    // ---------------------------------------------------------------- inputs

    fn var(&mut self, name: &str) -> Option<Sym> {
        if let Some(s) = self.vars.get(name) {
            return Some(s.clone());
        }
        let decl = self.schema.vars.get(name)?.clone();
        let s = self.mk_input(&decl.ty, name, Some(&decl.constraints), 0);
        self.vars.insert(name.to_string(), s.clone());
        Some(s)
    }

    /// Wrap assumptions added since `from` under a guard.
    fn guard_since(&mut self, from: usize, guard: &Bool) {
        for a in &mut self.assumptions[from..] {
            *a = guard.implies(&*a);
        }
    }

    fn mk_input(&mut self, ty: &CelType, path: &str, cons: Option<&Constraints>, depth: usize) -> Sym {
        let cons = if self.schema_constraints { cons } else { None };
        match ty {
            CelType::Bool => Sym::Bool(Bool::new_const(path)),
            CelType::Int | CelType::Uint => {
                let x = Int::new_const(path);
                self.assumptions.push(if *ty == CelType::Int { int_range(&x, I64_MIN, I64_MAX) } else { uint_range(&x) });
                if let Some(c) = cons {
                    self.numeric_constraints(&x, c);
                }
                self.soft.push(int_range(&x, -100, 100));
                if *ty == CelType::Int {
                    Sym::Int(x)
                } else {
                    Sym::Uint(x)
                }
            }
            CelType::Date => {
                let x = Int::new_const(path);
                let lo = date::days_from_civil(1, 1, 1);
                let hi = date::days_from_civil(9999, 12, 31);
                self.assumptions.push(int_range(&x, lo, hi));
                self.soft.push(int_range(&x, date::days_from_civil(1950, 1, 1), date::days_from_civil(2030, 12, 31)));
                // dates near today, and near each other, read like real records (not 1970-01-01)
                let today = today_days();
                self.soft.push(int_range(&x, today - 365, today + 365));
                match &self.first_date {
                    Some(d) => {
                        let gap = &x - d;
                        self.soft.push(int_range(&gap, -365, 365));
                    }
                    None => self.first_date = Some(x.clone()),
                }
                Sym::Date(x)
            }
            CelType::Double => {
                let x = Float::new_const_double(path);
                if let Some(c) = cons {
                    let lit = |v: f64| Float::from_f64(v);
                    if let Some(v) = c.ge {
                        self.assumptions.push(x.ge(lit(v)));
                    }
                    if let Some(v) = c.gt {
                        self.assumptions.push(x.gt(lit(v)));
                    }
                    if let Some(v) = c.le {
                        self.assumptions.push(x.le(lit(v)));
                    }
                    if let Some(v) = c.lt {
                        self.assumptions.push(x.lt(lit(v)));
                    }
                }
                // readable: small whole numbers, then finite ones
                self.soft.push(x.is_nan().not());
                self.soft.push(x.is_infinite().not());
                let whole = x.round_to_integral_with_rounding_mode(&RoundingMode::round_towards_zero());
                self.soft.push(whole.eq_fpa(&x));
                self.soft.push(and(&[&x.ge(Float::from_f64(-100.0)), &x.le(Float::from_f64(100.0))]));
                Sym::Double(x)
            }
            CelType::Timestamp => {
                let x = Int::new_const(path);
                self.assumptions.push(ts_range(&x));
                // readable: whole seconds, near today, near the other dates and times
                let n = big(NANOS);
                self.soft.push(x.modulo(&n).eq(Int::from_i64(0)));
                self.soft.push(x.modulo(big(60 * NANOS)).eq(Int::from_i64(0)));
                let day = x.div(big(86_400 * NANOS));
                let today = today_days();
                self.soft.push(int_range(&day, today - 365, today + 365));
                match &self.first_date {
                    Some(d) => self.soft.push(int_range(&(&day - d), -365, 365)),
                    None => self.first_date = Some(day),
                }
                Sym::Timestamp(x)
            }
            CelType::Duration => {
                let x = Int::new_const(path);
                self.assumptions.push(dur_range(&x));
                self.soft.push(x.modulo(big(NANOS)).eq(Int::from_i64(0)));
                self.soft.push(and(&[&x.ge(big(-86_400 * NANOS)), &x.le(big(86_400 * NANOS))]));
                Sym::Duration(x)
            }
            CelType::String => {
                let s = ZStr::new_const(path);
                // an enumerated or patterned string already has a prescribed shape;
                // "readable" preferences there are useless and slow the string solver
                let shaped = cons.is_some_and(|c| c.one_of.is_some() || c.pattern.is_some());
                if let Some(c) = cons {
                    let len = s.length();
                    if let Some(m) = c.min_length {
                        self.assumptions.push(len.ge(Int::from_u64(m)));
                    }
                    if let Some(m) = c.max_length {
                        self.assumptions.push(len.le(Int::from_u64(m)));
                    }
                    if let Some(opts) = &c.one_of {
                        let eqs: Vec<Bool> = opts
                            .iter()
                            .filter_map(|l| match l {
                                Literal::String(v) => Some(s.eq(zutil::str_lit(v))),
                                _ => None,
                            })
                            .collect();
                        self.assumptions.push(or(&eqs.iter().collect::<Vec<_>>()));
                    }
                    if let Some(p) = &c.pattern {
                        match zutil::translate_search(p) {
                            Ok(re) => self.assumptions.push(s.regex_matches(&re)),
                            Err(_) => {
                                self.approximations.insert(format!("pattern constraint on '{path}' is not encoded"));
                            }
                        }
                    }
                }
                if !shaped {
                    self.soft.push(s.length().le(Int::from_i64(8)));
                    if let Ok(re) = zutil::translate_search("^[a-z0-9]*$") {
                        self.soft.push(s.regex_matches(&re));
                    }
                }
                Sym::Str(s)
            }
            CelType::Null => Sym::Null,
            CelType::Nullable(inner) => {
                let is_null = Bool::new_const(format!("{path}?null"));
                let from = self.assumptions.len();
                let v = self.mk_input(inner, path, cons, depth);
                self.guard_since(from, &is_null.not());
                Sym::Nullable { is_null, inner: Box::new(v) }
            }
            CelType::List(elem) => {
                let max_len = cons.and_then(|c| c.max_length);
                let (n, trunc) = match max_len {
                    // a declared max_length raises the unroll bound automatically, so the encoding is exact
                    Some(m) if (m as usize) <= self.unroll.max(MAX_SLOTS) => (m as usize, false),
                    _ => (self.unroll, true),
                };
                let len = Int::new_const(format!("{path}#len"));
                self.assumptions.push(int_range(&len, 0, n as i64));
                if let Some(m) = cons.and_then(|c| c.min_length) {
                    self.assumptions.push(len.ge(Int::from_u64(m)));
                }
                self.soft.push(len.le(Int::from_i64(2)));
                let item_cons = cons.and_then(|c| c.items.as_deref());
                let mut slots = Vec::with_capacity(n);
                for i in 0..n {
                    let live = len.gt(Int::from_i64(i as i64));
                    let from = self.assumptions.len();
                    let v = self.mk_input(elem, &format!("{path}[{i}]"), item_cons, depth + 1);
                    self.guard_since(from, &live);
                    slots.push((live, v));
                }
                Sym::List { slots, elem: (**elem).clone(), trunc }
            }
            CelType::Map(kt, vt) if depth < 8 && is_key_type(kt) => {
                let max_len = cons.and_then(|c| c.max_length);
                let (n, trunc) = match max_len {
                    Some(m) if (m as usize) <= self.unroll.max(MAX_SLOTS) => (m as usize, false),
                    _ => (self.unroll, true),
                };
                let len = Int::new_const(format!("{path}#len"));
                self.assumptions.push(int_range(&len, 0, n as i64));
                if let Some(m) = cons.and_then(|c| c.min_length) {
                    self.assumptions.push(len.ge(Int::from_u64(m)));
                }
                self.soft.push(len.le(Int::from_i64(2)));
                let val_cons = cons.and_then(|c| c.items.as_deref());
                let mut slots = Vec::with_capacity(n);
                for i in 0..n {
                    let live = len.gt(Int::from_i64(i as i64));
                    let from = self.assumptions.len();
                    let k = self.mk_input(kt, &format!("{path}{{key{i}}}"), None, depth + 1);
                    let v = self.mk_input(vt, &format!("{path}{{val{i}}}"), val_cons, depth + 1);
                    self.guard_since(from, &live);
                    slots.push((live, k, v));
                }
                if let Some(d) = distinct_keys(&slots) {
                    self.assumptions.push(d);
                }
                Sym::Map { slots, key: (**kt).clone(), val: (**vt).clone(), trunc }
            }
            CelType::Struct(name) if depth < 8 => {
                let Some(sd) = self.schema.structs.get(name).cloned() else {
                    return self.opaque(ty);
                };
                let mut fields = BTreeMap::new();
                for f in &sd.fields {
                    let v = self.mk_input(&f.ty, &format!("{path}.{}", f.name), Some(&f.constraints), depth + 1);
                    fields.insert(f.name.clone(), v);
                }
                Sym::Struct { name: name.clone(), fields }
            }
            _ => self.opaque(ty),
        }
    }

    fn numeric_constraints(&mut self, x: &Int, c: &Constraints) {
        let bound = |f: f64| Int::from_i64(f.clamp(-1.0e19, 1.0e19) as i64);
        if let Some(v) = c.ge {
            self.assumptions.push(x.ge(bound(v.ceil())));
        }
        if let Some(v) = c.gt {
            self.assumptions.push(x.ge(bound(v.floor() + 1.0)));
        }
        if let Some(v) = c.le {
            self.assumptions.push(x.le(bound(v.floor())));
        }
        if let Some(v) = c.lt {
            self.assumptions.push(x.le(bound(v.ceil() - 1.0)));
        }
        if let Some(opts) = &c.one_of {
            let eqs: Vec<Bool> = opts
                .iter()
                .filter_map(|l| match l {
                    Literal::Int(i) => Some(x.eq(Int::from_i64(*i))),
                    Literal::Uint(u) => Some(x.eq(Int::from_u64(*u))),
                    _ => None,
                })
                .collect();
            self.assumptions.push(or(&eqs.iter().collect::<Vec<_>>()));
        }
    }

    fn opaque(&mut self, ty: &CelType) -> Sym {
        let n = self.fresh_name("opaque");
        Sym::Opaque { ty: ty.clone(), id: Int::new_const(n) }
    }

    /// An unconstrained value of the given type (used for over-approximation).
    fn fresh(&mut self, ty: &CelType) -> Sym {
        match ty {
            CelType::Bool => Sym::Bool(Bool::new_const(self.fresh_name("b"))),
            CelType::Int => {
                let x = Int::new_const(self.fresh_name("i"));
                self.assumptions.push(int_range(&x, I64_MIN, I64_MAX));
                Sym::Int(x)
            }
            CelType::Uint => {
                let x = Int::new_const(self.fresh_name("u"));
                self.assumptions.push(uint_range(&x));
                Sym::Uint(x)
            }
            CelType::Date => Sym::Date(Int::new_const(self.fresh_name("d"))),
            CelType::Double => Sym::Double(Float::new_const_double(self.fresh_name("f"))),
            CelType::Timestamp => {
                let x = Int::new_const(self.fresh_name("t"));
                self.assumptions.push(ts_range(&x));
                Sym::Timestamp(x)
            }
            CelType::Duration => {
                let x = Int::new_const(self.fresh_name("dur"));
                self.assumptions.push(dur_range(&x));
                Sym::Duration(x)
            }
            CelType::String => Sym::Str(ZStr::new_const(self.fresh_name("s"))),
            CelType::Null => Sym::Null,
            CelType::Nullable(t) => {
                let is_null = Bool::new_const(self.fresh_name("n"));
                Sym::Nullable { is_null, inner: Box::new(self.fresh(t)) }
            }
            CelType::List(t) => {
                // unknown lists: bounded, so marks results as bounded when consumed
                let n = self.unroll;
                let len = Int::new_const(self.fresh_name("len"));
                self.assumptions.push(int_range(&len, 0, n as i64));
                let slots = (0..n).map(|i| (len.gt(Int::from_i64(i as i64)), self.fresh(t))).collect();
                Sym::List { slots, elem: (**t).clone(), trunc: true }
            }
            CelType::Optional(t) => {
                let has = Bool::new_const(self.fresh_name("has"));
                Sym::Optional { has, val: Box::new(self.fresh(t)) }
            }
            CelType::Map(kt, vt) if is_key_type(kt) => {
                let n = self.unroll;
                let len = Int::new_const(self.fresh_name("len"));
                self.assumptions.push(int_range(&len, 0, n as i64));
                let slots: Vec<(Bool, Sym, Sym)> =
                    (0..n).map(|i| (len.gt(Int::from_i64(i as i64)), self.fresh(kt), self.fresh(vt))).collect();
                if let Some(d) = distinct_keys(&slots) {
                    self.assumptions.push(d);
                }
                Sym::Map { slots, key: (**kt).clone(), val: (**vt).clone(), trunc: true }
            }
            CelType::Struct(name) => {
                let Some(sd) = self.schema.structs.get(name).cloned() else {
                    return self.opaque(ty);
                };
                let mut fields = BTreeMap::new();
                for f in &sd.fields {
                    let v = self.fresh(&f.ty);
                    fields.insert(f.name.clone(), v);
                }
                Sym::Struct { name: name.clone(), fields }
            }
            _ => self.opaque(ty),
        }
    }

    fn approx(&mut self, c: &CheckedExpr, e: &Expr, why: impl Into<String>) -> SV {
        self.approximations.insert(why.into());
        let ty = c.type_of(e.id).clone();
        let v = self.fresh(&ty);
        SV { v, err: Bool::new_const(self.fresh_name("err")) }
    }

    // ------------------------------------------------------------ expressions

    pub fn encode(&mut self, c: &CheckedExpr) -> SV {
        self.enc(c, &c.expr)
    }

    fn enc(&mut self, c: &CheckedExpr, e: &Expr) -> SV {
        match &e.kind {
            ExprKind::Literal(l) => match l {
                Literal::Null => SV::ok(Sym::Null),
                Literal::Bool(b) => SV::ok(Sym::Bool(Bool::from_bool(*b))),
                Literal::Int(i) => SV::ok(Sym::Int(Int::from_i64(*i))),
                Literal::Uint(u) => SV::ok(Sym::Uint(Int::from_u64(*u))),
                Literal::String(s) => SV::ok(Sym::Str(zutil::str_lit(s))),
                Literal::Double(d) => SV::ok(Sym::Double(Float::from_f64(*d))),
                Literal::Bytes(_) => self.approx(c, e, "bytes are not yet modeled"),
            },
            ExprKind::Ident(name) => {
                if let Some((_, v)) = self.locals.iter().rev().find(|(n, _)| n == name) {
                    return v.clone();
                }
                match c.refs.get(&e.id) {
                    Some(Reference::Var(_)) | None => match self.var(name) {
                        Some(v) => SV::ok(v),
                        None => self.approx(c, e, format!("unknown variable '{name}'")),
                    },
                    Some(_) => self.approx(c, e, format!("unresolved identifier '{name}'")),
                }
            }
            ExprKind::Select { operand, field, test_only } => {
                let o = self.enc(c, operand);
                let (is_null, inner) = o.v.unwrap_nullable();
                match inner {
                    Sym::Struct { fields, .. } => {
                        let err = or(&[&o.err, &is_null]);
                        if *test_only {
                            // a declared field is set unless it holds null
                            return SV { v: Sym::Bool(Self::field_set(fields.get(field))), err };
                        }
                        match fields.get(field) {
                            Some(v) => SV { v: v.clone(), err },
                            None => self.approx(c, e, format!("unknown field '{field}'")),
                        }
                    }
                    Sym::Null => SV { v: self.fresh(c.type_of(e.id)), err: tt() },
                    Sym::Optional { has, val } if *test_only => {
                        // has() on an empty optional is false, otherwise it tests the value
                        let (has, val) = (has.clone(), (**val).clone());
                        match self.select_test(&val, field) {
                            Some(t) => SV { v: Sym::Bool(and(&[&has, &t])), err: o.err.clone() },
                            None => self.approx(c, e, "has() on this optional value is not modeled"),
                        }
                    }
                    Sym::Optional { .. } => {
                        let ty = c.type_of(e.id).clone();
                        match self.opt_select(&o.v, field, &ty) {
                            Some((v, err)) => SV { v, err: or(&[&o.err, &err]) },
                            None => self.approx(c, e, "selection on this optional value is not modeled"),
                        }
                    }
                    Sym::Map { slots, trunc, .. } => {
                        if *trunc {
                            self.bounded = true;
                        }
                        let key = Sym::Str(zutil::str_lit(field));
                        let Some((found, val)) = map_get(slots, &key) else {
                            return self.approx(c, e, "field selection on this map is not modeled");
                        };
                        let err = or(&[&o.err, &is_null]);
                        if *test_only {
                            return SV { v: Sym::Bool(found), err };
                        }
                        let v = match val {
                            Some(v) => v,
                            None => self.fresh(c.type_of(e.id)),
                        };
                        SV { v, err: or(&[&err, &found.not()]) }
                    }
                    _ => self.approx(c, e, "field selection on dyn values is not yet modeled"),
                }
            }
            ExprKind::List(items) => {
                let mut slots = Vec::new();
                let mut errs = Vec::new();
                for it in items {
                    let Some((live, v)) = self.entry_value(c, it) else {
                        return self.approx(c, e, "optional list entries of this shape are not modeled");
                    };
                    errs.push(v.err);
                    slots.push((live, v.v));
                }
                let elem = match c.type_of(e.id) {
                    CelType::List(t) => (**t).clone(),
                    _ => CelType::Dyn,
                };
                SV { v: Sym::List { slots, elem, trunc: false }, err: or(&errs.iter().collect::<Vec<_>>()) }
            }
            ExprKind::Map(entries) => {
                let (kt, vt) = match c.type_of(e.id) {
                    CelType::Map(k, v) => ((**k).clone(), (**v).clone()),
                    _ => (CelType::Dyn, CelType::Dyn),
                };
                if !is_key_type(&kt) {
                    return self.approx(c, e, "map literals with dyn keys are not yet modeled");
                }
                let mut slots = Vec::new();
                let mut errs = Vec::new();
                for (k, v) in entries {
                    let (ksv, live, vsv) = match self.entry_value(c, v) {
                        Some((live, vsv)) => (self.enc(c, k), live, vsv),
                        None => return self.approx(c, e, "optional map entries of this shape are not modeled"),
                    };
                    errs.push(ksv.err);
                    errs.push(vsv.err);
                    slots.push((live, ksv.v, vsv.v));
                }
                // a repeated key is a runtime error
                match distinct_keys(&slots) {
                    Some(d) => errs.push(d.not()),
                    None => return self.approx(c, e, "map literal keys the verifier does not model"),
                }
                SV { v: Sym::Map { slots, key: kt, val: vt, trunc: false }, err: or(&errs.iter().collect::<Vec<_>>()) }
            }
            ExprKind::Struct { type_name, fields } => {
                let mut out = BTreeMap::new();
                let mut errs = Vec::new();
                for (name, v) in fields {
                    let sv = self.enc(c, v);
                    errs.push(sv.err);
                    out.insert(name.clone(), sv.v);
                }
                if let Some(sd) = self.schema.structs.get(type_name).cloned() {
                    for f in &sd.fields {
                        if !out.contains_key(&f.name) {
                            let d = default_sym(&f.ty).unwrap_or_else(|| self.fresh(&f.ty));
                            out.insert(f.name.clone(), d);
                        }
                    }
                }
                SV { v: Sym::Struct { name: type_name.clone(), fields: out }, err: or(&errs.iter().collect::<Vec<_>>()) }
            }
            ExprKind::Comprehension(comp) => {
                let range = self.enc(c, &comp.iter_range);
                let two = comp.iter_var2.is_some();
                // (live, first variable, second variable) per iteration
                let (items, trunc): (Vec<(Bool, Sym, Option<Sym>)>, bool) = match range.v.clone() {
                    Sym::List { slots, trunc, .. } => {
                        let one = Int::from_i64(1);
                        let mut index = Int::from_i64(0);
                        let mut items = Vec::with_capacity(slots.len());
                        for (live, elem) in slots {
                            let item = if two { (live.clone(), Sym::Int(index.clone()), Some(elem)) } else { (live.clone(), elem, None) };
                            index = &index + live.ite(&one, &Int::from_i64(0));
                            items.push(item);
                        }
                        (items, trunc)
                    }
                    Sym::Map { slots, trunc, .. } => {
                        (slots.into_iter().map(|(l, k, v)| (l, k, if two { Some(v) } else { None })).collect(), trunc)
                    }
                    _ => return self.approx(c, e, "comprehension over this range is not yet modeled"),
                };
                if trunc {
                    self.bounded = true;
                }
                let init = self.enc(c, &comp.accu_init);
                self.locals.push((comp.accu_var.clone(), init));
                let accu_idx = self.locals.len() - 1;
                let mut stopped = ff();
                for (live, first, second) in items {
                    let accu = self.locals[accu_idx].1.clone();
                    let cond = self.enc(c, &comp.loop_condition);
                    let cv = cond.v.as_bool().cloned().unwrap_or_else(tt);
                    let active = and(&[&live, &stopped.not()]);
                    let pushed = self.locals.len();
                    self.locals.push((comp.iter_var.clone(), SV::ok(first)));
                    if let (Some(name), Some(v)) = (&comp.iter_var2, second) {
                        self.locals.push((name.clone(), SV::ok(v)));
                    }
                    let step = self.enc(c, &comp.loop_step);
                    self.locals.truncate(pushed);
                    let proceed = and(&[&active, &cv, &cond.err.not()]);
                    let Some(mut next) = ite_sv(&proceed, &step, &accu) else {
                        self.locals.truncate(accu_idx);
                        return self.approx(c, e, "comprehension accumulator shape is not supported");
                    };
                    next.err = or(&[&next.err, &and(&[&active, &cond.err])]);
                    stopped = or(&[&stopped, &and(&[&active, &or(&[&cond.err, &cv.not()])])]);
                    self.locals[accu_idx].1 = next;
                }
                let mut res = self.enc(c, &comp.result);
                self.locals.truncate(accu_idx);
                res.err = or(&[&res.err, &range.err]);
                res
            }
            ExprKind::Call { function, args, .. } if function == ops::OPT_SELECT && args.len() == 2 => {
                let o = self.enc(c, &args[0]);
                let ExprKind::Literal(Literal::String(field)) = &args[1].kind else {
                    return self.approx(c, e, "optional selection with a computed field name");
                };
                let ty = c.type_of(e.id).clone();
                match self.opt_select(&o.v, field, &ty) {
                    Some((v, err)) => SV { v, err: or(&[&o.err, &err]) },
                    None => self.approx(c, e, "optional selection on this value is not modeled"),
                }
            }
            ExprKind::Call { function, .. } if function == ops::OPT_ENTRY => {
                self.approx(c, e, "an optional entry outside a list or map literal")
            }
            ExprKind::Call { function, .. } if matches!(c.type_of(e.id), CelType::Opaque(_)) => {
                self.approx(c, e, format!("'{function}' returns an extension type the verifier does not model"))
            }
            ExprKind::Call { target, function, args } => self.call(c, e, target.as_deref(), function, args),
        }
    }

    fn call(&mut self, c: &CheckedExpr, e: &Expr, target: Option<&Expr>, function: &str, args: &[Expr]) -> SV {
        match function {
            ops::LOGICAL_AND | ops::LOGICAL_OR => {
                let l = self.enc(c, &args[0]);
                let r = self.enc(c, &args[1]);
                let (Some(lv), Some(rv)) = (l.v.as_bool(), r.v.as_bool()) else {
                    return self.approx(c, e, "non-bool logical operand");
                };
                return if function == ops::LOGICAL_AND {
                    let lf = and(&[&l.err.not(), &lv.not()]);
                    let rf = and(&[&r.err.not(), &rv.not()]);
                    let decided = or(&[&lf, &rf]);
                    SV { v: Sym::Bool(decided.not()), err: and(&[&decided.not(), &or(&[&l.err, &r.err])]) }
                } else {
                    let lt = and(&[&l.err.not(), lv]);
                    let rt = and(&[&r.err.not(), rv]);
                    let decided = or(&[&lt, &rt]);
                    SV { v: Sym::Bool(decided.clone()), err: and(&[&decided.not(), &or(&[&l.err, &r.err])]) }
                };
            }
            ops::CONDITIONAL => {
                let cond = self.enc(c, &args[0]);
                let a = self.enc(c, &args[1]);
                let b = self.enc(c, &args[2]);
                let Some(cv) = cond.v.as_bool() else {
                    return self.approx(c, e, "non-bool condition");
                };
                return match ite_sv(cv, &a, &b) {
                    Some(mut r) => {
                        r.err = or(&[&cond.err, &r.err]);
                        r
                    }
                    None => self.approx(c, e, "conditional branches have incompatible shapes"),
                };
            }
            ops::NOT_STRICTLY_FALSE => {
                let a = self.enc(c, &args[0]);
                let v = a.v.as_bool().cloned().unwrap_or_else(tt);
                return SV::ok(Sym::Bool(or(&[&a.err, &v])));
            }
            _ => {}
        }
        let mut vals = Vec::with_capacity(args.len() + 1);
        if let Some(t) = target {
            vals.push(self.enc(c, t));
        }
        for a in args {
            vals.push(self.enc(c, a));
        }
        // Equality and `in` compare nullable values as-is (null == null). Every other
        // builtin has no overload for null, so evaluating it on a null operand is an error:
        // unwrap to the inner value and fold `is_null` into the error flag.
        let keeps_null =
            matches!(function, ops::EQUALS | ops::NOT_EQUALS | ops::IN | "dyn" | "optional.of" | "optional.ofNonZeroValue" | "orValue");
        if !keeps_null {
            for sv in &mut vals {
                if let Sym::Nullable { is_null, inner } = &sv.v {
                    let (is_null, inner) = (is_null.clone(), (**inner).clone());
                    sv.err = or(&[&sv.err, &is_null]);
                    sv.v = inner;
                }
            }
        }
        let err_in = or(&vals.iter().map(|v| &v.err).collect::<Vec<_>>());
        let syms: Vec<Sym> = vals.into_iter().map(|v| v.v).collect();
        match self.builtin(c, e, function, &syms) {
            Some(Ok((v, err))) => SV { v, err: or(&[&err_in, &err]) },
            Some(Err(why)) => {
                let why = self.unmodeled(function, &syms).unwrap_or(why);
                let mut r = self.approx(c, e, why);
                r.err = or(&[&r.err, &err_in]);
                r
            }
            None => {
                let mut r = self.uninterpreted(c, e, function, &syms);
                r.err = or(&[&r.err, &err_in]);
                r
            }
        }
    }

    /// `has()` of a struct field: declared fields are set unless they hold null.
    fn field_set(f: Option<&Sym>) -> Bool {
        match f {
            None | Some(Sym::Null) => ff(),
            Some(Sym::Nullable { is_null, .. }) => is_null.not(),
            Some(_) => tt(),
        }
    }

    /// A literal element or map value: (live, value). `?e` entries are live iff `e` has a value.
    fn entry_value(&mut self, c: &CheckedExpr, v: &Expr) -> Option<(Bool, SV)> {
        match &v.kind {
            ExprKind::Call { target: None, function, args } if function == ops::OPT_ENTRY && args.len() == 1 => {
                let o = self.enc(c, &args[0]);
                match o.v {
                    Sym::Optional { has, val } => Some((has, SV { v: *val, err: o.err })),
                    _ => None,
                }
            }
            _ => Some((tt(), self.enc(c, v))),
        }
    }

    /// `v.?field`: (optional result, error).
    fn opt_select(&mut self, v: &Sym, field: &str, ty: &CelType) -> Option<(Sym, Bool)> {
        let inner_ty = match ty {
            CelType::Optional(t) => (**t).clone(),
            t => t.clone(),
        };
        Some(match v {
            Sym::Optional { has, val } => {
                let (r, err) = self.opt_select(val, field, ty)?;
                let Sym::Optional { has: h2, val: v2 } = r else {
                    return None;
                };
                (Sym::Optional { has: and(&[has, &h2]), val: v2 }, and(&[has, &err]))
            }
            Sym::Struct { fields, .. } => match fields.get(field) {
                Some(f) => (Sym::Optional { has: tt(), val: Box::new(f.clone()) }, ff()),
                None => (Sym::Optional { has: ff(), val: Box::new(self.fresh(&inner_ty)) }, ff()),
            },
            Sym::Map { slots, trunc, .. } => {
                if *trunc {
                    self.bounded = true;
                }
                let (found, val) = map_get(slots, &Sym::Str(zutil::str_lit(field)))?;
                let val = val.unwrap_or_else(|| self.fresh(&inner_ty));
                (Sym::Optional { has: found, val: Box::new(val) }, ff())
            }
            Sym::Nullable { is_null, inner } => {
                let (r, err) = self.opt_select(inner, field, ty)?;
                (r, or(&[is_null, &err]))
            }
            Sym::Null => (Sym::Optional { has: ff(), val: Box::new(self.fresh(&inner_ty)) }, tt()),
            _ => return None,
        })
    }

    /// `has(v.field)` on a non-optional value.
    fn select_test(&mut self, v: &Sym, field: &str) -> Option<Bool> {
        match v {
            Sym::Struct { fields, .. } => Some(Self::field_set(fields.get(field))),
            Sym::Map { slots, trunc, .. } => {
                if *trunc {
                    self.bounded = true;
                }
                Some(map_get(slots, &Sym::Str(zutil::str_lit(field)))?.0)
            }
            Sym::Optional { has, val } => Some(and(&[has, &self.select_test(val, field)?])),
            _ => None,
        }
    }

    /// `x[?i]` (and `opt[i]`): (optional result, error).
    fn opt_index(&mut self, x: &Sym, i: &Sym, ty: &CelType) -> Option<(Sym, Bool)> {
        let inner_ty = match ty {
            CelType::Optional(t) => (**t).clone(),
            t => t.clone(),
        };
        Some(match (x, i) {
            (Sym::Optional { has, val }, _) => {
                let (r, err) = self.opt_index(val, i, ty)?;
                let Sym::Optional { has: h2, val: v2 } = r else {
                    return None;
                };
                (Sym::Optional { has: and(&[has, &h2]), val: v2 }, and(&[has, &err]))
            }
            (Sym::List { slots, .. }, Sym::Int(k) | Sym::Uint(k)) => {
                let len = Sym::list_len(slots);
                let inside = and(&[&k.ge(Int::from_i64(0)), &k.lt(&len)]);
                let val = match nth_live(slots, k) {
                    Some((_, v)) => v,
                    None => self.fresh(&inner_ty),
                };
                (Sym::Optional { has: inside, val: Box::new(val) }, ff())
            }
            (Sym::Map { slots, .. }, k) => {
                let (found, val) = map_get(slots, k)?;
                let val = val.unwrap_or_else(|| self.fresh(&inner_ty));
                (Sym::Optional { has: found, val: Box::new(val) }, ff())
            }
            _ => return None,
        })
    }

    fn mark_lists(&mut self, args: &[Sym]) {
        for a in args {
            if let Sym::Map { trunc: true, .. } = a {
                self.bounded = true;
            }
        }
        for a in args {
            if let Sym::List { trunc: true, .. } = a {
                self.bounded = true;
            }
        }
    }

    /// Returns None when the function is not a builtin; Some(Err) when it is unsupported.
    fn builtin(&mut self, c: &CheckedExpr, e: &Expr, function: &str, v: &[Sym]) -> Option<Result<(Sym, Bool), String>> {
        use Sym::*;
        let ok = |s: Sym| Some(Ok((s, ff())));
        let int_res = |x: ZInt| {
            let over = int_range(&x, I64_MIN, I64_MAX).not();
            Some(Ok((Int(x), over)))
        };
        let uint_res = |x: ZInt| {
            let over = uint_range(&x).not();
            Some(Ok((Uint(x), over)))
        };
        self.mark_lists(v);
        match (function, v) {
            (ops::LOGICAL_NOT, [Bool(b)]) => ok(Bool(b.not())),
            (ops::NEGATE, [Int(x)]) => int_res(x.unary_minus()),
            (ops::NEGATE, [Double(x)]) => ok(Double(x.unary_neg())),
            (ops::ADD | ops::SUBTRACT | ops::MULTIPLY | ops::DIVIDE, [Double(a), Double(b)]) => {
                let rm = RoundingMode::round_nearest_ties_to_even();
                ok(Double(match function {
                    ops::ADD => a.add_with_rounding_mode(b, &rm),
                    ops::SUBTRACT => a.sub_with_rounding_mode(b, &rm),
                    ops::MULTIPLY => a.mul_with_rounding_mode(b, &rm),
                    _ => a.div_with_rounding_mode(b, &rm),
                }))
            }
            ("double", [Double(x)]) => ok(Double(x.clone())),
            ("double", [Int(x) | Uint(x)]) => ok(Double(zutil::int_to_double(x))),
            ("double", [Str(s)]) => match zutil::str_value(s) {
                Some(text) => match text.parse::<f64>() {
                    Ok(d) => ok(Double(Float::from_f64(d))),
                    Err(_) => {
                        let ty = c.type_of(e.id).clone();
                        Some(Ok((self.fresh(&ty), tt())))
                    }
                },
                None => Some(Err("double() of a non-constant string".into())),
            },
            ("int", [Double(d)]) => {
                let bad = or(&[&d.is_nan(), &d.le(Float::from_f64(-9.223372036854776e18)), &d.ge(Float::from_f64(9.223372036854776e18))]);
                Some(Ok((Int(zutil::double_trunc(d)), bad)))
            }
            ("uint", [Double(d)]) => {
                let bad = or(&[&d.is_nan(), &d.lt(Float::from_f64(0.0)), &d.ge(Float::from_f64(1.8446744073709552e19))]);
                Some(Ok((Uint(zutil::double_trunc(d)), bad)))
            }
            (ops::ADD, [Int(a), Int(b)]) => int_res(a + b),
            (ops::ADD, [Uint(a), Uint(b)]) => uint_res(a + b),
            (ops::ADD, [Str(a), Str(b)]) => ok(Str(ZStr::concat(&[a.clone(), b.clone()]))),
            (ops::ADD, [List { slots: a, elem, trunc: t1 }, List { slots: b, trunc: t2, .. }]) => {
                let mut slots = a.clone();
                slots.extend(b.iter().cloned());
                ok(List { slots, elem: elem.clone(), trunc: *t1 || *t2 })
            }
            (ops::ADD, [Date(d), Int(n)]) => ok(Date(d + n)),
            (ops::ADD, [Timestamp(t), Duration(d)] | [Duration(d), Timestamp(t)]) => {
                let r = t + d;
                Some(Ok((Timestamp(r.clone()), ts_range(&r).not())))
            }
            (ops::ADD, [Duration(a), Duration(b)]) => {
                let r = a + b;
                Some(Ok((Duration(r.clone()), dur_range(&r).not())))
            }
            (ops::SUBTRACT, [Timestamp(t), Duration(d)]) => {
                let r = t - d;
                Some(Ok((Timestamp(r.clone()), ts_range(&r).not())))
            }
            (ops::SUBTRACT, [Timestamp(a), Timestamp(b)]) | (ops::SUBTRACT, [Duration(a), Duration(b)]) => {
                let r = a - b;
                Some(Ok((Duration(r.clone()), dur_range(&r).not())))
            }
            ("timestamp", [Str(s)]) | ("duration", [Str(s)]) => {
                let Some(text) = zutil::str_value(s) else {
                    return Some(Err(format!("{function}() of a non-constant string")));
                };
                let parsed = if function == "timestamp" {
                    celspresso_eval::time::parse_timestamp(&text).map(|n| Timestamp(big(n)))
                } else {
                    celspresso_eval::time::parse_duration(&text).map(|n| Duration(big(n)))
                };
                match parsed {
                    Some(v) => ok(v),
                    None => {
                        let ty = c.type_of(e.id).clone();
                        Some(Ok((self.fresh(&ty), tt())))
                    }
                }
            }
            ("timestamp", [Int(secs)]) => {
                let r = secs * big(NANOS);
                Some(Ok((Timestamp(r.clone()), ts_range(&r).not())))
            }
            ("timestamp", [Timestamp(t)]) => ok(Timestamp(t.clone())),
            ("duration", [Duration(d)]) => ok(Duration(d.clone())),
            ("int", [Timestamp(t)]) => ok(Int(t.div(big(NANOS)))),
            (f, [Timestamp(t), rest @ ..]) if rest.len() <= 1 && ts_field_fn(f) => {
                let offset = match rest {
                    [] => 0,
                    [Str(z)] => match zutil::str_value(z).as_deref().and_then(fixed_offset) {
                        Some(o) => o,
                        None => return Some(Err(format!("'{f}' with a named or computed time zone"))),
                    },
                    _ => return Some(Err(format!("builtin '{f}' on these operand types is not modeled"))),
                };
                ok(Int(ts_field(t, f, offset)))
            }
            (f @ ("getHours" | "getMinutes" | "getSeconds" | "getMilliseconds"), [Duration(d)]) => {
                let r = match f {
                    "getHours" => trunc_divmod(d, &big(3600 * NANOS)).0,
                    "getMinutes" => trunc_divmod(d, &big(60 * NANOS)).0,
                    "getSeconds" => trunc_divmod(d, &big(NANOS)).0,
                    _ => trunc_divmod(&trunc_divmod(d, &big(NANOS)).1, &big(1_000_000)).0,
                };
                ok(Int(r))
            }
            (ops::SUBTRACT, [Int(a), Int(b)]) => int_res(a - b),
            (ops::SUBTRACT, [Uint(a), Uint(b)]) => uint_res(a - b),
            (ops::SUBTRACT, [Date(a), Date(b)]) => ok(Int(a - b)),
            (ops::SUBTRACT, [Date(d), Int(n)]) => ok(Date(d - n)),
            (ops::MULTIPLY, [Int(a), Int(b)]) => int_res(a * b),
            (ops::MULTIPLY, [Uint(a), Uint(b)]) => uint_res(a * b),
            (ops::DIVIDE | ops::MODULO, [Int(a), Int(b)] | [Uint(a), Uint(b)]) => {
                let (q, r) = trunc_divmod(a, b);
                let zero = b.eq(ZInt::from_i64(0));
                let is_uint = matches!(v[0], Uint(_));
                let res = if function == ops::DIVIDE { q } else { r };
                let over = if is_uint { uint_range(&res).not() } else { int_range(&res, I64_MIN, I64_MAX).not() };
                let s = if is_uint { Uint(res) } else { Int(res) };
                Some(Ok((s, or(&[&zero, &over]))))
            }
            (ops::EQUALS | ops::NOT_EQUALS, [a, b]) => match sym_eq(a, b) {
                Some(eq) => ok(Bool(if function == ops::EQUALS { eq } else { eq.not() })),
                None => Some(Err("equality on values the verifier does not model".into())),
            },
            (ops::LESS | ops::LESS_EQUALS | ops::GREATER | ops::GREATER_EQUALS, [a, b]) => {
                let r = match (a, b) {
                    (Int(x) | Uint(x) | Date(x), Int(y) | Uint(y) | Date(y))
                    | (Timestamp(x), Timestamp(y))
                    | (Duration(x), Duration(y)) => match function {
                        ops::LESS => x.lt(y),
                        ops::LESS_EQUALS => x.le(y),
                        ops::GREATER => x.gt(y),
                        _ => x.ge(y),
                    },
                    (Double(_), _) | (_, Double(_)) => {
                        let as_double = |s: &Sym| match s {
                            Double(d) => Some(d.clone()),
                            Int(i) | Uint(i) => Some(zutil::int_to_double(i)),
                            _ => None,
                        };
                        let (Some(x), Some(y)) = (as_double(a), as_double(b)) else {
                            return Some(Err("ordering on values the verifier does not model".into()));
                        };
                        // every comparison with NaN is false
                        match function {
                            ops::LESS => x.lt(&y),
                            ops::LESS_EQUALS => x.le(&y),
                            ops::GREATER => x.gt(&y),
                            _ => x.ge(&y),
                        }
                    }
                    (Str(x), Str(y)) => match function {
                        ops::LESS => x.str_lt(y),
                        ops::LESS_EQUALS => x.str_le(y),
                        ops::GREATER => y.str_lt(x),
                        _ => y.str_le(x),
                    },
                    (Bool(x), Bool(y)) => {
                        let lt = |p: &z3::ast::Bool, q: &z3::ast::Bool| and(&[&p.not(), q]);
                        match function {
                            ops::LESS => lt(x, y),
                            ops::LESS_EQUALS => lt(y, x).not(),
                            ops::GREATER => lt(y, x),
                            _ => lt(x, y).not(),
                        }
                    }
                    _ => return Some(Err("ordering on values the verifier does not model".into())),
                };
                ok(Bool(r))
            }
            (ops::INDEX, [List { slots, .. }, Int(i) | Uint(i)]) => {
                let len = Sym::list_len(slots);
                let oob = or(&[&i.lt(ZInt::from_i64(0)), &i.ge(&len)]);
                match nth_live(slots, i) {
                    Some((_, elem)) => Some(Ok((elem, oob))),
                    None => {
                        let ty = c.type_of(e.id).clone();
                        Some(Ok((self.fresh(&ty), tt())))
                    }
                }
            }
            ("optional.of", [x]) => ok(Optional { has: tt(), val: Box::new(x.clone()) }),
            ("optional.none", []) => {
                let inner = match c.type_of(e.id) {
                    CelType::Optional(t) => (**t).clone(),
                    _ => CelType::Dyn,
                };
                let val = default_sym(&inner).unwrap_or_else(|| self.fresh(&inner));
                ok(Optional { has: ff(), val: Box::new(val) })
            }
            ("optional.ofNonZeroValue", [x]) => match is_zero(x) {
                Some(z) => ok(Optional { has: z.not(), val: Box::new(x.clone()) }),
                None => Some(Err("optional.ofNonZeroValue on values the verifier does not model".into())),
            },
            ("hasValue", [Optional { has, .. }]) => ok(Bool(has.clone())),
            ("value", [Optional { has, val }]) => Some(Ok(((**val).clone(), has.not()))),
            ("or", [Optional { has: h1, val: v1 }, Optional { has: h2, val: v2 }]) => match ite_sym(h1, v1, v2) {
                Some(v) => ok(Optional { has: or(&[h1, h2]), val: Box::new(v) }),
                None => Some(Err("or() on optionals of different shapes".into())),
            },
            ("orValue", [Optional { has, val }, x]) => match ite_sym(has, val, x) {
                Some(v) => ok(v),
                None => Some(Err("orValue() with a default of a different shape".into())),
            },
            (ops::OPT_INDEX, [x, i]) | (ops::INDEX, [x @ Optional { .. }, i]) => {
                let ty = c.type_of(e.id).clone();
                match self.opt_index(x, i, &ty) {
                    Some(r) => Some(Ok(r)),
                    None => Some(Err("optional indexing on this value is not modeled".into())),
                }
            }
            (ops::INDEX | ops::IN, [Map { .. }, Double(_)] | [Double(_), Map { .. }]) => {
                Some(Err("map keys given as doubles are not yet modeled".into()))
            }
            (ops::INDEX, [Map { slots, .. }, k]) => match map_get(slots, k) {
                Some((found, Some(v))) => Some(Ok((v, found.not()))),
                Some((_, None)) => {
                    let ty = c.type_of(e.id).clone();
                    Some(Ok((self.fresh(&ty), tt())))
                }
                None => Some(Err("map lookup with a key the verifier does not model".into())),
            },
            (ops::IN, [k, Map { slots, .. }]) => match map_get(slots, k) {
                Some((found, _)) => ok(Bool(found)),
                None => Some(Err("map membership with a key the verifier does not model".into())),
            },
            ("size", [Map { slots, .. }]) => ok(Int(Sym::map_len(slots))),
            (ops::MAP_INSERT, [Map { slots, key, val, trunc }, k, v]) => {
                let (found, _) = map_get(slots, k)?;
                let mut out = slots.clone();
                out.push((tt(), k.clone(), v.clone()));
                Some(Ok((Map { slots: out, key: key.clone(), val: val.clone(), trunc: *trunc }, found)))
            }
            (ops::MAP_INSERT, [Map { slots, key, val, trunc: t1 }, Map { slots: other, trunc: t2, .. }]) => {
                let mut clash = Vec::new();
                for (live, k, _) in other {
                    clash.push(and(&[live, &map_get(slots, k)?.0]));
                }
                let mut out = slots.clone();
                out.extend(other.iter().cloned());
                let m = Map { slots: out, key: key.clone(), val: val.clone(), trunc: *t1 || *t2 };
                Some(Ok((m, or(&clash.iter().collect::<Vec<_>>()))))
            }
            (ops::IN, [x, List { slots, .. }]) => {
                let mut hits = Vec::new();
                for (live, y) in slots {
                    match sym_eq(x, y) {
                        Some(eq) => hits.push(and(&[live, &eq])),
                        None => return Some(Err("membership on values the verifier does not model".into())),
                    }
                }
                ok(Bool(or(&hits.iter().collect::<Vec<_>>())))
            }
            ("size", [Str(s)]) => ok(Int(s.length())),
            ("size", [List { slots, .. }]) => ok(Int(Sym::list_len(slots))),
            ("contains", [Str(a), Str(b)]) => ok(Bool(a.contains(b))),
            ("startsWith", [Str(a), Str(b)]) => ok(Bool(b.prefix(a))),
            ("endsWith", [Str(a), Str(b)]) => ok(Bool(b.suffix(a))),
            // positions count characters (code points) in both CEL and Z3
            ("indexOf", [Str(a), Str(b)]) => ok(Int(self.index_of(a, b, &ZInt::from_i64(0)))),
            ("indexOf", [Str(a), Str(b), Int(i)]) => {
                let bad = or(&[&i.lt(ZInt::from_i64(0)), &i.gt(a.length())]);
                Some(Ok((Int(self.index_of(a, b, i)), bad)))
            }
            ("lastIndexOf", [Str(a), Str(b)]) => ok(Int(self.last_index_of(a, b))),
            ("lastIndexOf", [Str(a), Str(b), Int(i)]) => {
                // the last match starting at or before i is the last match inside s[0, i + |b|)
                let bad = or(&[&i.lt(ZInt::from_i64(0)), &i.gt(a.length())]);
                let prefix = a.substr(ZInt::from_i64(0), i + b.length());
                Some(Ok((Int(self.last_index_of(&prefix, b)), bad)))
            }
            ("substring", [Str(a), Int(i)]) => {
                let bad = or(&[&i.lt(ZInt::from_i64(0)), &i.gt(a.length())]);
                Some(Ok((Str(a.substr(i, a.length() - i)), bad)))
            }
            ("substring", [Str(a), Int(i), Int(j)]) => {
                let zero = ZInt::from_i64(0);
                let bad = or(&[&i.lt(&zero), &i.gt(a.length()), &j.lt(&zero), &j.gt(a.length()), &i.gt(j)]);
                Some(Ok((Str(a.substr(i, j - i)), bad)))
            }
            ("charAt", [Str(a), Int(i)]) => {
                // Z3's at() is "" past the end, which is CEL's answer at i == size
                let bad = or(&[&i.lt(ZInt::from_i64(0)), &i.gt(a.length())]);
                Some(Ok((Str(a.at(i)), bad)))
            }
            ("matches", [Str(s), Str(p)]) => {
                let Some(pat) = zutil::str_value(p) else {
                    return Some(Err("matches() with a non-constant pattern".into()));
                };
                match zutil::translate_search(&pat) {
                    Ok(re) => ok(Bool(s.regex_matches(&re))),
                    Err(why) => Some(Err(why)),
                }
            }
            ("int", [Int(x)]) | ("dyn", [Int(x)]) => ok(Int(x.clone())),
            ("int", [Uint(x)]) => Some(Ok((Int(x.clone()), x.gt(ZInt::from_i64(I64_MAX))))),
            ("uint", [Uint(x)]) => ok(Uint(x.clone())),
            ("uint", [Int(x)]) => Some(Ok((Uint(x.clone()), x.lt(ZInt::from_i64(0))))),
            ("dyn", [x]) => ok(x.clone()),
            ("sum", [List { slots, elem, .. }]) if matches!(elem, CelType::Int | CelType::Uint) => {
                let mut acc = ZInt::from_i64(0);
                let mut over = Vec::new();
                let zero = ZInt::from_i64(0);
                for (live, x) in slots {
                    let xi = x.as_int()?.clone();
                    acc = &acc + live.ite(&xi, &zero);
                    let ok_range = if *elem == CelType::Int { int_range(&acc, I64_MIN, I64_MAX) } else { uint_range(&acc) };
                    over.push(and(&[live, &ok_range.not()]));
                }
                let s = if *elem == CelType::Int { Int(acc) } else { Uint(acc) };
                Some(Ok((s, or(&over.iter().collect::<Vec<_>>()))))
            }
            ("min" | "max", [List { slots, elem, .. }]) if matches!(elem, CelType::Int | CelType::Uint) => {
                let mut best: Option<z3::ast::Int> = None;
                let mut any = ff();
                for (live, x) in slots {
                    let xi = x.as_int()?.clone();
                    best = Some(match best {
                        None => xi,
                        Some(b) => {
                            let better = if function == "min" { xi.lt(&b) } else { xi.gt(&b) };
                            and(&[live, &or(&[&any.not(), &better])]).ite(&xi, &b)
                        }
                    });
                    any = or(&[&any, live]);
                }
                let b = best.unwrap_or_else(|| ZInt::from_i64(0));
                let s = if *elem == CelType::Int { Int(b) } else { Uint(b) };
                Some(Ok((s, any.not())))
            }
            ("date", [Str(s)]) => match zutil::str_value(s).and_then(|v| date::parse_date(&v)) {
                Some(d) => ok(Date(ZInt::from_i64(d))),
                None if zutil::str_value(s).is_some() => {
                    let ty = c.type_of(e.id).clone();
                    Some(Ok((self.fresh(&ty), tt())))
                }
                None => Some(Err("date() of a non-constant string".into())),
            },
            ("ageOn", [Date(b), Date(on)]) => {
                let (by, bm, bd) = civil_from_days(b);
                let (oy, om, od) = civil_from_days(on);
                let before = or(&[&om.lt(&bm), &and(&[&om.eq(&bm), &od.lt(&bd)])]);
                ok(Int(&oy - &by - before.ite(&ZInt::from_i64(1), &ZInt::from_i64(0))))
            }
            ("daysUntil", [Date(a), Date(b)]) => ok(Int(b - a)),
            ("year", [Date(d)]) => ok(Int(civil_from_days(d).0)),
            (
                "lowerAscii"
                | "upperAscii"
                | "trim"
                | "string"
                | "int"
                | "uint"
                | "double"
                | "bytes"
                | "bool"
                | "size"
                | "sum"
                | "min"
                | "max"
                | ops::ADD
                | ops::SUBTRACT
                | ops::MULTIPLY
                | ops::DIVIDE
                | ops::MODULO
                | ops::NEGATE
                | ops::INDEX
                | ops::IN,
                _,
            ) => Some(Err(format!("builtin '{function}' on these operand types is not modeled"))),
            _ => None,
        }
    }

    /// Why a solver witness didn't replay: something the encoding couldn't see exactly,
    /// a host function's real value or a builtin that isn't modeled yet.
    pub fn unreplayed_reason(&self) -> String {
        let tabulated = |n: &str| {
            self.func_overloads
                .get(n)
                .is_some_and(|os| os.iter().all(|(o, _)| self.schema.contracts.get(o).is_some_and(|k| k.table.is_some())))
        };
        let quoted: Vec<String> = self
            .opaque_host
            .iter()
            .map(|n| if tabulated(n) { format!("'{n}' (outside its tabulated inputs)") } else { format!("'{n}'") })
            .collect();
        let others: Vec<&String> = self
            .approximations
            .iter()
            .filter(|a| {
                !a.starts_with("function '") && !a.starts_with("relies on") && !a.starts_with("builtin '") && !a.starts_with("dyn ")
            })
            .collect();
        let mut parts = Vec::new();
        if self.reads_dyn {
            parts.push(
                "the answer depends on values of type dyn (from Any or dict[str, Any]), which the verifier can't see into; \
                 give them a concrete type, such as a Pydantic model for a tool's arguments"
                    .to_string(),
            );
        }
        if !self.unmodeled_builtins.is_empty() {
            let names: Vec<String> = self.unmodeled_builtins.iter().map(|n| format!("'{n}'")).collect();
            parts.push(format!(
                "the answer depends on {}, which the verifier doesn't model yet; rewrite the rule without {}, \
                 or treat this check as unverified",
                names.join(", "),
                if names.len() == 1 { "it" } else { "them" }
            ));
        }
        match quoted.len() {
            0 => {}
            n => parts.push(format!(
                "{} on what {} {}, which the verifier can't see; add an ensures= contract, \
                 give the parameters small finite types (bool, Literal, Enum or an int with ge/le) so it can be tabulated, \
                 or write it in CEL with env.define(name, body, params={{...}})",
                if parts.is_empty() { "the answer depends" } else { "it also depends" },
                quoted.join(", "),
                if n == 1 { "returns" } else { "return" }
            )),
        }
        if !others.is_empty() {
            parts.push(format!("approximations: {}", others.iter().map(|s| s.as_str()).collect::<Vec<_>>().join("; ")));
        }
        if parts.is_empty() {
            "internal: solver witness did not replay in the evaluator".into()
        } else {
            parts.join("; ")
        }
    }

    /// Why builtin `function` on `args` can't be encoded: a `dyn` operand, or the builtin
    /// itself. Records which, for `unreplayed_reason`; None means "keep the caller's reason".
    fn unmodeled(&mut self, function: &str, args: &[Sym]) -> Option<String> {
        let name = celspresso_check::display_fn(function);
        if args.iter().any(|a| matches!(a, Sym::Opaque { ty: CelType::Dyn, .. })) {
            self.reads_dyn = true;
            return Some(format!("dyn values in '{name}' are not modeled"));
        }
        self.unmodeled_builtins.insert(name.to_string());
        None
    }

    /// Note that `function` (overload `overload`) is opaque here; returns how to describe it.
    fn note_opaque(&mut self, function: &str, overload: &str, args: &[Sym]) -> String {
        if celspresso_check::is_builtin_overload(overload) {
            if let Some(why) = self.unmodeled(function, args) {
                return why;
            }
            format!("builtin '{}' is not modeled by the verifier", celspresso_check::display_fn(function))
        } else {
            self.opaque_host.insert(function.to_string());
            format!("function '{function}' is uninterpreted")
        }
    }

    fn uninterpreted(&mut self, c: &CheckedExpr, e: &Expr, function: &str, args: &[Sym]) -> SV {
        let sort_of = |t: &CelType| -> Option<Sort> {
            match t {
                CelType::Bool => Some(Sort::bool()),
                CelType::Int | CelType::Uint | CelType::Date | CelType::Timestamp | CelType::Duration => Some(Sort::int()),
                CelType::String => Some(Sort::string()),
                CelType::Double => Some(Sort::double()),
                _ => None,
            }
        };
        let overload = c.overload(e.id).unwrap_or(function).to_string();
        let result_ty = c.type_of(e.id).clone();
        let mut arg_asts: Vec<Dynamic> = Vec::new();
        let mut sorts = Vec::new();
        for a in args {
            let (d, s) = match a {
                Sym::Bool(b) => (Dynamic::from_ast(b), Sort::bool()),
                Sym::Int(i) | Sym::Uint(i) | Sym::Date(i) | Sym::Timestamp(i) | Sym::Duration(i) => (Dynamic::from_ast(i), Sort::int()),
                Sym::Str(s) => (Dynamic::from_ast(s), Sort::string()),
                Sym::Double(d) => (Dynamic::from_ast(d), Sort::double()),
                _ => {
                    let why = self.note_opaque(function, &overload, args);
                    return self.approx(c, e, why);
                }
            };
            arg_asts.push(d);
            sorts.push(s);
        }
        let why = self.note_opaque(function, &overload, args);
        let Some(rsort) = sort_of(&result_ty) else {
            return self.approx(c, e, why);
        };
        self.approximations.insert(why);
        let known = self.func_overloads.entry(function.to_string()).or_default();
        if !known.iter().any(|(o, _)| *o == overload) {
            known.push((overload.clone(), args.len()));
        }
        let (f, ferr) = self.funcs.entry(overload.clone()).or_insert_with(|| {
            let srefs: Vec<&Sort> = sorts.iter().collect();
            (FuncDecl::new(overload.clone(), &srefs, &rsort), FuncDecl::new(format!("{overload}!err"), &srefs, &Sort::bool()))
        });
        let refs: Vec<&dyn Ast> = arg_asts.iter().map(|d| d as &dyn Ast).collect();
        let mut out: Dynamic = f.apply(&refs);
        let mut err: Bool = ferr.apply(&refs).as_bool().unwrap();
        // a tabulated function is exact on its table (opaque only outside it)
        if let Some(table) = self.schema.contracts.get(&overload).and_then(|k| k.table.clone()) {
            for (inputs, result) in table.iter().rev() {
                let Some(conds) = inputs.iter().zip(&arg_asts).map(|(l, a)| Some(a.eq(literal_ast(l)?))).collect::<Option<Vec<Bool>>>()
                else {
                    continue;
                };
                let hit = and(&conds.iter().collect::<Vec<_>>());
                match result {
                    Some(r) => match literal_ast(r) {
                        Some(r) if r.get_sort() == out.get_sort() => {
                            out = hit.ite(&r, &out);
                            err = hit.ite(&ff(), &err);
                        }
                        _ => continue,
                    },
                    None => err = hit.ite(&tt(), &err),
                }
            }
        }
        let v = match result_ty {
            CelType::Bool => Sym::Bool(out.as_bool().unwrap()),
            CelType::Int => {
                let x = out.as_int().unwrap();
                self.assumptions.push(int_range(&x, I64_MIN, I64_MAX));
                Sym::Int(x)
            }
            CelType::Uint => {
                let x = out.as_int().unwrap();
                self.assumptions.push(uint_range(&x));
                Sym::Uint(x)
            }
            CelType::Date => Sym::Date(out.as_int().unwrap()),
            CelType::Double => Sym::Double(out.as_float().unwrap()),
            CelType::Timestamp => {
                let x = out.as_int().unwrap();
                self.assumptions.push(ts_range(&x));
                Sym::Timestamp(x)
            }
            CelType::Duration => {
                let x = out.as_int().unwrap();
                self.assumptions.push(dur_range(&x));
                Sym::Duration(x)
            }
            _ => Sym::Str(out.as_string().unwrap()),
        };
        let contract = self.schema.contracts.get(&overload).cloned();
        if contract.as_ref().is_some_and(|k| k.total) {
            self.assumptions.push(err.not());
            self.approximations.insert(format!("relies on '{function}' never failing (total=True)"));
        }
        if let Some((k, ensures)) = contract.as_ref().and_then(|k| Some((k, k.ensures.as_ref()?))) {
            let depth = self.locals.len();
            for (name, a) in k.params.iter().zip(args) {
                self.locals.push((name.clone(), SV::ok(a.clone())));
            }
            self.locals.push(("result".into(), SV::ok(v.clone())));
            let r = self.encode(ensures);
            self.locals.truncate(depth);
            if let Some(b) = r.v.as_bool() {
                self.assumptions.push(err.not().implies(and(&[b, &r.err.not()])));
                self.approximations.insert(format!("relies on the ensures contract of '{function}'"));
            }
        }
        SV { v, err }
    }

    /// `str.indexof` plus lemmas that hold for it (Z3 reasons about string positions
    /// poorly on its own): a hit is a real occurrence at or after `start`, and none
    /// starts earlier. Facts about Z3's own function, so sound to assume.
    fn index_of(&mut self, a: &ZStr, b: &ZStr, start: &ZInt) -> ZInt {
        let r = zutil::str_index_of(a, b, start);
        let zero = ZInt::from_i64(0);
        let found = r.ge(&zero);
        let occurs = and(&[&a.substr(&r, b.length()).eq(b), &(&r + b.length()).le(a.length()), &r.ge(start)]);
        // no occurrence starting in [start, r): b is not inside a[start, r + |b| - 1)
        let first = a.substr(start, &r + b.length() - ZInt::from_i64(1) - start).contains(b).not();
        let lemma = and(&[&r.ge(ZInt::from_i64(-1)), &found.implies(and(&[&occurs, &or(&[&b.length().eq(&zero), &first])]))]);
        self.assumptions.push(lemma);
        if start.as_i64() == Some(0) {
            self.relate_indexes(a, b, &r, false);
        }
        r
    }

    /// For each haystack/needle pair: found iff `contains`, and the first match is at or
    /// before the last one (the solver rarely finds this ordering by itself).
    fn relate_indexes(&mut self, a: &ZStr, b: &ZStr, r: &ZInt, is_last: bool) {
        let found = r.ge(ZInt::from_i64(0));
        self.assumptions.push(found.eq(a.contains(b)));
        for (a2, b2, r2, last2) in &self.index_terms {
            // hash-consed structural equality: the same terms, not just equal values
            if *last2 != is_last && PartialEq::eq(a2, a) && PartialEq::eq(b2, b) {
                let (first, last) = if is_last { (r2, r) } else { (r, r2) };
                self.assumptions.push(first.le(last));
            }
        }
        self.index_terms.push((a.clone(), b.clone(), r.clone(), is_last));
    }

    /// `str.lastindexof` plus lemmas: a hit is a real occurrence and none starts later.
    fn last_index_of(&mut self, a: &ZStr, b: &ZStr) -> ZInt {
        let r = zutil::str_last_index_of(a, b);
        let found = r.ge(ZInt::from_i64(0));
        let occurs = and(&[&a.substr(&r, b.length()).eq(b), &(&r + b.length()).le(a.length())]);
        let last = a.substr(&r + ZInt::from_i64(1), a.length()).contains(b).not();
        let lemma = and(&[&r.ge(ZInt::from_i64(-1)), &found.implies(and(&[&occurs, &or(&[&b.length().eq(ZInt::from_i64(0)), &last])]))]);
        self.assumptions.push(lemma);
        self.relate_indexes(a, b, &r, true);
        r
    }

    // --------------------------------------------------------------- witness

    /// The concrete value of any symbolic value in a model.
    pub fn value(&self, model: &Model, s: &Sym) -> Value {
        value_of(model, s)
    }

    /// Extract concrete values for every referenced root variable.
    pub fn witness(&self, model: &Model) -> BTreeMap<String, Value> {
        self.vars.iter().map(|(n, s)| (n.clone(), value_of(model, s))).collect()
    }
}

fn default_sym(t: &CelType) -> Option<Sym> {
    Some(match t {
        CelType::Bool => Sym::Bool(ff()),
        CelType::Int => Sym::Int(Int::from_i64(0)),
        CelType::Uint => Sym::Uint(Int::from_i64(0)),
        CelType::String => Sym::Str(ZStr::from("")),
        CelType::Nullable(_) | CelType::Null => Sym::Null,
        CelType::Optional(t) => Sym::Optional { has: ff(), val: Box::new(default_sym(t)?) },
        CelType::List(e) => Sym::List { slots: vec![], elem: (**e).clone(), trunc: false },
        CelType::Map(k, v) => Sym::Map { slots: vec![], key: (**k).clone(), val: (**v).clone(), trunc: false },
        _ => return None,
    })
}

/// A scalar literal as a Z3 term (function tables).
fn literal_ast(l: &celspresso_syntax::Literal) -> Option<Dynamic> {
    use celspresso_syntax::Literal as L;
    Some(match l {
        L::Bool(b) => Dynamic::from_ast(&Bool::from_bool(*b)),
        L::Int(i) => Dynamic::from_ast(&Int::from_i64(*i)),
        L::Uint(u) => Dynamic::from_ast(&Int::from_u64(*u)),
        L::Double(d) => Dynamic::from_ast(&Float::from_f64(*d)),
        L::String(s) => Dynamic::from_ast(&zutil::str_lit(s)),
        _ => return None,
    })
}

/// CEL truncating division/remainder from Z3's Euclidean ones.
fn trunc_divmod(a: &Int, b: &Int) -> (Int, Int) {
    let qe = a.div(b);
    let re = a.modulo(b);
    let zero = Int::from_i64(0);
    let adjust = and(&[&a.lt(&zero), &re.eq(&zero).not()]);
    let step = b.gt(&zero).ite(&Int::from_i64(1), &Int::from_i64(-1));
    let q = adjust.ite(&(&qe + &step), &qe);
    let r = a - &(b * &q);
    (q, r)
}

/// Exact symbolic version of `date::civil_from_days` (floor division by constants only).
fn civil_from_days(days: &Int) -> (Int, Int, Int) {
    let k = |n: i64| Int::from_i64(n);
    let z = days + k(719468);
    let era = z.div(k(146097));
    let doe = &z - &(&era * k(146097));
    let yoe = (&doe - doe.div(k(1460)) + doe.div(k(36524)) - doe.div(k(146096))).div(k(365));
    let y = &yoe + &(&era * k(400));
    let doy = &doe - &(&(&yoe * k(365)) + &yoe.div(k(4)) - yoe.div(k(100)));
    let mp = (&(&doy * k(5)) + k(2)).div(k(153));
    let d = &doy - &(&(&mp * k(153)) + k(2)).div(k(5)) + k(1);
    let m = mp.lt(k(10)).ite(&(&mp + k(3)), &(&mp - k(9)));
    let year = m.le(k(2)).ite(&(&y + k(1)), &y);
    (year, m, d)
}

fn value_of(model: &Model, s: &Sym) -> Value {
    let int = |x: &Int| model.eval(x, true).and_then(|v| v.as_i64()).unwrap_or(0);
    let boolean = |b: &Bool| model.eval(b, true).and_then(|v| v.as_bool()).unwrap_or(false);
    match s {
        Sym::Bool(b) => Value::Bool(boolean(b)),
        Sym::Int(x) => Value::Int(int(x)),
        Sym::Uint(x) => Value::Uint(model.eval(x, true).and_then(|v| v.as_u64()).unwrap_or(0)),
        Sym::Date(x) => Value::Date(int(x)),
        Sym::Double(x) => Value::Double(double_of(model, x)),
        Sym::Timestamp(x) => Value::Timestamp(model.eval(x, true).and_then(|v| v.as_i128()).unwrap_or(0)),
        Sym::Duration(x) => Value::Duration(model.eval(x, true).and_then(|v| v.as_i128()).unwrap_or(0)),
        Sym::Str(x) => Value::str(&model.eval(x, true).and_then(|v| zutil::str_value(&v)).unwrap_or_default()),
        Sym::Null => Value::Null,
        Sym::Nullable { is_null, inner } => {
            if boolean(is_null) {
                Value::Null
            } else {
                value_of(model, inner)
            }
        }
        Sym::List { slots, .. } => Value::list(slots.iter().filter(|(l, _)| boolean(l)).map(|(_, v)| value_of(model, v)).collect()),
        Sym::Optional { has, val } => Value::Optional(boolean(has).then(|| Arc::new(value_of(model, val)))),
        Sym::Map { slots, .. } => Value::Map(Arc::new(
            slots
                .iter()
                .filter(|(l, _, _)| boolean(l))
                .filter_map(|(_, k, v)| Some((Key::from_value(&value_of(model, k))?, value_of(model, v))))
                .collect(),
        )),
        Sym::Struct { name, fields } => Value::Struct(Arc::new(StructValue {
            type_name: name.clone(),
            fields: fields.iter().map(|(k, v)| (k.clone(), value_of(model, v))).collect(),
        })),
        Sym::Opaque { ty, .. } => match ty {
            CelType::Double => Value::Double(0.0),
            CelType::Bytes => Value::Bytes(Arc::from(&[][..])),
            CelType::Map(..) => Value::Map(Arc::new(BTreeMap::<Key, Value>::new())),
            _ => Value::Null,
        },
    }
}

fn is_key_type(t: &CelType) -> bool {
    matches!(t, CelType::Bool | CelType::Int | CelType::Uint | CelType::String)
}

fn double_of(model: &Model, x: &Float) -> f64 {
    let holds = |b: Bool| model.eval(&b, true).and_then(|v| v.as_bool()).unwrap_or(false);
    if holds(x.is_nan()) {
        return f64::NAN;
    }
    if holds(x.is_infinite()) {
        return if holds(x.is_negative()) { f64::NEG_INFINITY } else { f64::INFINITY };
    }
    match model.eval(x, true) {
        Some(v) => model.eval(&v.to_ieee_bv(), true).and_then(|b| b.as_u64()).map(f64::from_bits).unwrap_or_else(|| v.as_f64()),
        None => 0.0,
    }
}

fn ts_field_fn(f: &str) -> bool {
    celspresso_eval::time::TsField::from_function(f).is_some()
}

/// A fixed UTC offset in seconds: `UTC`, `+05:30`, `-02:00` or `02:00`.
fn fixed_offset(name: &str) -> Option<i64> {
    if name == "UTC" {
        return Some(0);
    }
    let (sign, body) = match name.as_bytes().first()? {
        b'+' => (1, &name[1..]),
        b'-' => (-1, &name[1..]),
        b'0'..=b'9' => (1, name),
        _ => return None,
    };
    let (h, m) = body.split_once(':')?;
    let (h, m): (i64, i64) = (h.parse().ok()?, m.parse().ok()?);
    (h <= 23 && m <= 59).then_some(sign * (h * 3600 + m * 60))
}

/// Exact symbolic `time::ts_field` at a fixed offset (Z3 div/mod by positive constants floor).
fn ts_field(ns: &Int, f: &str, offset: i64) -> Int {
    let k = |n: i64| Int::from_i64(n);
    let secs = ns.div(big(NANOS)) + k(offset);
    let days = secs.div(k(86_400));
    let tod = secs.modulo(k(86_400));
    let civil = || civil_from_days(&days);
    match f {
        "getFullYear" => civil().0,
        "getMonth" => civil().1 - k(1),
        "getDate" => civil().2,
        "getDayOfMonth" => civil().2 - k(1),
        "getDayOfWeek" => (&days + k(4)).modulo(k(7)),
        "getDayOfYear" => {
            // days_from_civil(year, 1, 1): January counts as month 13 of the previous year
            let y = civil().0 - k(1);
            let era = y.div(k(400));
            let yoe = &y - &(&era * k(400));
            let doe = &(&yoe * k(365)) + &yoe.div(k(4)) - yoe.div(k(100)) + k(306);
            let jan1 = &(&era * k(146_097)) + &doe - k(719_468);
            &days - &jan1
        }
        "getHours" => tod.div(k(3600)),
        "getMinutes" => tod.div(k(60)).modulo(k(60)),
        "getSeconds" => tod.modulo(k(60)),
        _ => ns.modulo(big(NANOS)).div(k(1_000_000)),
    }
}

/// The zero value test behind `optional.ofNonZeroValue`.
fn is_zero(s: &Sym) -> Option<Bool> {
    Some(match s {
        Sym::Null => tt(),
        Sym::Bool(b) => b.not(),
        Sym::Int(x) | Sym::Uint(x) | Sym::Date(x) | Sym::Timestamp(x) | Sym::Duration(x) => x.eq(Int::from_i64(0)),
        Sym::Str(x) => x.length().eq(Int::from_i64(0)),
        Sym::Double(x) => x.is_zero(),
        Sym::List { slots, .. } => Sym::list_len(slots).eq(Int::from_i64(0)),
        Sym::Map { slots, .. } => Sym::map_len(slots).eq(Int::from_i64(0)),
        Sym::Optional { has, .. } => has.not(),
        Sym::Nullable { is_null, inner } => or(&[is_null, &is_zero(inner)?]),
        _ => return None,
    })
}
