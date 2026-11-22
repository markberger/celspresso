//! Translate checked CEL expressions into Z3 terms.

use crate::sym::*;
use crate::zutil;
use celspresso_check::{CelType, CheckedExpr, Constraints, Reference, Schema};
use celspresso_eval::{date, Key, StructValue, Value};
use celspresso_syntax::ast::{ops, Expr, ExprKind, Literal};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::sync::Arc;
use z3::ast::{Ast, Bool, Dynamic, Int, Int as ZInt, String as ZStr};
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
    fresh: u32,
}

fn int_range(x: &Int, lo: i64, hi: i64) -> Bool {
    and(&[&x.ge(Int::from_i64(lo)), &x.le(Int::from_i64(hi))])
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
            fresh: 0,
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
                Sym::Date(x)
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
            CelType::Struct(name) => {
                let Some(sd) = self.schema.structs.get(name).cloned() else { return self.opaque(ty) };
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
                Literal::Double(_) => self.approx(c, e, "double arithmetic is not yet modeled"),
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
                            // declared fields are always present (Pydantic semantics)
                            return SV { v: Sym::Bool(tt()), err };
                        }
                        match fields.get(field) {
                            Some(v) => SV { v: v.clone(), err },
                            None => self.approx(c, e, format!("unknown field '{field}'")),
                        }
                    }
                    Sym::Null => SV { v: self.fresh(c.type_of(e.id)), err: tt() },
                    _ => self.approx(c, e, "field selection on maps/dyn is not yet modeled"),
                }
            }
            ExprKind::List(items) => {
                let mut slots = Vec::new();
                let mut errs = Vec::new();
                for it in items {
                    let v = self.enc(c, it);
                    errs.push(v.err);
                    slots.push((tt(), v.v));
                }
                let elem = match c.type_of(e.id) {
                    CelType::List(t) => (**t).clone(),
                    _ => CelType::Dyn,
                };
                SV { v: Sym::List { slots, elem, trunc: false }, err: or(&errs.iter().collect::<Vec<_>>()) }
            }
            ExprKind::Map(_) => self.approx(c, e, "map values are not yet modeled"),
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
                let Sym::List { slots, trunc, .. } = range.v.clone() else {
                    return self.approx(c, e, "comprehension over maps is not yet modeled");
                };
                if trunc {
                    self.bounded = true;
                }
                let init = self.enc(c, &comp.accu_init);
                self.locals.push((comp.accu_var.clone(), init));
                let accu_idx = self.locals.len() - 1;
                let mut stopped = ff();
                for (live, elem) in slots {
                    let accu = self.locals[accu_idx].1.clone();
                    let cond = self.enc(c, &comp.loop_condition);
                    let cv = cond.v.as_bool().cloned().unwrap_or_else(tt);
                    let active = and(&[&live, &stopped.not()]);
                    self.locals.push((comp.iter_var.clone(), SV::ok(elem)));
                    let step = self.enc(c, &comp.loop_step);
                    self.locals.pop();
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
                let Some(cv) = cond.v.as_bool() else { return self.approx(c, e, "non-bool condition") };
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
        let keeps_null = matches!(function, ops::EQUALS | ops::NOT_EQUALS | ops::IN);
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

    fn mark_lists(&mut self, args: &[Sym]) {
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
            (ops::ADD, [Int(a), Int(b)]) => int_res(a + b),
            (ops::ADD, [Uint(a), Uint(b)]) => uint_res(a + b),
            (ops::ADD, [Str(a), Str(b)]) => ok(Str(ZStr::concat(&[a.clone(), b.clone()]))),
            (ops::ADD, [List { slots: a, elem, trunc: t1 }, List { slots: b, trunc: t2, .. }]) => {
                let mut slots = a.clone();
                slots.extend(b.iter().cloned());
                ok(List { slots, elem: elem.clone(), trunc: *t1 || *t2 })
            }
            (ops::ADD, [Date(d), Int(n)]) => ok(Date(d + n)),
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
                    (Int(x) | Uint(x) | Date(x), Int(y) | Uint(y) | Date(y)) => match function {
                        ops::LESS => x.lt(y),
                        ops::LESS_EQUALS => x.le(y),
                        ops::GREATER => x.gt(y),
                        _ => x.ge(y),
                    },
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
                "lowerAscii" | "upperAscii" | "trim" | "string" | "int" | "uint" | "double" | "bytes" | "bool" | "size"
                | "sum" | "min" | "max" | ops::ADD | ops::SUBTRACT | ops::MULTIPLY | ops::DIVIDE | ops::MODULO
                | ops::NEGATE | ops::INDEX | ops::IN,
                _,
            ) => Some(Err(format!("'{function}' on these operand types is not yet modeled"))),
            _ => None,
        }
    }

    /// Custom (host) functions become uninterpreted functions of their arguments.
    /// A fact learned by running a real custom function: `f(args) == result` (and no
    /// error), or `f!err(args)` if it raised. None if the call cannot be expressed.
    pub fn refine(&self, function: &str, args: &[Value], result: &Result<Value, String>) -> Option<Bool> {
        let overloads = self.func_overloads.get(function)?;
        let (overload, _) = overloads.iter().find(|(_, n)| *n == args.len())?;
        let (f, ferr) = self.funcs.get(overload)?;
        let lit = |v: &Value| -> Option<Dynamic> {
            Some(match v {
                Value::Bool(b) => Dynamic::from_ast(&Bool::from_bool(*b)),
                Value::Int(i) | Value::Date(i) => Dynamic::from_ast(&Int::from_i64(*i)),
                Value::Uint(u) => Dynamic::from_ast(&Int::from_u64(*u)),
                Value::String(s) => Dynamic::from_ast(&zutil::str_lit(s)),
                _ => return None,
            })
        };
        let arg_asts = args.iter().map(lit).collect::<Option<Vec<_>>>()?;
        let refs: Vec<&dyn Ast> = arg_asts.iter().map(|d| d as &dyn Ast).collect();
        let err = ferr.apply(&refs).as_bool()?;
        Some(match result {
            Err(_) => err,
            Ok(v) => and(&[&f.apply(&refs).eq(lit(v)?), &err.not()]),
        })
    }

    fn uninterpreted(&mut self, c: &CheckedExpr, e: &Expr, function: &str, args: &[Sym]) -> SV {
        let sort_of = |t: &CelType| -> Option<Sort> {
            match t {
                CelType::Bool => Some(Sort::bool()),
                CelType::Int | CelType::Uint | CelType::Date => Some(Sort::int()),
                CelType::String => Some(Sort::string()),
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
                Sym::Int(i) | Sym::Uint(i) | Sym::Date(i) => (Dynamic::from_ast(i), Sort::int()),
                Sym::Str(s) => (Dynamic::from_ast(s), Sort::string()),
                _ => return self.approx(c, e, format!("custom function '{function}' with structured arguments")),
            };
            arg_asts.push(d);
            sorts.push(s);
        }
        let Some(rsort) = sort_of(&result_ty) else {
            return self.approx(c, e, format!("custom function '{function}' returning {result_ty}"));
        };
        self.approximations.insert(format!("custom function '{function}' is uninterpreted"));
        let known = self.func_overloads.entry(function.to_string()).or_default();
        if !known.iter().any(|(o, _)| *o == overload) {
            known.push((overload.clone(), args.len()));
        }
        let (f, ferr) = self.funcs.entry(overload.clone()).or_insert_with(|| {
            let srefs: Vec<&Sort> = sorts.iter().collect();
            (FuncDecl::new(overload.clone(), &srefs, &rsort), FuncDecl::new(format!("{overload}!err"), &srefs, &Sort::bool()))
        });
        let refs: Vec<&dyn Ast> = arg_asts.iter().map(|d| d as &dyn Ast).collect();
        let out: Dynamic = f.apply(&refs);
        let err: Bool = ferr.apply(&refs).as_bool().unwrap();
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
            _ => Sym::Str(out.as_string().unwrap()),
        };
        SV { v, err }
    }

    // --------------------------------------------------------------- witness

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
        CelType::List(e) => Sym::List { slots: vec![], elem: (**e).clone(), trunc: false },
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
        Sym::Str(x) => Value::str(&model.eval(x, true).and_then(|v| zutil::str_value(&v)).unwrap_or_default()),
        Sym::Null => Value::Null,
        Sym::Nullable { is_null, inner } => {
            if boolean(is_null) {
                Value::Null
            } else {
                value_of(model, inner)
            }
        }
        Sym::List { slots, .. } => {
            Value::list(slots.iter().filter(|(l, _)| boolean(l)).map(|(_, v)| value_of(model, v)).collect())
        }
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
