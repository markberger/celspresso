//! Tree-walking CEL evaluator over checked expressions.

pub mod date;
pub mod ext;
pub mod net;
pub mod time;
pub mod validate;
pub mod value;

pub use value::{Key, StructValue, Value};

use celspresso_check::{CheckedExpr, Reference};
use celspresso_syntax::ast::{ops, Comprehension, Expr, ExprId, ExprKind, Literal};
use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap};
use std::fmt;
use std::sync::Arc;

#[derive(Clone, Debug, PartialEq)]
pub struct EvalError {
    pub message: String,
    pub expr_id: ExprId,
}

impl fmt::Display for EvalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.message)
    }
}

pub type EvalResult = Result<Value, EvalError>;

/// Variable bindings.
pub trait Activation {
    fn resolve(&self, name: &str) -> Option<Value>;
}

impl Activation for HashMap<String, Value> {
    fn resolve(&self, name: &str) -> Option<Value> {
        self.get(name).cloned()
    }
}

impl Activation for BTreeMap<String, Value> {
    fn resolve(&self, name: &str) -> Option<Value> {
        self.get(name).cloned()
    }
}

/// Host-provided function implementations (custom functions).
pub trait Functions {
    /// Return `None` if the function is not provided by the host.
    fn call(&self, function: &str, args: &[Value]) -> Option<Result<Value, String>>;
}

pub struct NoFunctions;
impl Functions for NoFunctions {
    fn call(&self, _: &str, _: &[Value]) -> Option<Result<Value, String>> {
        None
    }
}

/// Resource limits for evaluating untrusted expressions.
#[derive(Clone, Copy, Debug)]
pub struct Limits {
    pub max_cost: u64,
    pub max_iterations: u64,
    pub max_string_len: usize,
    pub max_list_len: usize,
    pub max_regex_size: usize,
}

impl Default for Limits {
    fn default() -> Self {
        Limits {
            max_cost: 10_000_000,
            max_iterations: 1_000_000,
            max_string_len: 10_000_000,
            max_list_len: 1_000_000,
            max_regex_size: 1 << 20,
        }
    }
}

/// One step of an evaluation trace: the value (or error) of a node.
pub type Trace = HashMap<ExprId, Result<Value, String>>;

pub struct Evaluator<'a> {
    checked: &'a CheckedExpr,
    act: &'a dyn Activation,
    funcs: &'a dyn Functions,
    limits: Limits,
    locals: Vec<(String, EvalResult)>,
    cost: u64,
    iterations: u64,
    regex_cache: RefCell<HashMap<String, regex::Regex>>,
    trace: Option<Trace>,
}

pub fn evaluate(checked: &CheckedExpr, act: &dyn Activation, funcs: &dyn Functions, limits: Limits) -> EvalResult {
    Evaluator::new(checked, act, funcs, limits).run()
}

/// Evaluate and record the value of every node, for `explain()`.
pub fn evaluate_traced(checked: &CheckedExpr, act: &dyn Activation, funcs: &dyn Functions, limits: Limits) -> (EvalResult, Trace) {
    let mut ev = Evaluator::new(checked, act, funcs, limits);
    ev.trace = Some(Trace::new());
    let r = ev.run();
    (r, ev.trace.unwrap_or_default())
}

fn err(e: &Expr, message: impl Into<String>) -> EvalError {
    EvalError { message: message.into(), expr_id: e.id }
}

impl<'a> Evaluator<'a> {
    pub fn new(checked: &'a CheckedExpr, act: &'a dyn Activation, funcs: &'a dyn Functions, limits: Limits) -> Self {
        Evaluator {
            checked,
            act,
            funcs,
            limits,
            locals: Vec::new(),
            cost: 0,
            iterations: 0,
            regex_cache: RefCell::new(HashMap::new()),
            trace: None,
        }
    }

    pub fn run(&mut self) -> EvalResult {
        let e = &self.checked.expr;
        self.eval(e)
    }

    fn eval(&mut self, e: &Expr) -> EvalResult {
        self.cost += 1;
        if self.cost > self.limits.max_cost {
            return Err(err(e, "evaluation cost limit exceeded"));
        }
        let r = self.eval_inner(e);
        if let Some(t) = self.trace.as_mut() {
            t.insert(e.id, r.clone().map_err(|er| er.message));
        }
        r
    }

    fn eval_inner(&mut self, e: &Expr) -> EvalResult {
        match &e.kind {
            ExprKind::Literal(l) => Ok(match l {
                Literal::Null => Value::Null,
                Literal::Bool(b) => Value::Bool(*b),
                Literal::Int(i) => Value::Int(*i),
                Literal::Uint(u) => Value::Uint(*u),
                Literal::Double(d) => Value::Double(*d),
                Literal::String(s) => Value::String(Arc::from(s.as_str())),
                Literal::Bytes(b) => Value::Bytes(Arc::from(b.as_slice())),
            }),
            ExprKind::Ident(name) => {
                if let Some((_, v)) = self.locals.iter().rev().find(|(n, _)| n == name) {
                    return v.clone();
                }
                match self.checked.refs.get(&e.id) {
                    Some(Reference::Type(t)) => Ok(Value::Type(Arc::from(t.as_str()))),
                    Some(Reference::Var(_)) | None => {
                        self.act.resolve(name).ok_or_else(|| err(e, format!("no value bound for variable '{name}'")))
                    }
                    Some(_) => Err(err(e, format!("unresolved identifier '{name}'"))),
                }
            }
            ExprKind::Select { .. } if matches!(self.checked.refs.get(&e.id), Some(Reference::Type(_))) => {
                let Some(Reference::Type(t)) = self.checked.refs.get(&e.id) else { unreachable!() };
                Ok(Value::Type(Arc::from(t.as_str())))
            }
            ExprKind::Select { .. } if matches!(self.checked.refs.get(&e.id), Some(Reference::Var(_))) => {
                let Some(Reference::Var(name)) = self.checked.refs.get(&e.id) else { unreachable!() };
                self.act.resolve(name).ok_or_else(|| err(e, format!("no value bound for variable '{name}'")))
            }
            ExprKind::Select { operand, field, test_only } => {
                let v = self.eval(operand)?;
                select(e, &v, field, *test_only)
            }
            ExprKind::Call { target, function, args } => self.call(e, target.as_deref(), function, args),
            ExprKind::List(items) => {
                let mut out = Vec::with_capacity(items.len());
                for it in items {
                    if let Some(v) = self.entry(it)? {
                        out.push(v);
                    }
                }
                Ok(Value::list(out))
            }
            ExprKind::Map(entries) => {
                let mut m = BTreeMap::new();
                for (k, v) in entries {
                    let kv = self.eval(k)?;
                    let key = Key::from_value(&kv).ok_or_else(|| err(k, format!("unsupported map key type '{}'", kv.type_name())))?;
                    let Some(vv) = self.entry(v)? else { continue };
                    if m.insert(key, vv).is_some() {
                        return Err(err(k, format!("duplicate map key {kv}")));
                    }
                }
                Ok(Value::Map(Arc::new(m)))
            }
            ExprKind::Struct { type_name, fields } => {
                let mut out = BTreeMap::new();
                let Some(sd) = self.checked.schema.structs.get(type_name) else {
                    return Err(err(e, format!("unknown type '{type_name}'")));
                };
                for f in &sd.fields {
                    if matches!(f.ty, celspresso_check::CelType::Nullable(_)) {
                        out.insert(f.name.clone(), Value::Null);
                    }
                }
                for (name, v) in fields {
                    if sd.field(name).is_none() {
                        return Err(err(v, format!("undefined field '{name}' on {type_name}")));
                    }
                    let vv = self.eval(v)?;
                    out.insert(name.clone(), vv);
                }
                Ok(Value::Struct(Arc::new(StructValue { type_name: type_name.clone(), fields: out })))
            }
            ExprKind::Comprehension(c) => self.comprehension(e, c),
        }
    }

    fn comprehension(&mut self, e: &Expr, c: &Comprehension) -> EvalResult {
        let range = self.eval(&c.iter_range)?;
        // (first, second) variable values per iteration
        let two = c.iter_var2.is_some();
        let items: Vec<(Value, Value)> = match &range {
            Value::List(l) if two => l.iter().enumerate().map(|(i, v)| (Value::Int(i as i64), v.clone())).collect(),
            Value::List(l) => l.iter().map(|v| (v.clone(), Value::Null)).collect(),
            Value::Map(m) => m.iter().map(|(k, v)| (k.to_value(), v.clone())).collect(),
            other => return Err(err(&c.iter_range, format!("cannot iterate over '{}'", other.type_name()))),
        };
        let accu = self.eval(&c.accu_init)?;
        self.locals.push((c.accu_var.clone(), Ok(accu)));
        let accu_idx = self.locals.len() - 1;
        let mut result = Ok(());
        for item in items {
            self.iterations += 1;
            if self.iterations > self.limits.max_iterations {
                result = Err(err(e, "comprehension iteration limit exceeded"));
                break;
            }
            match self.eval(&c.loop_condition) {
                Ok(Value::Bool(true)) => {}
                Ok(Value::Bool(false)) => break,
                Ok(other) => {
                    result = Err(err(&c.loop_condition, format!("loop condition is not bool: {}", other.type_name())));
                    break;
                }
                Err(er) => {
                    result = Err(er);
                    break;
                }
            }
            let (first, second) = item;
            self.locals.push((c.iter_var.clone(), Ok(first)));
            if let Some(v2) = &c.iter_var2 {
                self.locals.push((v2.clone(), Ok(second)));
            }
            // errors are values for the accumulator: `err && false` must still be false
            let step = self.eval(&c.loop_step);
            self.locals.truncate(accu_idx + 1);
            self.locals[accu_idx].1 = step;
        }
        let r = match result {
            Ok(()) => self.eval(&c.result),
            Err(er) => Err(er),
        };
        self.locals.truncate(accu_idx);
        r
    }

    fn call(&mut self, e: &Expr, target: Option<&Expr>, function: &str, args: &[Expr]) -> EvalResult {
        // Non-strict operators first.
        match function {
            ops::LOGICAL_AND | ops::LOGICAL_OR => {
                let is_and = function == ops::LOGICAL_AND;
                let l = self.eval(&args[0]);
                if let Ok(Value::Bool(b)) = l {
                    if b != is_and {
                        return Ok(Value::Bool(b));
                    }
                }
                let r = self.eval(&args[1]);
                if let Ok(Value::Bool(b)) = r {
                    if b != is_and {
                        return Ok(Value::Bool(b));
                    }
                }
                return match (l, r) {
                    (Ok(Value::Bool(_)), Ok(Value::Bool(b))) => Ok(Value::Bool(b)),
                    (Err(er), _) | (_, Err(er)) => Err(er),
                    _ => Err(err(e, format!("no such overload for '{}'", function))),
                };
            }
            ops::CONDITIONAL => {
                return match self.eval(&args[0])? {
                    Value::Bool(true) => self.eval(&args[1]),
                    Value::Bool(false) => self.eval(&args[2]),
                    other => Err(err(&args[0], format!("ternary condition is not bool: {}", other.type_name()))),
                };
            }
            ops::NOT_STRICTLY_FALSE => {
                return Ok(match self.eval(&args[0]) {
                    Ok(Value::Bool(b)) => Value::Bool(b),
                    _ => Value::Bool(true),
                });
            }
            _ => {}
        }
        let mut vals = Vec::with_capacity(args.len() + 1);
        if let Some(t) = target {
            vals.push(self.eval(t)?);
        }
        for a in args {
            vals.push(self.eval(a)?);
        }
        if let Some(r) = self.funcs.call(function, &vals) {
            return r.map_err(|m| err(e, m));
        }
        self.builtin(e, function, &vals)
    }

    /// A list element or map value; `?e` entries are dropped when the optional is empty.
    fn entry(&mut self, e: &Expr) -> Result<Option<Value>, EvalError> {
        match &e.kind {
            ExprKind::Call { target: None, function, args } if function == ops::OPT_ENTRY && args.len() == 1 => {
                match self.eval(&args[0])? {
                    Value::Optional(o) => Ok(o.map(|v| v.as_ref().clone())),
                    other => Err(err(e, format!("optional entry must be an optional value, got {}", other.type_name()))),
                }
            }
            _ => self.eval(e).map(Some),
        }
    }

    fn check_len(&self, e: &Expr, v: Value) -> EvalResult {
        match &v {
            Value::String(s) if s.len() > self.limits.max_string_len => Err(err(e, "string length limit exceeded")),
            Value::Bytes(b) if b.len() > self.limits.max_string_len => Err(err(e, "bytes length limit exceeded")),
            Value::List(l) if l.len() > self.limits.max_list_len => Err(err(e, "list length limit exceeded")),
            _ => Ok(v),
        }
    }

    fn regex(&self, e: &Expr, pattern: &str) -> Result<regex::Regex, EvalError> {
        if let Some(r) = self.regex_cache.borrow().get(pattern) {
            return Ok(r.clone());
        }
        let r = regex::RegexBuilder::new(pattern)
            .size_limit(self.limits.max_regex_size)
            .build()
            .map_err(|er| err(e, format!("invalid regex: {er}")))?;
        self.regex_cache.borrow_mut().insert(pattern.to_string(), r.clone());
        Ok(r)
    }

    fn builtin(&mut self, e: &Expr, function: &str, v: &[Value]) -> EvalResult {
        use Value::*;
        let overflow = || err(e, "integer overflow");
        let no_overload = || {
            let tys: Vec<std::string::String> = v.iter().map(|x| x.type_name()).collect();
            err(e, format!("no such overload: {function}({})", tys.join(", ")))
        };
        let ts = |ns: Option<i128>| match ns {
            Some(ns) if time::ts_in_range(ns) => Ok(Timestamp(ns)),
            _ => Err(err(e, "timestamp out of range")),
        };
        let dur = |ns: Option<i128>| match ns {
            Some(ns) if time::dur_in_range(ns) => Ok(Duration(ns)),
            _ => Err(err(e, "duration out of range")),
        };
        Ok(match (function, v) {
            (ops::LOGICAL_NOT, [Bool(b)]) => Bool(!b),
            (ops::ADD, [Timestamp(t), Duration(d)]) | (ops::ADD, [Duration(d), Timestamp(t)]) => ts(t.checked_add(*d))?,
            (ops::ADD, [Duration(a), Duration(b)]) => dur(a.checked_add(*b))?,
            (ops::SUBTRACT, [Timestamp(t), Duration(d)]) => ts(t.checked_sub(*d))?,
            (ops::SUBTRACT, [Timestamp(a), Timestamp(b)]) => dur(a.checked_sub(*b))?,
            (ops::SUBTRACT, [Duration(a), Duration(b)]) => dur(a.checked_sub(*b))?,
            ("type", [x]) => Type(Arc::from(x.type_name())),
            ("timestamp", [String(s)]) => {
                Timestamp(time::parse_timestamp(s).ok_or_else(|| err(e, format!("invalid timestamp {}", Value::String(s.clone()))))?)
            }
            ("timestamp", [Int(secs)]) => ts(time::ts_from_seconds(*secs))?,
            ("timestamp", [Timestamp(t)]) => Timestamp(*t),
            ("duration", [String(s)]) => {
                Duration(time::parse_duration(s).ok_or_else(|| err(e, format!("invalid duration {}", Value::String(s.clone()))))?)
            }
            ("duration", [Duration(d)]) => Duration(*d),
            ("int", [Timestamp(t)]) => Int(time::ts_seconds(*t)),
            ("string", [Timestamp(t)]) => String(Arc::from(time::format_timestamp(*t))),
            ("string", [Duration(d)]) => String(Arc::from(time::format_duration(*d))),
            (f, [Timestamp(t), rest @ ..]) if rest.len() <= 1 && time::TsField::from_function(f).is_some() => {
                let field = time::TsField::from_function(f).unwrap();
                let tz = match rest {
                    [String(z)] => Some(z.as_ref()),
                    [] => None,
                    _ => return Err(no_overload()),
                };
                Int(time::ts_field(*t, field, tz).map_err(|m| err(e, m))?)
            }
            (f, [Duration(d)]) if time::TsField::from_function(f).is_some() => {
                Int(time::dur_field(*d, time::TsField::from_function(f).unwrap()).ok_or_else(no_overload)?)
            }
            (ops::NEGATE, [Int(i)]) => Int(i.checked_neg().ok_or_else(overflow)?),
            (ops::NEGATE, [Double(d)]) => Double(-d),
            (ops::ADD, [Int(a), Int(b)]) => Int(a.checked_add(*b).ok_or_else(overflow)?),
            (ops::ADD, [Uint(a), Uint(b)]) => Uint(a.checked_add(*b).ok_or_else(overflow)?),
            (ops::ADD, [Double(a), Double(b)]) => Double(a + b),
            (ops::ADD, [String(a), String(b)]) => return self.check_len(e, String(Arc::from(format!("{a}{b}")))),
            (ops::ADD, [Bytes(a), Bytes(b)]) => return self.check_len(e, Bytes(Arc::from([a.as_ref(), b.as_ref()].concat()))),
            (ops::ADD, [List(a), List(b)]) => {
                let mut out = a.as_ref().clone();
                out.extend(b.iter().cloned());
                return self.check_len(e, Value::list(out));
            }
            (ops::ADD, [Date(d), Int(n)]) => Date(d.checked_add(*n).ok_or_else(overflow)?),
            (ops::SUBTRACT, [Int(a), Int(b)]) => Int(a.checked_sub(*b).ok_or_else(overflow)?),
            (ops::SUBTRACT, [Uint(a), Uint(b)]) => Uint(a.checked_sub(*b).ok_or_else(overflow)?),
            (ops::SUBTRACT, [Double(a), Double(b)]) => Double(a - b),
            (ops::SUBTRACT, [Date(a), Date(b)]) => Int(a - b),
            (ops::SUBTRACT, [Date(d), Int(n)]) => Date(d.checked_sub(*n).ok_or_else(overflow)?),
            (ops::MULTIPLY, [Int(a), Int(b)]) => Int(a.checked_mul(*b).ok_or_else(overflow)?),
            (ops::MULTIPLY, [Uint(a), Uint(b)]) => Uint(a.checked_mul(*b).ok_or_else(overflow)?),
            (ops::MULTIPLY, [Double(a), Double(b)]) => Double(a * b),
            (ops::DIVIDE, [Int(_), Int(0)]) | (ops::MODULO, [Int(_), Int(0)]) => return Err(err(e, "division by zero")),
            (ops::DIVIDE, [Uint(_), Uint(0)]) | (ops::MODULO, [Uint(_), Uint(0)]) => return Err(err(e, "division by zero")),
            (ops::DIVIDE, [Int(a), Int(b)]) => Int(a.checked_div(*b).ok_or_else(overflow)?),
            (ops::DIVIDE, [Uint(a), Uint(b)]) => Uint(a / b),
            (ops::DIVIDE, [Double(a), Double(b)]) => Double(a / b),
            (ops::MODULO, [Int(a), Int(b)]) => Int(a.checked_rem(*b).ok_or_else(overflow)?),
            (ops::MODULO, [Uint(a), Uint(b)]) => Uint(a % b),
            (ops::EQUALS, [a, b]) => Bool(a.cel_eq(b)),
            (ops::NOT_EQUALS, [a, b]) => Bool(!a.cel_eq(b)),
            (ops::LESS | ops::LESS_EQUALS | ops::GREATER | ops::GREATER_EQUALS, [a, b]) => {
                use std::cmp::Ordering as O;
                let ord = match (a, b) {
                    (String(x), String(y)) => Some(x.cmp(y)),
                    (Bytes(x), Bytes(y)) => Some(x.cmp(y)),
                    (Bool(x), Bool(y)) => Some(x.cmp(y)),
                    (Date(x), Date(y)) => Some(x.cmp(y)),
                    (Timestamp(x), Timestamp(y)) | (Duration(x), Duration(y)) => Some(x.cmp(y)),
                    _ if matches!(a, Int(_) | Uint(_) | Double(_)) && matches!(b, Int(_) | Uint(_) | Double(_)) => {
                        match value::numeric_cmp(a, b) {
                            Some(o) => Some(o),
                            None => return Ok(Bool(false)), // NaN
                        }
                    }
                    _ => None,
                };
                let ord = ord.ok_or_else(no_overload)?;
                Bool(match function {
                    ops::LESS => ord == O::Less,
                    ops::LESS_EQUALS => ord != O::Greater,
                    ops::GREATER => ord == O::Greater,
                    _ => ord != O::Less,
                })
            }
            (ops::OPT_SELECT, [x, String(f)]) => opt_select(e, x, f)?,
            (ops::INDEX, [Optional(None), _]) | (ops::OPT_INDEX, [Optional(None), _]) => Optional(None),
            (ops::INDEX | ops::OPT_INDEX, [Optional(Some(x)), idx]) => {
                let x = x.as_ref().clone();
                return self.builtin(e, ops::OPT_INDEX, &[x, idx.clone()]);
            }
            (ops::OPT_INDEX, [List(l), idx]) => {
                let i = match idx {
                    Int(i) => *i,
                    Uint(u) => i64::try_from(*u).unwrap_or(i64::MAX),
                    Double(d) if d.fract() == 0.0 => *d as i64,
                    _ => return Err(no_overload()),
                };
                Optional(usize::try_from(i).ok().and_then(|i| l.get(i)).map(|v| Arc::new(v.clone())))
            }
            (ops::OPT_INDEX, [Map(m), k]) => {
                let key = Key::from_value(k).ok_or_else(no_overload)?;
                Optional(m.get(&key).map(|v| Arc::new(v.clone())))
            }
            (ops::INDEX, [List(l), idx]) => {
                let i = match idx {
                    Int(i) => *i,
                    Uint(u) => i64::try_from(*u).unwrap_or(i64::MAX),
                    Double(d) if d.fract() == 0.0 => *d as i64,
                    _ => return Err(no_overload()),
                };
                if i < 0 || i as usize >= l.len() {
                    return Err(err(e, format!("index out of range: {i}")));
                }
                l[i as usize].clone()
            }
            (ops::INDEX, [Map(m), k]) => {
                let key = Key::from_value(k).ok_or_else(no_overload)?;
                m.get(&key).cloned().ok_or_else(|| err(e, format!("no such key: {k}")))?
            }
            (ops::MAP_INSERT, [Map(m), k, val]) => {
                let key = Key::from_value(k).ok_or_else(no_overload)?;
                let mut out = m.as_ref().clone();
                if out.insert(key, val.clone()).is_some() {
                    return Err(err(e, format!("insert failed: key {k} already exists")));
                }
                Map(Arc::new(out))
            }
            (ops::MAP_INSERT, [Map(m), Map(other)]) => {
                let mut out = m.as_ref().clone();
                for (k, val) in other.iter() {
                    if out.insert(k.clone(), val.clone()).is_some() {
                        return Err(err(e, format!("insert failed: key {} already exists", k.to_value())));
                    }
                }
                Map(Arc::new(out))
            }
            (ops::IN, [x, List(l)]) => Bool(l.iter().any(|y| x.cel_eq(y))),
            (ops::IN, [x, Map(m)]) => Bool(Key::from_value(x).is_some_and(|k| m.contains_key(&k))),
            ("size", [String(s)]) => Int(s.chars().count() as i64),
            ("size", [Bytes(b)]) => Int(b.len() as i64),
            ("size", [List(l)]) => Int(l.len() as i64),
            ("size", [Map(m)]) => Int(m.len() as i64),
            ("contains", [String(a), String(b)]) => Bool(a.contains(b.as_ref())),
            ("startsWith", [String(a), String(b)]) => Bool(a.starts_with(b.as_ref())),
            ("endsWith", [String(a), String(b)]) => Bool(a.ends_with(b.as_ref())),
            ("matches", [String(a), String(p)]) => Bool(self.regex(e, p)?.is_match(a)),
            ("lowerAscii", [String(a)]) => String(Arc::from(a.to_ascii_lowercase())),
            ("upperAscii", [String(a)]) => String(Arc::from(a.to_ascii_uppercase())),
            ("trim", [String(a)]) => String(Arc::from(a.trim())),
            ("int", [Int(i)]) => Int(*i),
            ("int", [Uint(u)]) => Int(i64::try_from(*u).map_err(|_| err(e, "int range error"))?),
            ("int", [Double(d)]) => {
                if d.is_nan() || *d <= -9.223372036854776e18 || *d >= 9.223372036854776e18 {
                    return Err(err(e, "int range error"));
                }
                Int(d.trunc() as i64)
            }
            ("int", [String(s)]) => Int(s.parse().map_err(|_| err(e, format!("cannot convert {} to int", Value::String(s.clone()))))?),
            ("uint", [Uint(u)]) => Uint(*u),
            ("uint", [Int(i)]) => Uint(u64::try_from(*i).map_err(|_| err(e, "uint range error"))?),
            ("uint", [Double(d)]) => {
                if d.is_nan() || *d < 0.0 || *d >= 1.8446744073709552e19 {
                    return Err(err(e, "uint range error"));
                }
                Uint(d.trunc() as u64)
            }
            ("uint", [String(s)]) => Uint(s.parse().map_err(|_| err(e, "cannot convert to uint"))?),
            ("double", [Double(d)]) => Double(*d),
            ("double", [Int(i)]) => Double(*i as f64),
            ("double", [Uint(u)]) => Double(*u as f64),
            ("double", [String(s)]) => Double(s.parse().map_err(|_| err(e, "cannot convert to double"))?),
            ("string", [String(s)]) => String(s.clone()),
            ("string", [Int(i)]) => String(Arc::from(i.to_string())),
            ("string", [Uint(u)]) => String(Arc::from(u.to_string())),
            ("string", [Double(d)]) => String(Arc::from(d.to_string())),
            ("string", [Bool(b)]) => String(Arc::from(b.to_string())),
            ("string", [Bytes(b)]) => String(Arc::from(std::str::from_utf8(b).map_err(|_| err(e, "invalid UTF-8 in bytes"))?)),
            ("string", [Date(d)]) => String(Arc::from(date::format_date(*d))),
            ("bytes", [String(s)]) => Bytes(Arc::from(s.as_bytes())),
            ("bytes", [Bytes(b)]) => Bytes(b.clone()),
            ("bool", [Bool(b)]) => Bool(*b),
            ("bool", [String(s)]) => match s.as_ref() {
                "true" | "TRUE" | "True" | "t" | "1" => Bool(true),
                "false" | "FALSE" | "False" | "f" | "0" => Bool(false),
                _ => return Err(err(e, "cannot convert to bool")),
            },
            ("dyn", [x]) => x.clone(),
            ("sum", [List(l)]) => {
                let mut acc: Option<Value> = None;
                for x in l.iter() {
                    acc = Some(match (acc, x) {
                        (None, x) => x.clone(),
                        (Some(Int(a)), Int(b)) => Int(a.checked_add(*b).ok_or_else(overflow)?),
                        (Some(Uint(a)), Uint(b)) => Uint(a.checked_add(*b).ok_or_else(overflow)?),
                        (Some(Double(a)), Double(b)) => Double(a + b),
                        _ => return Err(no_overload()),
                    });
                }
                acc.unwrap_or(Int(0))
            }
            ("min" | "max", [List(l)]) => {
                let mut best: Option<&Value> = None;
                for x in l.iter() {
                    best = Some(match best {
                        None => x,
                        Some(b) => {
                            let o = value::numeric_cmp(x, b).ok_or_else(no_overload)?;
                            let better = if function == "min" { o.is_lt() } else { o.is_gt() };
                            if better {
                                x
                            } else {
                                b
                            }
                        }
                    });
                }
                best.cloned().ok_or_else(|| err(e, format!("{function}() of empty list")))?
            }
            ("date", [String(s)]) => Date(date::parse_date(s).ok_or_else(|| err(e, format!("invalid date '{s}'")))?),
            ("ageOn", [Date(b), Date(on)]) => Int(date::age_on(*b, *on)),
            ("daysUntil", [Date(a), Date(b)]) => Int(b - a),
            ("year", [Date(d)]) => Int(date::civil_from_days(*d).0),
            _ => match ext::call(function, v) {
                Some(Ok(out)) => return self.check_len(e, out),
                Some(Err(m)) => return Err(err(e, m)),
                None => return Err(no_overload()),
            },
        })
    }
}

/// `v.?field`: an optional of the field, empty when it is absent.
fn opt_select(e: &Expr, v: &Value, field: &str) -> EvalResult {
    let some = |x: &Value| Value::Optional(Some(Arc::new(x.clone())));
    match v {
        Value::Optional(None) => Ok(Value::Optional(None)),
        Value::Optional(Some(x)) => opt_select(e, x, field),
        Value::Map(m) => Ok(m.get(&Key::String(Arc::from(field))).map_or(Value::Optional(None), some)),
        Value::Struct(s) => Ok(s.fields.get(field).map_or(Value::Optional(None), some)),
        other => select(e, other, field, false).map(|x| some(&x)),
    }
}

fn select(e: &Expr, v: &Value, field: &str, test_only: bool) -> EvalResult {
    match v {
        // selecting through an optional behaves like `.?`; has() on an empty one is false
        Value::Optional(None) if test_only => Ok(Value::Bool(false)),
        Value::Optional(Some(x)) if test_only => select(e, x, field, true),
        Value::Optional(_) => opt_select(e, v, field),
        Value::Struct(s) => {
            if test_only {
                return Ok(Value::Bool(s.fields.contains_key(field)));
            }
            s.fields.get(field).cloned().ok_or_else(|| err(e, format!("no such field '{field}'")))
        }
        Value::Map(m) => {
            let key = Key::String(Arc::from(field));
            if test_only {
                return Ok(Value::Bool(m.contains_key(&key)));
            }
            m.get(&key).cloned().ok_or_else(|| err(e, format!("no such key: '{field}'")))
        }
        Value::Null => Err(err(e, format!("cannot select field '{field}' from null"))),
        other => Err(err(e, format!("type '{}' does not support field selection", other.type_name()))),
    }
}

#[cfg(test)]
mod tests;
