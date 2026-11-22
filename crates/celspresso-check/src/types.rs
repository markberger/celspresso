use std::collections::HashMap;
use std::fmt;

/// Static CEL types.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum CelType {
    Bool,
    Int,
    Uint,
    Double,
    String,
    Bytes,
    Null,
    /// Calendar date extension (days since epoch); maps to `datetime.date`.
    Date,
    List(Box<CelType>),
    Map(Box<CelType>, Box<CelType>),
    /// A named record type declared in the environment schema.
    Struct(String),
    /// `T` or `null` (Pydantic `T | None`, proto wrapper types).
    Nullable(Box<CelType>),
    Dyn,
    /// Type parameter used by generic overloads and inference.
    Param(String),
    /// Placeholder after a type error, suppresses cascading errors.
    Error,
}

impl CelType {
    pub fn list(t: CelType) -> CelType {
        CelType::List(Box::new(t))
    }
    pub fn map(k: CelType, v: CelType) -> CelType {
        CelType::Map(Box::new(k), Box::new(v))
    }
    pub fn nullable(t: CelType) -> CelType {
        match t {
            CelType::Nullable(_) | CelType::Null | CelType::Dyn => t,
            t => CelType::Nullable(Box::new(t)),
        }
    }
    pub fn p(name: &str) -> CelType {
        CelType::Param(name.to_string())
    }
    pub fn is_numeric(&self) -> bool {
        matches!(self, CelType::Int | CelType::Uint | CelType::Double)
    }
    /// Strip a Nullable wrapper.
    pub fn non_null(&self) -> &CelType {
        match self {
            CelType::Nullable(t) => t,
            t => t,
        }
    }
    pub fn is_dyn_like(&self) -> bool {
        matches!(self, CelType::Dyn | CelType::Error)
    }

    fn substitute(&self, s: &Subst) -> CelType {
        match self {
            CelType::Param(p) => match s.get(p) {
                Some(t) => t.substitute(s),
                None => self.clone(),
            },
            CelType::List(e) => CelType::list(e.substitute(s)),
            CelType::Map(k, v) => CelType::map(k.substitute(s), v.substitute(s)),
            CelType::Nullable(t) => CelType::nullable(t.substitute(s)),
            t => t.clone(),
        }
    }

    /// Replace any unbound type parameters with `dyn`.
    pub fn finalize(&self, s: &Subst) -> CelType {
        match self.substitute(s) {
            CelType::Param(_) => CelType::Dyn,
            CelType::List(e) => CelType::list(e.finalize(s)),
            CelType::Map(k, v) => CelType::map(k.finalize(s), v.finalize(s)),
            CelType::Nullable(t) => CelType::nullable(t.finalize(s)),
            t => t,
        }
    }
}

impl fmt::Display for CelType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CelType::Bool => write!(f, "bool"),
            CelType::Int => write!(f, "int"),
            CelType::Uint => write!(f, "uint"),
            CelType::Double => write!(f, "double"),
            CelType::String => write!(f, "string"),
            CelType::Bytes => write!(f, "bytes"),
            CelType::Null => write!(f, "null_type"),
            CelType::Date => write!(f, "date"),
            CelType::List(e) => write!(f, "list({e})"),
            CelType::Map(k, v) => write!(f, "map({k}, {v})"),
            CelType::Struct(n) => write!(f, "{n}"),
            CelType::Nullable(t) => write!(f, "{t}?"),
            CelType::Dyn => write!(f, "dyn"),
            CelType::Param(p) => write!(f, "{p}"),
            CelType::Error => write!(f, "*error*"),
        }
    }
}

pub type Subst = HashMap<String, CelType>;

/// Can a value of type `arg` be passed where `param` is expected? Binds
/// type parameters in `s` as a side effect (only on success).
pub fn assignable(param: &CelType, arg: &CelType, s: &mut Subst) -> bool {
    let mut trial = s.clone();
    if unify(param, arg, &mut trial) {
        *s = trial;
        true
    } else {
        false
    }
}

fn unify(param: &CelType, arg: &CelType, s: &mut Subst) -> bool {
    use CelType::*;
    let param = param.substitute(s);
    let arg = arg.substitute(s);
    match (&param, &arg) {
        (Error, _) | (_, Error) | (Dyn, _) | (_, Dyn) => true,
        (Param(a), Param(b)) if a == b => true,
        (Param(p), t) | (t, Param(p)) => {
            if occurs(p, t) {
                return false;
            }
            s.insert(p.clone(), t.clone());
            true
        }
        (List(a), List(b)) => unify(a, b, s),
        (Map(k1, v1), Map(k2, v2)) => unify(k1, k2, s) && unify(v1, v2, s),
        // wrapper semantics: T? flows into T (null becomes a runtime error) and back
        (Nullable(a), Nullable(b)) => unify(a, b, s),
        (Nullable(_), Null) | (Null, Nullable(_)) => true,
        (Nullable(a), b) | (b, Nullable(a)) => unify(a, b, s),
        (a, b) => a == b,
    }
}

fn occurs(p: &str, t: &CelType) -> bool {
    match t {
        CelType::Param(q) => p == q,
        CelType::List(e) | CelType::Nullable(e) => occurs(p, e),
        CelType::Map(k, v) => occurs(p, k) || occurs(p, v),
        _ => false,
    }
}

/// Least common type for list/map literal elements and conditionals.
pub fn join(a: &CelType, b: &CelType, s: &mut Subst) -> CelType {
    if assignable(a, b, s) {
        let a2 = a.substitute(s);
        let b2 = b.substitute(s);
        // prefer the nullable side so that `cond ? x : null` is `T?`
        match (&a2, &b2) {
            (CelType::Null, t) | (t, CelType::Null) => CelType::nullable(t.clone()),
            (CelType::Nullable(_), _) => a2,
            (_, CelType::Nullable(_)) => b2,
            (CelType::Dyn, _) | (CelType::Error, _) => b2,
            _ => a2,
        }
    } else {
        CelType::Dyn
    }
}
