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
    /// `google.protobuf.Timestamp`: an instant with nanosecond precision.
    Timestamp,
    /// `google.protobuf.Duration`: a signed span with nanosecond precision.
    Duration,
    /// The type of a type value: `type(1)` is `type(int)`, `int` is `type(int)`.
    Type(Box<CelType>),
    List(Box<CelType>),
    Map(Box<CelType>, Box<CelType>),
    /// A named record type declared in the environment schema.
    Struct(String),
    /// `T` or `null` (Pydantic `T | None`, proto wrapper types).
    Nullable(Box<CelType>),
    /// `optional_type(T)`: a value that may be absent (`optional.of(x)`, `m.?key`).
    Optional(Box<CelType>),
    /// An extension type with no fields, known only by name (`net.IP`, `net.CIDR`).
    Opaque(String),
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
            // optionals already admit null
            CelType::Nullable(_) | CelType::Optional(_) | CelType::Null | CelType::Dyn => t,
            t => CelType::Nullable(Box::new(t)),
        }
    }
    pub fn optional(t: CelType) -> CelType {
        CelType::Optional(Box::new(t))
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
            CelType::Type(t) => CelType::Type(Box::new(t.substitute(s))),
            CelType::Optional(t) => CelType::optional(t.substitute(s)),
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
            CelType::Type(t) => CelType::Type(Box::new(t.finalize(s))),
            CelType::Optional(t) => CelType::optional(t.finalize(s)),
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
            CelType::Timestamp => write!(f, "google.protobuf.Timestamp"),
            CelType::Duration => write!(f, "google.protobuf.Duration"),
            CelType::Type(t) => write!(f, "type({t})"),
            CelType::List(e) => write!(f, "list({e})"),
            CelType::Map(k, v) => write!(f, "map({k}, {v})"),
            CelType::Struct(n) => write!(f, "{n}"),
            CelType::Nullable(t) => write!(f, "{t}?"),
            CelType::Optional(t) => write!(f, "optional_type({t})"),
            CelType::Opaque(n) => write!(f, "{n}"),
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
    // every type value has kind `type`, so a parameter bound to type(int) that meets
    // type(uint) widens ("decays") to type(dyn) instead of failing; likewise nested
    if let (Param(p), Some(bound)) = (param, s.get(param_name(param)).cloned()) {
        let arg = arg.substitute(s);
        let mut trial = s.clone();
        if !unify(&bound, &arg, &mut trial) {
            if let Some(wide) = decay(&bound.substitute(s), &arg) {
                s.insert(p.clone(), wide);
                return true;
            }
        }
    }
    // resolve only the outermost parameter, so nested parameters reach the check above
    let param = shallow(param, s);
    let arg = shallow(arg, s);
    match (&param, &arg) {
        (Error, _) | (_, Error) => true,
        (Param(a), Param(b)) if a == b => true,
        // a parameter meeting dyn binds to dyn, so later uses widen rather than narrow
        (Param(p), t) | (t, Param(p)) => {
            if occurs(p, &t.substitute(s)) {
                return false;
            }
            s.insert(p.clone(), t.clone());
            true
        }
        (Dyn, _) | (_, Dyn) => true,
        (List(a), List(b)) | (Type(a), Type(b)) | (Optional(a), Optional(b)) => unify(a, b, s),
        (Map(k1, v1), Map(k2, v2)) => unify(k1, k2, s) && unify(v1, v2, s),
        // wrapper semantics: T? flows into T (null becomes a runtime error) and back
        (Nullable(a), Nullable(b)) => unify(a, b, s),
        (Nullable(_), Null) | (Null, Nullable(_)) | (Optional(_), Null) | (Null, Optional(_)) => true,
        (Nullable(a), b) | (b, Nullable(a)) => unify(a, b, s),
        (a, b) => a.substitute(s) == b.substitute(s),
    }
}

fn shallow(t: &CelType, s: &Subst) -> CelType {
    let mut t = t.clone();
    while let CelType::Param(p) = &t {
        match s.get(p) {
            Some(next) => t = next.clone(),
            None => break,
        }
    }
    t
}

/// The more general of two mutually assignable types: dyn wins at every position.
fn generalize(a: &CelType, b: &CelType) -> CelType {
    use CelType::*;
    match (a, b) {
        (Dyn, _) | (_, Dyn) => Dyn,
        (List(x), List(y)) => CelType::list(generalize(x, y)),
        (Optional(x), Optional(y)) => CelType::optional(generalize(x, y)),
        (Type(x), Type(y)) => Type(Box::new(generalize(x, y))),
        (Map(k1, v1), Map(k2, v2)) => CelType::map(generalize(k1, k2), generalize(v1, v2)),
        _ => a.clone(),
    }
}

fn param_name(t: &CelType) -> &str {
    match t {
        CelType::Param(p) => p,
        _ => "",
    }
}

/// The common supertype of two types that differ only inside type values,
/// e.g. `list(type(int))` and `list(type(uint))` give `list(type(dyn))`.
fn decay(a: &CelType, b: &CelType) -> Option<CelType> {
    use CelType::*;
    match (a, b) {
        (Type(_), Type(_)) => Some(if a == b { a.clone() } else { Type(Box::new(Dyn)) }),
        (List(x), List(y)) => Some(CelType::list(decay(x, y)?)),
        (Optional(x), Optional(y)) => Some(CelType::optional(decay(x, y)?)),
        (Map(k1, v1), Map(k2, v2)) => Some(CelType::map(decay(k1, k2)?, decay(v1, v2)?)),
        (x, y) if x == y => Some(x.clone()),
        _ => None,
    }
}

fn occurs(p: &str, t: &CelType) -> bool {
    match t {
        CelType::Param(q) => p == q,
        CelType::List(e) | CelType::Nullable(e) | CelType::Type(e) | CelType::Optional(e) => occurs(p, e),
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
            // once a literal is heterogeneous it stays dyn: [1, 'a', 2] is list(dyn)
            (CelType::Dyn, _) => a2,
            (CelType::Error, _) => b2,
            // [optional.of(1), optional.of(dyn(1))] is list(optional_type(dyn))
            _ => generalize(&a2, &b2),
        }
    } else {
        // [int, bool] is list(type(dyn)), not list(dyn)
        decay(&a.substitute(s), &b.substitute(s)).unwrap_or(CelType::Dyn)
    }
}
