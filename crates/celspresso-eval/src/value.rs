use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::fmt;
use std::sync::Arc;

/// Runtime CEL values.
#[derive(Clone, Debug)]
pub enum Value {
    Null,
    Bool(bool),
    Int(i64),
    Uint(u64),
    Double(f64),
    String(Arc<str>),
    Bytes(Arc<[u8]>),
    /// Days since 1970-01-01.
    Date(i64),
    List(Arc<Vec<Value>>),
    Map(Arc<BTreeMap<Key, Value>>),
    Struct(Arc<StructValue>),
}

#[derive(Clone, Debug)]
pub struct StructValue {
    pub type_name: String,
    pub fields: BTreeMap<String, Value>,
}

/// Map keys. Numeric keys compare across int/uint, as the spec requires.
#[derive(Clone, Debug)]
pub enum Key {
    Bool(bool),
    Int(i64),
    Uint(u64),
    String(Arc<str>),
}

impl Key {
    fn rank(&self) -> (u8, i128) {
        match self {
            Key::Bool(b) => (0, *b as i128),
            Key::Int(i) => (1, *i as i128),
            Key::Uint(u) => (1, *u as i128),
            Key::String(_) => (2, 0),
        }
    }
    pub fn from_value(v: &Value) -> Option<Key> {
        Some(match v {
            Value::Bool(b) => Key::Bool(*b),
            Value::Int(i) => Key::Int(*i),
            Value::Uint(u) => Key::Uint(*u),
            Value::String(s) => Key::String(s.clone()),
            Value::Double(d) if d.fract() == 0.0 && *d >= i64::MIN as f64 && *d < i64::MAX as f64 => Key::Int(*d as i64),
            _ => return None,
        })
    }
    pub fn to_value(&self) -> Value {
        match self {
            Key::Bool(b) => Value::Bool(*b),
            Key::Int(i) => Value::Int(*i),
            Key::Uint(u) => Value::Uint(*u),
            Key::String(s) => Value::String(s.clone()),
        }
    }
}

impl PartialEq for Key {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}
impl Eq for Key {}
impl PartialOrd for Key {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for Key {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (Key::String(a), Key::String(b)) => a.cmp(b),
            _ => self.rank().cmp(&other.rank()),
        }
    }
}

impl Value {
    pub fn str(s: &str) -> Value {
        Value::String(Arc::from(s))
    }
    pub fn list(items: Vec<Value>) -> Value {
        Value::List(Arc::new(items))
    }
    pub fn type_name(&self) -> String {
        match self {
            Value::Null => "null_type".into(),
            Value::Bool(_) => "bool".into(),
            Value::Int(_) => "int".into(),
            Value::Uint(_) => "uint".into(),
            Value::Double(_) => "double".into(),
            Value::String(_) => "string".into(),
            Value::Bytes(_) => "bytes".into(),
            Value::Date(_) => "date".into(),
            Value::List(_) => "list".into(),
            Value::Map(_) => "map".into(),
            Value::Struct(s) => s.type_name.clone(),
        }
    }

    /// CEL heterogeneous equality. Returns `None` never; different kinds are unequal.
    pub fn cel_eq(&self, other: &Value) -> bool {
        use Value::*;
        match (self, other) {
            (Null, Null) => true,
            (Bool(a), Bool(b)) => a == b,
            (String(a), String(b)) => a == b,
            (Bytes(a), Bytes(b)) => a == b,
            (Date(a), Date(b)) => a == b,
            (Int(_) | Uint(_) | Double(_), Int(_) | Uint(_) | Double(_)) => {
                numeric_cmp(self, other) == Some(Ordering::Equal)
            }
            (List(a), List(b)) => a.len() == b.len() && a.iter().zip(b.iter()).all(|(x, y)| x.cel_eq(y)),
            (Map(a), Map(b)) => {
                a.len() == b.len() && a.iter().all(|(k, v)| b.get(k).is_some_and(|w| v.cel_eq(w)))
            }
            (Struct(a), Struct(b)) => {
                a.type_name == b.type_name
                    && a.fields.len() == b.fields.len()
                    && a.fields.iter().all(|(k, v)| b.fields.get(k).is_some_and(|w| v.cel_eq(w)))
            }
            _ => false,
        }
    }
}

/// Ordering across int/uint/double.
pub fn numeric_cmp(a: &Value, b: &Value) -> Option<Ordering> {
    use Value::*;
    match (a, b) {
        (Int(x), Int(y)) => Some(x.cmp(y)),
        (Uint(x), Uint(y)) => Some(x.cmp(y)),
        (Int(x), Uint(y)) => Some((*x as i128).cmp(&(*y as i128))),
        (Uint(x), Int(y)) => Some((*x as i128).cmp(&(*y as i128))),
        (Double(x), Double(y)) => x.partial_cmp(y),
        (Double(x), Int(y)) => cmp_f64_i128(*x, *y as i128),
        (Double(x), Uint(y)) => cmp_f64_i128(*x, *y as i128),
        (Int(x), Double(y)) => cmp_f64_i128(*y, *x as i128).map(Ordering::reverse),
        (Uint(x), Double(y)) => cmp_f64_i128(*y, *x as i128).map(Ordering::reverse),
        _ => None,
    }
}

fn cmp_f64_i128(x: f64, y: i128) -> Option<Ordering> {
    if x.is_nan() {
        return None;
    }
    if x < -1.8e19 {
        return Some(Ordering::Less);
    }
    if x > 1.8e19 {
        return Some(Ordering::Greater);
    }
    let t = x.trunc() as i128;
    Some(match t.cmp(&y) {
        Ordering::Equal => x.fract().partial_cmp(&0.0).unwrap(),
        o => o,
    })
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Null => write!(f, "null"),
            Value::Bool(b) => write!(f, "{b}"),
            Value::Int(i) => write!(f, "{i}"),
            Value::Uint(u) => write!(f, "{u}u"),
            Value::Double(d) => write!(f, "{d:?}"),
            Value::String(s) => write!(f, "{}", celspresso_syntax::ast::quote_string(s)),
            Value::Bytes(b) => write!(f, "b{:?}", String::from_utf8_lossy(b)),
            Value::Date(d) => write!(f, "date(\"{}\")", crate::date::format_date(*d)),
            Value::List(items) => {
                write!(f, "[")?;
                for (i, v) in items.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{v}")?;
                }
                write!(f, "]")
            }
            Value::Map(m) => {
                write!(f, "{{")?;
                for (i, (k, v)) in m.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}: {v}", k.to_value())?;
                }
                write!(f, "}}")
            }
            Value::Struct(s) => {
                write!(f, "{}{{", s.type_name)?;
                for (i, (k, v)) in s.fields.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{k}: {v}")?;
                }
                write!(f, "}}")
            }
        }
    }
}

impl PartialEq for Value {
    /// Structural CEL equality (heterogeneous numerics compare by value).
    fn eq(&self, other: &Self) -> bool {
        self.cel_eq(other)
    }
}
