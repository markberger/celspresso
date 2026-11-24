//! Schema constraints at runtime.
//!
//! The verifier assumes every input satisfies its schema's constraints (`ge`, `le`,
//! `max_length`, `Literal`, `pattern`, ...), so a proof only covers inputs that do. This
//! module checks the same constraints on concrete inputs, so evaluation never runs a
//! rule on data its proofs don't cover. Messages name the path and the constraint, never
//! the value (inputs may hold PHI).

use crate::value::{Key, Value};
use celspresso_check::{CelType, Constraints, Schema};
use celspresso_syntax::Literal;
use std::cell::RefCell;
use std::collections::HashMap;

/// Check `v` (of type `ty`, found at `path`) and everything inside it against the schema.
pub fn validate(v: &Value, ty: &CelType, cons: &Constraints, schema: &Schema, path: &str) -> Result<(), String> {
    if matches!(v, Value::Null) {
        return Ok(());
    }
    check(v, cons).map_err(|why| format!("input '{path}' violates the schema: {why}"))?;
    let ty = match ty {
        CelType::Nullable(inner) => inner,
        t => t,
    };
    let none = Constraints::default();
    match (v, ty) {
        (Value::List(items), CelType::List(elem)) => {
            let ic = cons.items.as_deref().unwrap_or(&none);
            for (i, x) in items.iter().enumerate() {
                validate(x, elem, ic, schema, &format!("{path}[{i}]"))?;
            }
        }
        (Value::Map(m), CelType::Map(kt, vt)) => {
            let ic = cons.items.as_deref().unwrap_or(&none);
            let kc = cons.keys.as_deref().unwrap_or(&none);
            for (k, x) in m.iter() {
                validate(&k.to_value(), kt, kc, schema, &format!("{path} key {}", key_label(k)))?;
                validate(x, vt, ic, schema, &format!("{path}[{}]", key_label(k)))?;
            }
        }
        (Value::Struct(s), CelType::Struct(name)) => {
            if let Some(sd) = schema.structs.get(name) {
                for f in &sd.fields {
                    if let Some(x) = s.fields.get(&f.name) {
                        validate(x, &f.ty, &f.constraints, schema, &format!("{path}.{}", f.name))?;
                    }
                }
            }
        }
        _ => {}
    }
    Ok(())
}

/// Map keys in paths: strings quoted, other scalars as written (no free-form values).
fn key_label(k: &Key) -> String {
    match k {
        Key::String(s) => format!("{s:?}"),
        Key::Int(i) => i.to_string(),
        Key::Uint(u) => format!("{u}u"),
        Key::Bool(b) => b.to_string(),
    }
}

fn check(v: &Value, c: &Constraints) -> Result<(), String> {
    if c.is_empty() {
        return Ok(());
    }
    let num = match v {
        Value::Int(i) => Some(*i as f64),
        Value::Uint(u) => Some(*u as f64),
        Value::Double(d) => Some(*d),
        _ => None,
    };
    if let Some(x) = num {
        use std::cmp::Ordering::{Greater, Less};
        if let Some(b) = c.ge {
            if order(v, x, b, f64::ceil).is_none_or(|o| o == Less) {
                return Err(format!("must be >= {b}"));
            }
        }
        if let Some(b) = c.gt {
            if order(v, x, b, f64::floor) != Some(Greater) {
                return Err(format!("must be > {b}"));
            }
        }
        if let Some(b) = c.le {
            if order(v, x, b, f64::floor).is_none_or(|o| o == Greater) {
                return Err(format!("must be <= {b}"));
            }
        }
        if let Some(b) = c.lt {
            if order(v, x, b, f64::ceil) != Some(Less) {
                return Err(format!("must be < {b}"));
            }
        }
    }
    let len = match v {
        Value::String(s) => Some(s.chars().count() as u64),
        Value::Bytes(b) => Some(b.len() as u64),
        Value::List(l) => Some(l.len() as u64),
        Value::Map(m) => Some(m.len() as u64),
        _ => None,
    };
    if let Some(n) = len {
        if let Some(m) = c.min_length {
            if n < m {
                return Err(format!("length must be >= {m}"));
            }
        }
        if let Some(m) = c.max_length {
            if n > m {
                return Err(format!("length must be <= {m}"));
            }
        }
    }
    if let Some(opts) = &c.one_of {
        if !opts.iter().any(|l| literal_eq(l, v)) {
            return Err(format!("must be one of {}", opts.iter().map(literal_text).collect::<Vec<_>>().join(", ")));
        }
    }
    if let (Some(p), Value::String(s)) = (&c.pattern, v) {
        if !pattern_matches(p, s)? {
            return Err(format!("must match pattern {p:?}"));
        }
    }
    Ok(())
}

/// Compare a number with a bound: ints exactly (against the bound rounded the way that
/// keeps the comparison equivalent), doubles in IEEE order (NaN compares as nothing).
fn order(v: &Value, x: f64, bound: f64, round: fn(f64) -> f64) -> Option<std::cmp::Ordering> {
    match v {
        Value::Int(i) => Some((*i as i128).cmp(&(round(bound) as i128))),
        Value::Uint(u) => Some((*u as i128).cmp(&(round(bound) as i128))),
        _ => x.partial_cmp(&bound),
    }
}

fn literal_eq(l: &Literal, v: &Value) -> bool {
    match (l, v) {
        (Literal::String(a), Value::String(b)) => a.as_str() == &**b,
        (Literal::Int(a), Value::Int(b)) => a == b,
        (Literal::Int(a), Value::Uint(b)) => *a >= 0 && *a as u64 == *b,
        (Literal::Uint(a), Value::Uint(b)) => a == b,
        (Literal::Uint(a), Value::Int(b)) => *b >= 0 && *b as u64 == *a,
        (Literal::Double(a), Value::Double(b)) => a == b,
        (Literal::Bool(a), Value::Bool(b)) => a == b,
        _ => false,
    }
}

fn literal_text(l: &Literal) -> String {
    match l {
        Literal::String(s) => format!("{s:?}"),
        Literal::Int(i) => i.to_string(),
        Literal::Uint(u) => format!("{u}u"),
        Literal::Double(d) => d.to_string(),
        Literal::Bool(b) => b.to_string(),
        other => format!("{other:?}"),
    }
}

thread_local! {
    static PATTERNS: RefCell<HashMap<String, regex::Regex>> = RefCell::new(HashMap::new());
}

/// Why `pattern` can't be used as a schema pattern, if it can't.
pub fn pattern_error(pattern: &str) -> Option<String> {
    regex::Regex::new(pattern).err().map(|e| format!("invalid pattern {pattern:?}: {e}"))
}

/// Pydantic-style `pattern`: an unanchored search, compiled once per thread.
fn pattern_matches(pattern: &str, s: &str) -> Result<bool, String> {
    PATTERNS.with(|cache| {
        let mut cache = cache.borrow_mut();
        if !cache.contains_key(pattern) {
            let re = regex::Regex::new(pattern).map_err(|e| format!("invalid pattern {pattern:?}: {e}"))?;
            cache.insert(pattern.to_string(), re);
        }
        Ok(cache[pattern].is_match(s))
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use celspresso_check::{FieldDecl, StructDecl};

    fn cons(f: impl FnOnce(&mut Constraints)) -> Constraints {
        let mut c = Constraints::default();
        f(&mut c);
        c
    }

    #[test]
    fn scalars() {
        let s = Schema::default();
        let le10 = cons(|c| c.le = Some(10.0));
        assert!(validate(&Value::Int(10), &CelType::Int, &le10, &s, "x").is_ok());
        let e = validate(&Value::Int(11), &CelType::Int, &le10, &s, "x").unwrap_err();
        assert_eq!(e, "input 'x' violates the schema: must be <= 10");
        let gt0 = cons(|c| c.gt = Some(0.0));
        assert!(validate(&Value::Double(f64::NAN), &CelType::Double, &gt0, &s, "d").is_err());
        assert!(validate(&Value::Uint(0), &CelType::Uint, &gt0, &s, "u").is_err());
        // exact beyond 2^53: i64::MAX is not <= 2^63 - 1025 even though both round to 2^63
        let big = cons(|c| c.le = Some(9_223_372_036_854_774_784.0));
        assert!(validate(&Value::Int(i64::MAX), &CelType::Int, &big, &s, "x").is_err());
        let tier = cons(|c| c.one_of = Some(vec![Literal::String("free".into()), Literal::String("pro".into())]));
        assert!(validate(&Value::str("pro"), &CelType::String, &tier, &s, "t").is_ok());
        let e = validate(&Value::str("gold"), &CelType::String, &tier, &s, "t").unwrap_err();
        assert!(e.ends_with("must be one of \"free\", \"pro\"") && !e.contains("gold"), "{e}");
        let zip = cons(|c| {
            c.pattern = Some(r"^\d{5}$".into());
            c.max_length = Some(5)
        });
        assert!(validate(&Value::str("94110"), &CelType::String, &zip, &s, "z").is_ok());
        assert!(validate(&Value::str("9411"), &CelType::String, &zip, &s, "z").is_err());
        assert!(validate(&Value::str("941101"), &CelType::String, &zip, &s, "z").unwrap_err().contains("length"));
        let bad = cons(|c| c.pattern = Some("(".into()));
        assert!(validate(&Value::str("x"), &CelType::String, &bad, &s, "z").unwrap_err().contains("invalid pattern"));
        let two = cons(|c| c.min_length = Some(2));
        assert!(validate(&Value::Bytes(std::sync::Arc::from(&b"a"[..])), &CelType::Bytes, &two, &s, "b").is_err());
        let one_int = cons(|c| c.one_of = Some(vec![Literal::Int(1), Literal::Uint(2)]));
        assert!(validate(&Value::Uint(1), &CelType::Uint, &one_int, &s, "n").is_ok());
        assert!(validate(&Value::Int(2), &CelType::Int, &one_int, &s, "n").is_ok());
        assert!(validate(&Value::Int(3), &CelType::Int, &one_int, &s, "n").is_err());
        // null satisfies anything (Optional fields)
        assert!(validate(&Value::Null, &CelType::nullable(CelType::Int), &le10, &s, "x").is_ok());
    }

    #[test]
    fn nested() {
        let mut s = Schema::default();
        s.structs.insert(
            "M".into(),
            StructDecl {
                name: "M".into(),
                fields: vec![FieldDecl { name: "age".into(), ty: CelType::Int, constraints: cons(|c| c.ge = Some(0.0)) }],
            },
        );
        let m = |age: i64| {
            let mut fields = std::collections::BTreeMap::new();
            fields.insert("age".to_string(), Value::Int(age));
            Value::Struct(std::sync::Arc::new(crate::StructValue { type_name: "M".into(), fields }))
        };
        let ty = CelType::list(CelType::Struct("M".into()));
        let items = cons(|c| c.max_length = Some(2));
        assert!(validate(&Value::list(vec![m(1), m(2)]), &ty, &items, &s, "ms").is_ok());
        let e = validate(&Value::list(vec![m(1), m(-1)]), &ty, &items, &s, "ms").unwrap_err();
        assert_eq!(e, "input 'ms[1].age' violates the schema: must be >= 0");
        assert!(validate(&Value::list(vec![m(1), m(2), m(3)]), &ty, &items, &s, "ms").is_err());
        let each = cons(|c| c.items = Some(Box::new(cons(|c| c.le = Some(5.0)))));
        let e = validate(&Value::list(vec![Value::Int(1), Value::Int(6)]), &CelType::list(CelType::Int), &each, &s, "xs").unwrap_err();
        assert_eq!(e, "input 'xs[1]' violates the schema: must be <= 5");
        let mut map = std::collections::BTreeMap::new();
        map.insert(Key::String("k".into()), m(-5));
        let e = validate(
            &Value::Map(std::sync::Arc::new(map)),
            &CelType::map(CelType::String, CelType::Struct("M".into())),
            &Constraints::default(),
            &s,
            "mm",
        )
        .unwrap_err();
        assert_eq!(e, "input 'mm[\"k\"].age' violates the schema: must be >= 0");
    }
}
