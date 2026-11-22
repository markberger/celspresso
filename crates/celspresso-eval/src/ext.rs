//! Runtime implementations of cel-go's extension libraries (strings, math, lists,
//! sets, encoders). String positions are in code points, as in cel-go.

use crate::net::{self, Net as N};
use crate::time;
use crate::value::{numeric_cmp, Key, Value};
use std::cmp::Ordering;
use std::sync::Arc;

/// Outcome of an extension call: `None` when no overload accepts these arguments.
pub type ExtResult = Option<Result<Value, String>>;

pub fn call(function: &str, args: &[Value]) -> ExtResult {
    use Value::*;
    let ok = |v: Value| Some(Ok(v));
    let fail = |m: std::string::String| Some(Err(m));
    match (function, args) {
        // ------------------------------------------------------------ optionals
        ("optional.of", [x]) => ok(Optional(Some(Arc::new(x.clone())))),
        ("optional.ofNonZeroValue", [x]) => ok(Optional((!is_zero(x)).then(|| Arc::new(x.clone())))),
        ("optional.none", []) => ok(Optional(None)),
        ("hasValue", [Optional(o)]) => ok(Bool(o.is_some())),
        ("value", [Optional(Some(x))]) => ok(x.as_ref().clone()),
        ("value", [Optional(None)]) => fail("optional.none() dereference".into()),
        ("or", [Optional(a), Optional(b)]) => ok(Optional(a.clone().or_else(|| b.clone()))),
        ("orValue", [Optional(a), x]) => ok(a.as_ref().map_or_else(|| x.clone(), |v| v.as_ref().clone())),

        // ------------------------------------------------------------ network
        ("ip", [String(s)]) => Some(net::parse_ip(s).map(|a| netv(N::Ip(a)))),
        ("cidr", [String(s)]) => Some(net::parse_cidr(s).map(netv)),
        ("isIP", [String(s)]) => ok(Bool(net::parse_ip(s).is_ok())),
        ("isCIDR", [String(s)]) => ok(Bool(net::parse_cidr(s).is_ok())),
        ("ip.isCanonical", [String(s)]) => Some(net::is_canonical(s).map(Bool)),
        ("string", [Value::Net(n)]) => ok(str(n.to_string())),
        (f, [Value::Net(n), rest @ ..]) => match (f, n.as_ref(), rest) {
            ("family", N::Ip(a), []) => ok(Int(if a.is_ipv4() { 4 } else { 6 })),
            ("isUnspecified", N::Ip(a), []) => ok(Bool(a.is_unspecified())),
            ("isLoopback", N::Ip(a), []) => ok(Bool(a.is_loopback())),
            ("isGlobalUnicast", N::Ip(a), []) => ok(Bool(net::is_global_unicast(a))),
            ("isLinkLocalMulticast", N::Ip(a), []) => ok(Bool(net::is_link_local_multicast(a))),
            ("isLinkLocalUnicast", N::Ip(a), []) => ok(Bool(net::is_link_local_unicast(a))),
            ("ip", N::Cidr(a, _), []) => ok(netv(N::Ip(*a))),
            ("masked", N::Cidr(a, n), []) => ok(netv(N::Cidr(net::masked(a, *n), *n))),
            ("prefixLength", N::Cidr(_, n), []) => ok(Int(i64::from(*n))),
            ("containsIP", N::Cidr(a, n), [x]) => {
                let ip = match x {
                    String(s) => match net::parse_ip(s) {
                        Ok(ip) => ip,
                        Err(m) => return fail(m),
                    },
                    Value::Net(o) => match o.as_ref() {
                        N::Ip(ip) => *ip,
                        N::Cidr(..) => return None,
                    },
                    _ => return None,
                };
                ok(Bool(net::contains_ip(a, *n, &ip)))
            }
            ("containsCIDR", N::Cidr(a, n), [x]) => {
                let other = match x {
                    String(s) => match net::parse_cidr(s) {
                        Ok(c) => c,
                        Err(m) => return fail(m),
                    },
                    Value::Net(o) => o.as_ref().clone(),
                    _ => return None,
                };
                match other {
                    N::Cidr(b, m) => ok(Bool(net::contains_cidr(a, *n, &b, m))),
                    N::Ip(_) => None,
                }
            }
            _ => None,
        },

        // ------------------------------------------------------------ math
        ("math.greatest" | "math.least", args) => {
            let items: &[Value] = match args {
                [List(l)] => l.as_slice(),
                xs => xs,
            };
            if items.is_empty() {
                return fail(format!("{function}(): list must not be empty"));
            }
            let mut best = &items[0];
            for x in items {
                let o = numeric_cmp(x, best)?;
                if (function == "math.greatest" && o.is_gt()) || (function == "math.least" && o.is_lt()) {
                    best = x;
                }
            }
            numeric_cmp(best, best)?; // the single-element case must still be numeric
            ok(best.clone())
        }
        ("math.ceil", [Double(d)]) => ok(Double(d.ceil())),
        ("math.floor", [Double(d)]) => ok(Double(d.floor())),
        ("math.round", [Double(d)]) => ok(Double(d.round())),
        ("math.trunc", [Double(d)]) => ok(Double(d.trunc())),
        ("math.isNaN", [Double(d)]) => ok(Bool(d.is_nan())),
        ("math.isInf", [Double(d)]) => ok(Bool(d.is_infinite())),
        ("math.isFinite", [Double(d)]) => ok(Bool(d.is_finite())),
        ("math.abs", [Int(i)]) => Some(i.checked_abs().map(Int).ok_or_else(|| "integer overflow".to_string())),
        ("math.abs", [Uint(u)]) => ok(Uint(*u)),
        ("math.abs", [Double(d)]) => ok(Double(d.abs())),
        ("math.sign", [Int(i)]) => ok(Int(i.signum())),
        ("math.sign", [Uint(u)]) => ok(Uint(u64::from(*u > 0))),
        ("math.sign", [Double(d)]) => ok(Double(if d.is_nan() || *d == 0.0 { *d } else { d.signum() })),
        ("math.bitAnd", [Int(a), Int(b)]) => ok(Int(a & b)),
        ("math.bitAnd", [Uint(a), Uint(b)]) => ok(Uint(a & b)),
        ("math.bitOr", [Int(a), Int(b)]) => ok(Int(a | b)),
        ("math.bitOr", [Uint(a), Uint(b)]) => ok(Uint(a | b)),
        ("math.bitXor", [Int(a), Int(b)]) => ok(Int(a ^ b)),
        ("math.bitXor", [Uint(a), Uint(b)]) => ok(Uint(a ^ b)),
        ("math.bitNot", [Int(a)]) => ok(Int(!a)),
        ("math.bitNot", [Uint(a)]) => ok(Uint(!a)),
        ("math.bitShiftLeft" | "math.bitShiftRight", [x, Int(n)]) if matches!(x, Int(_) | Uint(_)) => {
            if *n < 0 {
                return fail(format!("{function}() negative offset: {n}"));
            }
            let bits = match x {
                Int(i) => *i as u64,
                Uint(u) => *u,
                _ => unreachable!(),
            };
            // shifts of 64 or more clear every bit; right shifts are logical
            let out = match (*n >= 64, function == "math.bitShiftLeft") {
                (true, _) => 0,
                (false, true) => bits << n,
                (false, false) => bits >> n,
            };
            ok(if matches!(x, Int(_)) { Int(out as i64) } else { Uint(out) })
        }

        // ------------------------------------------------------------ strings
        ("charAt", [String(s), Int(i)]) => {
            let chars: Vec<char> = s.chars().collect();
            match usize::try_from(*i) {
                Ok(i) if i < chars.len() => ok(str(chars[i].to_string())),
                Ok(i) if i == chars.len() => ok(str(std::string::String::new())),
                _ => fail(format!("index out of range: {i}")),
            }
        }
        ("indexOf", [String(s), String(sub), rest @ ..]) if rest.len() <= 1 => {
            let chars: Vec<char> = s.chars().collect();
            let needle: Vec<char> = sub.chars().collect();
            let start = match rest {
                [Int(o)] => match usize::try_from(*o) {
                    Ok(o) if o <= chars.len() => o,
                    _ => return fail(format!("index out of range: {o}")),
                },
                [] => 0,
                _ => return None,
            };
            let found = (start..=chars.len().saturating_sub(needle.len()))
                .find(|&i| i + needle.len() <= chars.len() && chars[i..i + needle.len()] == needle[..]);
            ok(Int(found.map_or(-1, |i| i as i64)))
        }
        ("lastIndexOf", [String(s), String(sub), rest @ ..]) if rest.len() <= 1 => {
            let chars: Vec<char> = s.chars().collect();
            let needle: Vec<char> = sub.chars().collect();
            let last = match rest {
                [Int(o)] => match usize::try_from(*o) {
                    Ok(o) if o <= chars.len() => o,
                    _ => return fail(format!("index out of range: {o}")),
                },
                [] => chars.len(),
                _ => return None,
            };
            if needle.len() > chars.len() {
                return ok(Int(-1));
            }
            let top = last.min(chars.len() - needle.len());
            let found = (0..=top).rev().find(|&i| chars[i..i + needle.len()] == needle[..]);
            ok(Int(found.map_or(-1, |i| i as i64)))
        }
        ("substring", [String(s), Int(start), rest @ ..]) if rest.len() <= 1 => {
            let chars: Vec<char> = s.chars().collect();
            let end = match rest {
                [Int(e)] => *e,
                [] => chars.len() as i64,
                _ => return None,
            };
            if *start < 0 || *start as usize > chars.len() {
                return fail(format!("index out of range: {start}"));
            }
            if end < 0 || end as usize > chars.len() {
                return fail(format!("index out of range: {end}"));
            }
            if *start > end {
                return fail(format!("invalid substring range. start: {start}, end: {end}"));
            }
            ok(str(chars[*start as usize..end as usize].iter().collect()))
        }
        ("replace", [String(s), String(from), String(to), rest @ ..]) if rest.len() <= 1 => {
            let n = match rest {
                [Int(n)] => *n,
                [] => -1,
                _ => return None,
            };
            ok(str(match usize::try_from(n) {
                Ok(n) => s.replacen(from.as_ref(), to, n),
                Err(_) => s.replace(from.as_ref(), to),
            }))
        }
        ("split", [String(s), String(sep), rest @ ..]) if rest.len() <= 1 => {
            let n = match rest {
                [Int(n)] => *n,
                [] => -1,
                _ => return None,
            };
            if n == 0 {
                return ok(Value::list(vec![]));
            }
            let parts: Vec<std::string::String> = if sep.is_empty() {
                let chars: Vec<char> = s.chars().collect();
                let limit = usize::try_from(n).unwrap_or(usize::MAX).min(chars.len());
                let mut out: Vec<std::string::String> = chars.iter().take(limit.saturating_sub(1)).map(|c| c.to_string()).collect();
                if limit > 0 {
                    out.push(chars[limit - 1..].iter().collect());
                }
                out
            } else {
                match usize::try_from(n) {
                    Ok(n) => s.splitn(n, sep.as_ref()).map(str::to_string).collect(),
                    Err(_) => s.split(sep.as_ref()).map(str::to_string).collect(),
                }
            };
            ok(Value::list(parts.into_iter().map(str).collect()))
        }
        ("join", [List(l), rest @ ..]) if rest.len() <= 1 => {
            let sep = match rest {
                [String(s)] => s.as_ref(),
                [] => "",
                _ => return None,
            };
            let mut parts = Vec::with_capacity(l.len());
            for x in l.iter() {
                match x {
                    String(s) => parts.push(s.as_ref()),
                    other => return fail(format!("join: list element is {}, not string", other.type_name())),
                }
            }
            ok(str(parts.join(sep)))
        }
        ("reverse", [String(s)]) => ok(str(s.chars().rev().collect())),
        ("reverse", [List(l)]) => ok(Value::list(l.iter().rev().cloned().collect())),
        ("strings.quote", [String(s)]) => ok(str(quote(s))),
        ("format", [String(f), List(l)]) => Some(format(f, l)),

        // ------------------------------------------------------------ lists
        ("sort", [List(l)]) => Some(sorted(l, l).map(Value::list)),
        ("@sortByAssociatedKeys", [List(l), List(keys)]) => {
            if l.len() != keys.len() {
                return fail("sortBy: key list length differs from list length".into());
            }
            Some(sorted(l, keys).map(Value::list))
        }
        ("slice", [List(l), Int(a), Int(b)]) => {
            if *a < 0 || *b < 0 {
                return fail(format!("cannot slice({a}, {b}), negative indexes not supported"));
            }
            if a > b {
                return fail(format!("cannot slice({a}, {b}), start index must be less than or equal to end index"));
            }
            if *b as usize > l.len() {
                return fail(format!("cannot slice({a}, {b}), list is length {}", l.len()));
            }
            ok(Value::list(l[*a as usize..*b as usize].to_vec()))
        }
        ("distinct", [List(l)]) => {
            let mut out: Vec<Value> = Vec::new();
            for x in l.iter() {
                if !out.iter().any(|y| y.cel_eq(x)) {
                    out.push(x.clone());
                }
            }
            ok(Value::list(out))
        }
        ("flatten", [List(l), rest @ ..]) if rest.len() <= 1 => {
            let depth = match rest {
                [Int(d)] => *d,
                [] => 1,
                _ => return None,
            };
            if depth < 0 {
                return fail("level must be non-negative".into());
            }
            let mut out = Vec::new();
            flatten(l, depth, &mut out);
            ok(Value::list(out))
        }
        ("lists.range", [Int(n)]) if *n < 0 => fail(format!("lists.range() requires a non-negative count, got {n}")),
        ("lists.range", [Int(n)]) => ok(Value::list((0..*n).map(Int).collect())),

        // ------------------------------------------------------------ sets
        ("sets.contains", [List(a), List(b)]) => ok(Bool(subset(b, a))),
        ("sets.equivalent", [List(a), List(b)]) => ok(Bool(subset(a, b) && subset(b, a))),
        ("sets.intersects", [List(a), List(b)]) => ok(Bool(a.iter().any(|x| b.iter().any(|y| x.cel_eq(y))))),

        // ------------------------------------------------------------ encoders
        ("base64.encode", [Bytes(b)]) => ok(str(base64_encode(b))),
        ("base64.decode", [String(s)]) => {
            Some(base64_decode(s).map(|b| Bytes(Arc::from(b))).ok_or_else(|| "illegal base64 data".to_string()))
        }
        _ => None,
    }
}

/// The zero value of a type, which `optional.ofNonZeroValue` treats as absent.
fn is_zero(v: &Value) -> bool {
    use Value::*;
    match v {
        Null => true,
        Bool(b) => !b,
        Int(i) => *i == 0,
        Uint(u) => *u == 0,
        Double(d) => *d == 0.0,
        String(s) => s.is_empty(),
        Bytes(b) => b.is_empty(),
        List(l) => l.is_empty(),
        Map(m) => m.is_empty(),
        Struct(s) => s.fields.is_empty(),
        Timestamp(t) | Duration(t) => *t == 0,
        Date(d) => *d == 0,
        Optional(o) => o.is_none(),
        Type(_) | Net(_) => false,
    }
}

fn netv(n: N) -> Value {
    Value::Net(Arc::new(n))
}

fn str(s: std::string::String) -> Value {
    Value::String(Arc::from(s))
}

fn subset(small: &[Value], big: &[Value]) -> bool {
    small.iter().all(|x| big.iter().any(|y| x.cel_eq(y)))
}

fn flatten(l: &[Value], depth: i64, out: &mut Vec<Value>) {
    for x in l {
        match x {
            Value::List(inner) if depth > 0 => flatten(inner, depth - 1, out),
            other => out.push(other.clone()),
        }
    }
}

/// Order two values of one comparable kind (numbers compare across kinds).
pub fn order(a: &Value, b: &Value) -> Option<Ordering> {
    use Value::*;
    match (a, b) {
        (String(x), String(y)) => Some(x.cmp(y)),
        (Bytes(x), Bytes(y)) => Some(x.cmp(y)),
        (Bool(x), Bool(y)) => Some(x.cmp(y)),
        (Date(x), Date(y)) => Some(x.cmp(y)),
        (Timestamp(x), Timestamp(y)) | (Duration(x), Duration(y)) => Some(x.cmp(y)),
        _ => numeric_cmp(a, b),
    }
}

/// `items` sorted (stably) by the parallel list `keys`.
fn sorted(items: &[Value], keys: &[Value]) -> Result<Vec<Value>, String> {
    let mut idx: Vec<usize> = (0..items.len()).collect();
    if let Some(first) = keys.first() {
        for k in keys {
            if order(first, k).is_none() || std::mem::discriminant(first) != std::mem::discriminant(k) {
                return Err(format!("list elements must have the same type: {} and {}", first.type_name(), k.type_name()));
            }
        }
    }
    idx.sort_by(|&i, &j| order(&keys[i], &keys[j]).unwrap_or(Ordering::Equal));
    Ok(idx.into_iter().map(|i| items[i].clone()).collect())
}

/// `strings.quote`: a double-quoted CEL string literal.
fn quote(s: &str) -> std::string::String {
    let mut out = std::string::String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '\u{7}' => out.push_str("\\a"),
            '\u{8}' => out.push_str("\\b"),
            '\u{c}' => out.push_str("\\f"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\u{b}' => out.push_str("\\v"),
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            c if c.is_control() => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

// ---------------------------------------------------------------- format

/// `"...".format([args])`: printf-style clauses `%s %d %f %e %b %o %x %X`, with an
/// optional precision (`%.3f`) and `%%` for a literal percent sign.
fn format(f: &str, args: &[Value]) -> Result<Value, String> {
    let mut out = std::string::String::new();
    let mut chars = f.chars().peekable();
    let mut next_arg = 0usize;
    while let Some(c) = chars.next() {
        if c != '%' {
            out.push(c);
            continue;
        }
        if chars.peek() == Some(&'%') {
            chars.next();
            out.push('%');
            continue;
        }
        let mut precision: Option<usize> = None;
        if chars.peek() == Some(&'.') {
            chars.next();
            let mut digits = std::string::String::new();
            while let Some(d) = chars.peek().filter(|d| d.is_ascii_digit()) {
                digits.push(*d);
                chars.next();
            }
            precision = Some(digits.parse().map_err(|_| "could not parse formatting clause: invalid precision".to_string())?);
        }
        let verb = chars.next().ok_or("could not parse formatting clause: missing formatting verb")?;
        if !matches!(verb, 's' | 'd' | 'f' | 'e' | 'b' | 'o' | 'x' | 'X') {
            return Err(format!("could not parse formatting clause: unrecognized formatting clause \"{verb}\""));
        }
        let arg = args.get(next_arg).ok_or_else(|| format!("index {next_arg} out of range"))?;
        next_arg += 1;
        out.push_str(&clause(verb, precision, arg).map_err(|m| format!("error during formatting: {m}"))?);
    }
    Ok(str(out))
}

fn clause(verb: char, precision: Option<usize>, arg: &Value) -> Result<std::string::String, std::string::String> {
    use Value::*;
    let given = || arg.type_name();
    let non_finite = |d: f64| -> Option<std::string::String> {
        if d.is_nan() {
            Some("NaN".into())
        } else if d.is_infinite() {
            Some(if d > 0.0 { "Infinity".into() } else { "-Infinity".into() })
        } else {
            None
        }
    };
    let as_double = |what: &str| -> Result<f64, std::string::String> {
        match arg {
            Double(d) => Ok(*d),
            Int(i) => Ok(*i as f64),
            Uint(u) => Ok(*u as f64),
            _ => Err(format!("{what} clause can only be used on doubles, was given {}", given())),
        }
    };
    Ok(match verb {
        's' => to_display(arg)?,
        'd' => match arg {
            Int(i) => i.to_string(),
            Uint(u) => u.to_string(),
            Double(d) if !d.is_finite() => non_finite(*d).unwrap(),
            _ => return Err(format!("decimal clause can only be used on integers, was given {}", given())),
        },
        'f' => {
            let d = as_double("fixed-point")?;
            non_finite(d).unwrap_or_else(|| format!("{d:.*}", precision.unwrap_or(6)))
        }
        'e' => {
            let d = as_double("scientific")?;
            non_finite(d).unwrap_or_else(|| scientific(d, precision.unwrap_or(6)))
        }
        'b' => match arg {
            Int(i) if *i < 0 => format!("-{:b}", i.unsigned_abs()),
            Int(i) => format!("{i:b}"),
            Uint(u) => format!("{u:b}"),
            Bool(b) => u8::from(*b).to_string(),
            _ => return Err(format!("only integers and bools can be formatted as binary, was given {}", given())),
        },
        'o' => match arg {
            Int(i) if *i < 0 => format!("-{:o}", i.unsigned_abs()),
            Int(i) => format!("{i:o}"),
            Uint(u) => format!("{u:o}"),
            _ => return Err(format!("octal clause can only be used on integers, was given {}", given())),
        },
        _ => {
            let hex = match arg {
                Int(i) if *i < 0 => format!("-{:x}", i.unsigned_abs()),
                Int(i) => format!("{i:x}"),
                Uint(u) => format!("{u:x}"),
                String(s) => s.bytes().map(|b| format!("{b:02x}")).collect(),
                Bytes(b) => b.iter().map(|b| format!("{b:02x}")).collect(),
                _ => return Err(format!("only integers, byte buffers, and strings can be formatted as hex, was given {}", given())),
            };
            if verb == 'X' {
                hex.to_uppercase()
            } else {
                hex
            }
        }
    })
}

/// `1.052033e+03`: Go's `%e` layout, with a sign and at least two exponent digits.
fn scientific(d: f64, precision: usize) -> std::string::String {
    let s = format!("{d:.precision$e}");
    let (mantissa, exp) = s.split_once('e').unwrap_or((&s, "0"));
    let exp: i32 = exp.parse().unwrap_or(0);
    format!("{mantissa}e{}{:02}", if exp < 0 { '-' } else { '+' }, exp.abs())
}

/// The `%s` rendering of a value: strings unquoted, containers recursively.
fn to_display(v: &Value) -> Result<std::string::String, std::string::String> {
    use Value::*;
    Ok(match v {
        Null => "null".into(),
        Bool(b) => b.to_string(),
        Int(i) => i.to_string(),
        Uint(u) => u.to_string(),
        Double(d) => format_double(*d),
        String(s) => s.to_string(),
        Bytes(b) => std::string::String::from_utf8_lossy(b).into_owned(),
        Type(t) => t.to_string(),
        Timestamp(t) => time::format_timestamp(*t),
        Duration(d) => time::format_duration(*d),
        Date(d) => crate::date::format_date(*d),
        List(l) => {
            let parts: Result<Vec<_>, _> = l.iter().map(to_display).collect();
            format!("[{}]", parts?.join(", "))
        }
        Map(m) => {
            let mut parts = m
                .iter()
                .map(|(k, x)| Ok((to_display(&Key::to_value(k))?, to_display(x)?)))
                .collect::<Result<Vec<_>, std::string::String>>()?;
            parts.sort();
            let parts: Vec<_> = parts.into_iter().map(|(k, x)| format!("{k}: {x}")).collect();
            format!("{{{}}}", parts.join(", "))
        }
        Value::Net(n) => n.to_string(),
        Struct(_) | Optional(_) => {
            return Err(format!(
                "string clause can only be used on strings, bools, bytes, ints, doubles, maps, lists, types, durations, and timestamps, was given {}",
                v.type_name()
            ))
        }
    })
}

/// Shortest round-trip rendering of a double, as `string(double)` gives it.
pub fn format_double(d: f64) -> std::string::String {
    if d.is_nan() {
        "NaN".into()
    } else if d.is_infinite() {
        if d > 0.0 { "Infinity" } else { "-Infinity" }.into()
    } else if d != 0.0 && (d.abs() >= 1e21 || d.abs() < 1e-6) {
        let s = format!("{d:e}");
        let (m, e) = s.split_once('e').unwrap_or((&s, "0"));
        let e: i32 = e.parse().unwrap_or(0);
        format!("{m}e{}{:02}", if e < 0 { '-' } else { '+' }, e.abs())
    } else {
        d.to_string()
    }
}

// ---------------------------------------------------------------- base64

const B64: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

fn base64_encode(b: &[u8]) -> std::string::String {
    let mut out = std::string::String::with_capacity(b.len().div_ceil(3) * 4);
    for chunk in b.chunks(3) {
        let n = (u32::from(chunk[0]) << 16) | (u32::from(*chunk.get(1).unwrap_or(&0)) << 8) | u32::from(*chunk.get(2).unwrap_or(&0));
        for i in 0..4 {
            if i <= chunk.len() {
                out.push(B64[(n >> (18 - 6 * i) & 63) as usize] as char);
            } else {
                out.push('=');
            }
        }
    }
    out
}

/// Standard alphabet; padding is optional (cel-go accepts both forms).
fn base64_decode(s: &str) -> Option<Vec<u8>> {
    let body = s.trim_end_matches('=');
    if s.len() - body.len() > 2 || (s.len() != body.len() && !s.len().is_multiple_of(4)) {
        return None;
    }
    let mut out = Vec::with_capacity(body.len() * 3 / 4);
    let (mut acc, mut bits) = (0u32, 0u32);
    for c in body.bytes() {
        let v = B64.iter().position(|&x| x == c)? as u32;
        acc = (acc << 6) | v;
        bits += 6;
        if bits >= 8 {
            bits -= 8;
            out.push((acc >> bits) as u8);
            acc &= (1 << bits) - 1;
        }
    }
    // a lone trailing sextet cannot encode a byte
    (body.len() % 4 != 1).then_some(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn base64_round_trip() {
        for s in ["", "f", "fo", "foo", "foob", "fooba", "foobar"] {
            let enc = base64_encode(s.as_bytes());
            assert_eq!(base64_decode(&enc).as_deref(), Some(s.as_bytes()), "{enc}");
            assert_eq!(base64_decode(enc.trim_end_matches('=')).as_deref(), Some(s.as_bytes()));
        }
        assert_eq!(base64_encode(b"hello"), "aGVsbG8=");
        assert!(base64_decode("a").is_none());
        assert!(base64_decode("a$==").is_none());
    }

    #[test]
    fn format_clauses() {
        let f = |fmt: &str, args: Vec<Value>| match format(fmt, &args) {
            Ok(Value::String(s)) => s.to_string(),
            other => panic!("{other:?}"),
        };
        assert_eq!(f("%.3f", vec![Value::Double(1.2345)]), "1.234");
        assert_eq!(f("%.6e", vec![Value::Double(1052.032911275)]), "1.052033e+03");
        assert_eq!(f("%x", vec![Value::str("Hello world!")]), "48656c6c6f20776f726c6421");
        assert_eq!(f("%%%s%%", vec![Value::str("t")]), "%t%");
        assert!(format("%d %d", &[Value::Int(1)]).is_err());
        assert!(format("%E", &[Value::Double(1.0)]).is_err());
    }
}
