//! cel-spec conformance runner.
//!
//! Runs every test in `third_party/cel-spec/tests/simple/testdata` through celspresso's
//! parser, checker and evaluator, prints a per-file report with failures grouped by cause,
//! and ratchets against `passing.txt`: a test that passed before must keep passing.
//!
//!   cargo run -p celspresso-conformance --release            # report + ratchet check
//!   cargo run -p celspresso-conformance --release -- --update   # record new passes
//!   cargo run -p celspresso-conformance --release -- --show <substring>   # list failures

use celspresso_check::{check, check_unchecked, CelType, Schema, VarDecl};
use celspresso_eval::{evaluate, Key, Limits, NoFunctions, Value};
use celspresso_syntax::parse;
use prost_reflect::{DescriptorPool, DynamicMessage, MapKey, Value as PV};
use std::collections::{BTreeMap, BTreeSet};
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::path::{Path, PathBuf};
use std::sync::Arc;

const DESCRIPTORS: &[u8] = include_bytes!(concat!(env!("OUT_DIR"), "/cel_spec.bin"));

enum Outcome {
    Pass,
    /// Not runnable yet (needs a feature the runner or library deliberately lacks).
    Skip(String),
    Fail(String),
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let update = args.iter().any(|a| a == "--update");
    let show = args.iter().position(|a| a == "--show").and_then(|i| args.get(i + 1)).cloned();

    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let data = manifest.join("../../third_party/cel-spec/tests/simple/testdata");
    let baseline_path = manifest.join("passing.txt");

    let pool = DescriptorPool::decode(DESCRIPTORS).expect("descriptor set");
    let file_desc = pool.get_message_by_name("cel.expr.conformance.test.SimpleTestFile").unwrap();

    let mut files: Vec<PathBuf> = std::fs::read_dir(&data)
        .unwrap_or_else(|_| panic!("{} missing; run `git submodule update --init`", data.display()))
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|x| x == "textproto"))
        .collect();
    files.sort();

    let parsed: Vec<(String, DynamicMessage)> = files
        .iter()
        .map(|path| {
            let text = std::fs::read_to_string(path).unwrap();
            let file = DynamicMessage::parse_text_format(file_desc.clone(), &text).unwrap_or_else(|e| panic!("{}: {e:?}", path.display()));
            (path.file_stem().unwrap().to_string_lossy().to_string(), file)
        })
        .collect();

    // silence panic messages from isolated tests; they are reported as failures
    std::panic::set_hook(Box::new(|_| {}));

    let mut passing = BTreeSet::new();
    let mut causes: BTreeMap<String, Vec<String>> = BTreeMap::new();
    let mut skips: BTreeMap<String, usize> = BTreeMap::new();
    let (mut total_pass, mut total_fail, mut total_skip) = (0, 0, 0);
    println!("| file | pass | fail | skip |\n|---|---:|---:|---:|");
    for (fname, file) in &parsed {
        let (mut p, mut f, mut s) = (0, 0, 0);
        for section in list(file, "section") {
            let sname = string(&section, "name");
            for test in list(&section, "test") {
                let id = format!("{fname}/{sname}/{}", string(&test, "name"));
                let outcome = catch_unwind(AssertUnwindSafe(|| run_test(&test)))
                    .unwrap_or_else(|e| Outcome::Fail(format!("panic: {}", panic_message(&e))));
                match outcome {
                    Outcome::Pass => {
                        p += 1;
                        passing.insert(id);
                    }
                    Outcome::Skip(why) => {
                        s += 1;
                        *skips.entry(why).or_default() += 1;
                    }
                    Outcome::Fail(why) => {
                        f += 1;
                        if show.as_deref().is_some_and(|q| id.starts_with(q) || why.contains(q)) {
                            println!("FAIL {id}\n     expr: {}\n     {why}", string(&test, "expr"));
                        }
                        causes.entry(bucket(&why)).or_default().push(id);
                    }
                }
            }
        }
        println!("| {fname} | {p} | {f} | {s} |");
        total_pass += p;
        total_fail += f;
        total_skip += s;
    }
    let total = total_pass + total_fail + total_skip;
    println!("| **total** | **{total_pass}** ({:.1}%) | {total_fail} | {total_skip} |", 100.0 * total_pass as f64 / total as f64);

    let mut ranked: Vec<_> = causes.iter().collect();
    ranked.sort_by_key(|(_, ids)| std::cmp::Reverse(ids.len()));
    println!("\nTop failure causes:");
    for (cause, ids) in ranked.iter().take(25) {
        println!("  {:>4}  {cause}   (e.g. {})", ids.len(), ids[0]);
    }
    println!("\nSkipped:");
    for (why, n) in &skips {
        println!("  {n:>4}  {why}");
    }

    ratchet(&baseline_path, &passing, update);
}

fn ratchet(path: &Path, passing: &BTreeSet<String>, update: bool) {
    let baseline: BTreeSet<String> = std::fs::read_to_string(path)
        .unwrap_or_default()
        .lines()
        .filter(|l| !l.is_empty() && !l.starts_with('#'))
        .map(str::to_string)
        .collect();
    let regressed: Vec<_> = baseline.difference(passing).collect();
    let gained = passing.difference(&baseline).count();
    if !regressed.is_empty() {
        eprintln!("\nREGRESSION: {} previously passing test(s) now fail:", regressed.len());
        for r in &regressed {
            eprintln!("  {r}");
        }
        std::process::exit(1);
    }
    if update {
        let mut out = String::from("# cel-spec conformance tests celspresso passes. Maintained by:\n");
        out.push_str("#   cargo run -p celspresso-conformance --release -- --update\n");
        for id in passing {
            out.push_str(id);
            out.push('\n');
        }
        std::fs::write(path, out).unwrap();
        println!("\nrecorded {} passing tests ({gained} new)", passing.len());
    } else if gained > 0 {
        println!("\n{gained} new passing test(s); run with --update to lock them in");
    } else {
        println!("\nratchet ok ({} tests locked in)", baseline.len());
    }
}

/// Group failure messages so the report ranks causes, not individual tests.
fn bucket(why: &str) -> String {
    let mut out = String::new();
    let mut in_quote = false;
    for c in why.chars() {
        match c {
            '\'' => {
                in_quote = !in_quote;
                out.push('\'');
            }
            _ if in_quote => {}
            c if c.is_ascii_digit() => {}
            c => out.push(c),
        }
    }
    // keep the quoted name for "undeclared reference / no overload" style messages
    if why.contains("undeclared") || why.contains("no matching overload") || why.contains("undefined") {
        return why.chars().take(90).collect();
    }
    out.chars().take(90).collect()
}

fn panic_message(e: &Box<dyn std::any::Any + Send>) -> String {
    e.downcast_ref::<String>().cloned().or_else(|| e.downcast_ref::<&str>().map(|s| s.to_string())).unwrap_or_default()
}

// -- running one test -----------------------------------------------------------

fn run_test(t: &DynamicMessage) -> Outcome {
    let src = string(t, "expr");
    if boolean(t, "disable_macros") {
        return Outcome::Skip("disable_macros".into());
    }
    if !string(t, "container").is_empty() {
        return Outcome::Skip("container".into());
    }
    if t.has_field_by_name("unknown") || t.has_field_by_name("any_unknowns") {
        return Outcome::Skip("unknowns (partial evaluation)".into());
    }

    let mut schema = Schema::with_stdlib();
    for decl in list(t, "type_env") {
        let name = string(&decl, "name");
        if let Some(ident) = msg(&decl, "ident") {
            let ty = match msg(&ident, "type").map(|ty| cel_type(&ty)) {
                Some(Ok(ty)) => ty,
                Some(Err(why)) => return Outcome::Fail(format!("type_env: {why}")),
                None => CelType::Dyn,
            };
            schema.vars.insert(name.clone(), VarDecl { name, ty, constraints: Default::default() });
        } else {
            return Outcome::Skip("type_env function declarations".into());
        }
    }

    let mut bindings = BTreeMap::new();
    if let Some(PV::Map(m)) = t.get_field_by_name("bindings").map(|c| c.into_owned()) {
        for (k, v) in m {
            let MapKey::String(name) = k else { continue };
            let PV::Message(ev) = v else { continue };
            let Some(val) = msg(&ev, "value") else {
                return Outcome::Skip("error/unknown bindings".into());
            };
            match value(&val) {
                Ok(v) => {
                    schema.vars.entry(name.clone()).or_insert(VarDecl {
                        name: name.clone(),
                        ty: CelType::Dyn,
                        constraints: Default::default(),
                    });
                    bindings.insert(name, v);
                }
                Err(why) => return Outcome::Fail(format!("binding: {why}")),
            }
        }
    }

    let expr = match parse(&src) {
        Ok(e) => e,
        Err(e) => return Outcome::Fail(format!("parse: {}", e.message)),
    };
    if boolean(t, "disable_check") {
        let checked = check_unchecked(expr, Arc::new(schema));
        let result = evaluate(&checked, &bindings, &NoFunctions, Limits::default());
        return judge(t, result);
    }
    let checked = match check(expr, Arc::new(schema)) {
        Ok(c) => c,
        Err(errs) => {
            let first = errs.into_iter().next().map(|e| e.message).unwrap_or_default();
            // a test that expects an error may legitimately fail type-checking
            if t.has_field_by_name("eval_error") || t.has_field_by_name("any_eval_errors") {
                return Outcome::Pass;
            }
            return Outcome::Fail(format!("check: {first}"));
        }
    };

    if let Some(tr) = msg(t, "typed_result") {
        if let Some(dt) = msg(&tr, "deduced_type") {
            let want = match cel_type(&dt) {
                Ok(ty) => ty,
                Err(why) => return Outcome::Fail(format!("deduced_type: {why}")),
            };
            let got = checked.type_of(checked.expr.id).clone();
            if got != want {
                return Outcome::Fail(format!("deduced type: got {got}, want {want}"));
            }
        }
        if boolean(t, "check_only") {
            return Outcome::Pass;
        }
    } else if boolean(t, "check_only") {
        return Outcome::Pass;
    }

    let result = evaluate(&checked, &bindings, &NoFunctions, Limits::default());
    judge(t, result)
}

fn judge(t: &DynamicMessage, result: celspresso_eval::EvalResult) -> Outcome {
    let expected = if let Some(v) = msg(t, "value") {
        Some(v)
    } else if let Some(tr) = msg(t, "typed_result") {
        msg(&tr, "result")
    } else {
        None
    };
    match expected {
        Some(v) => {
            let want = match value(&v) {
                Ok(w) => w,
                Err(why) => return Outcome::Fail(format!("expected value: {why}")),
            };
            match result {
                Ok(got) if strict_eq(&got, &want) => Outcome::Pass,
                Ok(got) => Outcome::Fail(format!("wrong value: got {}, want {}", show(&got), show(&want))),
                Err(e) => Outcome::Fail(format!("eval error: {}", e.message)),
            }
        }
        // eval_error / any_eval_errors: error messages are implementation-defined
        None if t.has_field_by_name("eval_error") || t.has_field_by_name("any_eval_errors") => match result {
            Err(_) => Outcome::Pass,
            Ok(got) => Outcome::Fail(format!("expected an error, got {}", show(&got))),
        },
        // no matcher means "evaluates to true"
        None => match result {
            Ok(Value::Bool(true)) => Outcome::Pass,
            Ok(got) => Outcome::Fail(format!("wrong value: got {}, want true", show(&got))),
            Err(e) => Outcome::Fail(format!("eval error: {}", e.message)),
        },
    }
}

/// Exact equality for test comparison: types must match, NaN equals NaN.
fn strict_eq(a: &Value, b: &Value) -> bool {
    match (a, b) {
        (Value::Null, Value::Null) => true,
        (Value::Bool(x), Value::Bool(y)) => x == y,
        (Value::Int(x), Value::Int(y)) => x == y,
        (Value::Uint(x), Value::Uint(y)) => x == y,
        (Value::Double(x), Value::Double(y)) => (x.is_nan() && y.is_nan()) || x == y,
        (Value::String(x), Value::String(y)) => x == y,
        (Value::Bytes(x), Value::Bytes(y)) => x == y,
        (Value::Date(x), Value::Date(y)) => x == y,
        (Value::Timestamp(x), Value::Timestamp(y)) | (Value::Duration(x), Value::Duration(y)) => x == y,
        (Value::Type(x), Value::Type(y)) => x == y,
        (Value::List(x), Value::List(y)) => x.len() == y.len() && x.iter().zip(y.iter()).all(|(a, b)| strict_eq(a, b)),
        (Value::Map(x), Value::Map(y)) => {
            x.len() == y.len()
                && x.iter().all(|(k, v)| y.get(k).is_some_and(|w| key_type_eq(k, y.get_key_value(k).unwrap().0) && strict_eq(v, w)))
        }
        (Value::Struct(x), Value::Struct(y)) => {
            x.type_name == y.type_name
                && x.fields.len() == y.fields.len()
                && x.fields.iter().all(|(k, v)| y.fields.get(k).is_some_and(|w| strict_eq(v, w)))
        }
        _ => false,
    }
}

fn key_type_eq(a: &Key, b: &Key) -> bool {
    std::mem::discriminant(a) == std::mem::discriminant(b)
}

fn show(v: &Value) -> String {
    let s = format!("{v:?}");
    if s.len() > 120 {
        format!("{}…", &s[..s.char_indices().nth(120).map_or(s.len(), |(i, _)| i)])
    } else {
        s
    }
}

// -- proto -> celspresso conversion ---------------------------------------------

fn value(m: &DynamicMessage) -> Result<Value, String> {
    let field = |n: &str| m.get_field_by_name(n).map(|c| c.into_owned());
    let has = |n: &str| m.has_field_by_name(n);
    Ok(if has("null_value") {
        Value::Null
    } else if has("bool_value") {
        Value::Bool(matches!(field("bool_value"), Some(PV::Bool(true))))
    } else if has("int64_value") {
        let Some(PV::I64(i)) = field("int64_value") else { unreachable!() };
        Value::Int(i)
    } else if has("uint64_value") {
        let Some(PV::U64(u)) = field("uint64_value") else { unreachable!() };
        Value::Uint(u)
    } else if has("double_value") {
        let Some(PV::F64(d)) = field("double_value") else { unreachable!() };
        Value::Double(d)
    } else if has("string_value") {
        Value::String(string(m, "string_value").into())
    } else if has("bytes_value") {
        let Some(PV::Bytes(b)) = field("bytes_value") else { unreachable!() };
        Value::Bytes(b.to_vec().into())
    } else if has("list_value") {
        let lv = msg(m, "list_value").unwrap();
        Value::List(Arc::new(list(&lv, "values").iter().map(value).collect::<Result<_, _>>()?))
    } else if has("map_value") {
        let mv = msg(m, "map_value").unwrap();
        let mut out = BTreeMap::new();
        for e in list(&mv, "entries") {
            let k = value(&msg(&e, "key").ok_or("map entry without key")?)?;
            let k = Key::from_value(&k).ok_or_else(|| format!("invalid map key {k:?}"))?;
            out.insert(k, value(&msg(&e, "value").ok_or("map entry without value")?)?);
        }
        Value::Map(Arc::new(out))
    } else if has("type_value") {
        Value::Type(string(m, "type_value").into())
    } else if has("enum_value") {
        return Err("enum values are not supported".into());
    } else if has("object_value") {
        let any = msg(m, "object_value").unwrap();
        let url = string(&any, "type_url");
        let short = url.rsplit('/').next().unwrap_or(&url);
        if short == "google.protobuf.Duration" || short == "google.protobuf.Timestamp" {
            let Some(PV::Bytes(b)) = any.get_field_by_name("value").map(|c| c.into_owned()) else {
                return Err("Any without value".into());
            };
            let (secs, nanos) = seconds_nanos(&b)?;
            let ns = i128::from(secs) * 1_000_000_000 + i128::from(nanos);
            return Ok(if short.ends_with("Duration") { Value::Duration(ns) } else { Value::Timestamp(ns) });
        }
        return Err(format!("object values ({}) are not supported", short.replace("cel.expr.conformance.", "")));
    } else {
        return Err("empty value".into());
    })
}

fn cel_type(t: &DynamicMessage) -> Result<CelType, String> {
    let has = |n: &str| t.has_field_by_name(n);
    let prim = |n: &str| -> Result<CelType, String> {
        Ok(match t.get_field_by_name(n).map(|c| c.into_owned()) {
            Some(PV::EnumNumber(1)) => CelType::Bool,
            Some(PV::EnumNumber(2)) => CelType::Int,
            Some(PV::EnumNumber(3)) => CelType::Uint,
            Some(PV::EnumNumber(4)) => CelType::Double,
            Some(PV::EnumNumber(5)) => CelType::String,
            Some(PV::EnumNumber(6)) => CelType::Bytes,
            other => return Err(format!("unknown primitive {other:?}")),
        })
    };
    Ok(if has("dyn") {
        CelType::Dyn
    } else if has("null") {
        CelType::Null
    } else if has("primitive") {
        prim("primitive")?
    } else if has("wrapper") {
        CelType::Nullable(Box::new(prim("wrapper")?))
    } else if has("list_type") {
        let l = msg(t, "list_type").unwrap();
        CelType::list(msg(&l, "elem_type").map(|e| cel_type(&e)).transpose()?.unwrap_or(CelType::Dyn))
    } else if has("map_type") {
        let m = msg(t, "map_type").unwrap();
        let k = msg(&m, "key_type").map(|e| cel_type(&e)).transpose()?.unwrap_or(CelType::Dyn);
        let v = msg(&m, "value_type").map(|e| cel_type(&e)).transpose()?.unwrap_or(CelType::Dyn);
        CelType::Map(Box::new(k), Box::new(v))
    } else if has("type_param") {
        CelType::Param(string(t, "type_param"))
    } else if has("well_known") {
        match t.get_field_by_name("well_known").map(|c| c.into_owned()) {
            Some(PV::EnumNumber(2)) => CelType::Timestamp,
            Some(PV::EnumNumber(3)) => CelType::Duration,
            Some(PV::EnumNumber(1)) => return Err("google.protobuf.Any is not supported".into()),
            _ => return Err("unknown well-known type".into()),
        }
    } else if has("message_type") && string(t, "message_type") == "google.protobuf.Duration" {
        CelType::Duration
    } else if has("message_type") && string(t, "message_type") == "google.protobuf.Timestamp" {
        CelType::Timestamp
    } else if has("message_type") {
        return Err(format!("message types ({}) are not supported", string(t, "message_type")));
    } else if has("abstract_type") {
        let a = msg(t, "abstract_type").unwrap();
        let params: Vec<CelType> = match a.get_field_by_name("parameter_types").map(|c| c.into_owned()) {
            Some(PV::List(xs)) => xs
                .iter()
                .map(|x| match x {
                    PV::Message(m) => cel_type(m),
                    _ => Err("bad abstract type parameter".to_string()),
                })
                .collect::<Result<_, _>>()?,
            _ => vec![],
        };
        match (string(&a, "name").as_str(), params.as_slice()) {
            ("optional_type", [p]) => CelType::optional(p.clone()),
            (name, _) => return Err(format!("abstract type '{name}' is not supported")),
        }
    } else if has("type") {
        CelType::Type(Box::new(msg(t, "type").map(|e| cel_type(&e)).transpose()?.unwrap_or(CelType::Dyn)))
    } else {
        return Err("unsupported type kind".into());
    })
}

/// Decode the wire bytes of a `google.protobuf.Duration` / `Timestamp`: fields
/// 1 (int64 seconds) and 2 (int32 nanos), both varints.
fn seconds_nanos(mut b: &[u8]) -> Result<(i64, i32), String> {
    fn varint(b: &mut &[u8]) -> Result<u64, String> {
        let mut out = 0u64;
        for shift in (0..64).step_by(7) {
            let (&byte, rest) = b.split_first().ok_or("truncated varint")?;
            *b = rest;
            out |= u64::from(byte & 0x7f) << shift;
            if byte & 0x80 == 0 {
                return Ok(out);
            }
        }
        Err("varint too long".into())
    }
    let (mut secs, mut nanos) = (0i64, 0i32);
    while !b.is_empty() {
        let tag = varint(&mut b)?;
        let v = varint(&mut b)?;
        match tag {
            0x08 => secs = v as i64,
            0x10 => nanos = v as i64 as i32,
            _ => return Err(format!("unexpected field tag {tag}")),
        }
    }
    Ok((secs, nanos))
}

// -- DynamicMessage helpers -------------------------------------------------------

fn string(m: &DynamicMessage, name: &str) -> String {
    match m.get_field_by_name(name).map(|c| c.into_owned()) {
        Some(PV::String(s)) => s,
        _ => String::new(),
    }
}

fn boolean(m: &DynamicMessage, name: &str) -> bool {
    matches!(m.get_field_by_name(name).map(|c| c.into_owned()), Some(PV::Bool(true)))
}

fn msg(m: &DynamicMessage, name: &str) -> Option<DynamicMessage> {
    if !m.has_field_by_name(name) {
        return None;
    }
    match m.get_field_by_name(name)?.into_owned() {
        PV::Message(x) => Some(x),
        _ => None,
    }
}

fn list(m: &DynamicMessage, name: &str) -> Vec<DynamicMessage> {
    match m.get_field_by_name(name).map(|c| c.into_owned()) {
        Some(PV::List(xs)) => xs
            .into_iter()
            .filter_map(|x| match x {
                PV::Message(m) => Some(m),
                _ => None,
            })
            .collect(),
        _ => vec![],
    }
}
