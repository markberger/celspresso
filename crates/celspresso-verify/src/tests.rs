use crate::*;
use celspresso_check::{check, CelType, Constraints, FieldDecl, Schema, StructDecl, VarDecl};
use celspresso_eval::NoFunctions;
use std::sync::Arc;

fn schema() -> Arc<Schema> {
    let mut s = Schema::with_stdlib();
    let age = Constraints { ge: Some(0.0), le: Some(150.0), ..Default::default() };
    let roles = Constraints { max_length: Some(3), ..Default::default() };
    let tier = Constraints {
        one_of: Some(vec![celspresso_syntax::Literal::String("free".into()), celspresso_syntax::Literal::String("pro".into())]),
        ..Default::default()
    };
    s.structs.insert(
        "User".into(),
        StructDecl {
            name: "User".into(),
            fields: vec![
                FieldDecl { name: "age".into(), ty: CelType::Int, constraints: age },
                FieldDecl { name: "roles".into(), ty: CelType::list(CelType::String), constraints: roles },
                FieldDecl { name: "tier".into(), ty: CelType::String, constraints: tier },
                FieldDecl { name: "nick".into(), ty: CelType::nullable(CelType::String), constraints: Default::default() },
                FieldDecl { name: "born".into(), ty: CelType::Date, constraints: Default::default() },
            ],
        },
    );
    for (n, t) in [
        ("user", CelType::Struct("User".into())),
        ("x", CelType::Int),
        ("y", CelType::Int),
        ("s", CelType::String),
        ("xs", CelType::list(CelType::Int)),
        ("today", CelType::Date),
        ("m", CelType::map(CelType::String, CelType::Int)),
        ("ids", CelType::map(CelType::Int, CelType::String)),
    ] {
        s.vars.insert(n.into(), VarDecl { name: n.into(), ty: t, constraints: Default::default() });
    }
    for (n, t) in [
        ("at", CelType::Timestamp),
        ("until", CelType::Timestamp),
        ("dur", CelType::Duration),
        ("d", CelType::Double),
        ("e", CelType::Double),
    ] {
        s.vars.insert(n.into(), VarDecl { name: n.into(), ty: t, constraints: Default::default() });
    }
    let price = Constraints { ge: Some(0.0), le: Some(1000.0), ..Default::default() };
    s.vars.insert("price".into(), VarDecl { name: "price".into(), ty: CelType::Double, constraints: price });
    let lit = |v: i64| celspresso_syntax::Literal::Int(v);
    let more = [
        ("n", CelType::Uint, Constraints::default()),
        ("code", CelType::Int, Constraints { gt: Some(0.0), lt: Some(10.0), ..Default::default() }),
        ("level", CelType::Int, Constraints { one_of: Some(vec![lit(1), lit(2), lit(3)]), ..Default::default() }),
        (
            "zip",
            CelType::String,
            Constraints { min_length: Some(5), max_length: Some(5), pattern: Some("^[0-9]+$".into()), ..Default::default() },
        ),
        ("blob", CelType::Bytes, Constraints::default()),
        ("flags", CelType::list(CelType::Bool), Constraints { min_length: Some(1), max_length: Some(2), ..Default::default() }),
        (
            "tags",
            CelType::map(CelType::String, CelType::Bool),
            Constraints { min_length: Some(1), max_length: Some(2), ..Default::default() },
        ),
    ];
    for (n, t, cons) in more {
        s.vars.insert(n.into(), VarDecl { name: n.into(), ty: t, constraints: cons });
    }
    let ov =
        |id: &str, params: Vec<CelType>, result: CelType| celspresso_check::Overload { id: id.into(), receiver: false, params, result };
    s.functions.insert(
        "risk".into(),
        celspresso_check::FunctionDecl { name: "risk".into(), overloads: vec![ov("risk_int", vec![CelType::Int], CelType::Int)] },
    );
    s.functions.insert(
        "scale".into(),
        celspresso_check::FunctionDecl {
            name: "scale".into(),
            overloads: vec![ov("scale_double", vec![CelType::Double], CelType::Double)],
        },
    );
    s.functions.insert(
        "words".into(),
        celspresso_check::FunctionDecl {
            name: "words".into(),
            overloads: vec![ov("words_string", vec![CelType::String], CelType::list(CelType::String))],
        },
    );
    let small = Constraints { max_length: Some(3), ..Default::default() };
    for (n, t) in [
        ("bm", CelType::map(CelType::String, CelType::Int)),
        ("bids", CelType::map(CelType::Int, CelType::String)),
        ("bxs", CelType::list(CelType::Int)),
    ] {
        s.vars.insert(n.into(), VarDecl { name: n.into(), ty: t, constraints: small.clone() });
    }
    Arc::new(s)
}

fn c(src: &str) -> CheckedExpr {
    check(celspresso_syntax::parse(src).unwrap(), schema()).unwrap_or_else(|e| panic!("{src}: {}", e[0].message))
}

fn run(q: Query) -> Outcome {
    verify(&q, &[], Options::default(), &NoFunctions)
}

#[track_caller]
fn sat(src: &str) -> BTreeMap<String, Value> {
    match run(Query::Satisfiable(&c(src))).status {
        Status::Found(w) => w,
        s => panic!("{src}: expected SAT, got {s:?}"),
    }
}
#[track_caller]
fn unsat(src: &str) {
    match run(Query::Satisfiable(&c(src))).status {
        Status::NotFound => {}
        s => panic!("{src}: expected UNSAT, got {s:?}"),
    }
}
#[track_caller]
fn proved(src: &str) {
    match run(Query::AlwaysTrue(&c(src))).status {
        Status::NotFound => {}
        s => panic!("{src}: expected PROVED, got {s:?}"),
    }
}
#[track_caller]
fn refuted(src: &str) -> BTreeMap<String, Value> {
    match run(Query::AlwaysTrue(&c(src))).status {
        Status::Found(w) => w,
        s => panic!("{src}: expected REFUTED, got {s:?}"),
    }
}
#[track_caller]
fn exact(src: &str) {
    // proved without relying on the unroll bound
    let o = run(Query::AlwaysTrue(&c(src)));
    assert!(matches!(o.status, Status::NotFound), "{src}: expected PROVED, got {:?}", o.status);
    assert!(!o.bounded, "{src}: proof relied on the unroll bound");
}

#[test]
fn schema_constraints_are_assumptions() {
    unsat("user.age > 200");
    let w = sat("user.age > 100 && user.tier == 'pro'");
    let Value::Struct(u) = &w["user"] else { panic!() };
    assert!(matches!(u.fields["age"], Value::Int(a) if a > 100 && a <= 150));
    unsat("user.tier == 'enterprise'");
    unsat("size(user.roles) > 3");
}

#[test]
fn integer_semantics() {
    proved("x / 2 * 2 + x % 2 == x || x == 0 || true");
    proved("x >= 0 || x / 2 <= 0");
    refuted("x + 1 > x"); // overflow at int64 max is an error, so not always true
    proved("-7 / 2 == -3 && -7 % 2 == -1");
    let w = refuted("x / y == x / y");
    assert_eq!(w["y"], Value::Int(0));
}

#[test]
fn error_semantics() {
    proved("1 / x == 1 && false || true");
    let q = c("1 / x > 0 || x == 0");
    assert!(matches!(run(Query::AlwaysTrue(&q)).status, Status::Found(_)));
    let e = c("x / y");
    match run(Query::CanError(&e)).status {
        Status::Found(w) => assert_eq!(w["y"], Value::Int(0)),
        s => panic!("{s:?}"),
    }
    assert!(matches!(run(Query::CanError(&c("x + 0 == x || true"))).status, Status::NotFound));
}

#[test]
fn equivalence_and_implication() {
    let a = c("x > 5 && y < 3");
    let b = c("!(x <= 5 || y >= 3)");
    assert!(matches!(run(Query::Equivalent(&a, &b, ErrorMode::Strict)).status, Status::NotFound));
    let a = c("x > 5");
    let b = c("x > 3");
    assert!(matches!(run(Query::Implies(&a, &b)).status, Status::NotFound));
    assert!(matches!(run(Query::Implies(&b, &a)).status, Status::Found(_)));
    // `10 / x` errors at x == 0, but the `x > 0` guard absorbs it (in either order)
    let a = c("x > 0 && 10 / x >= 1");
    let b = c("x > 0 && x <= 10");
    assert!(matches!(run(Query::Equivalent(&a, &b, ErrorMode::Strict)).status, Status::NotFound));
    let a = c("10 / x >= 1 && x > 0");
    assert!(matches!(run(Query::Equivalent(&a, &b, ErrorMode::Strict)).status, Status::NotFound));
    let a = c("10 / x >= 1");
    let b = c("x <= 10 && x > 0");
    assert!(matches!(run(Query::Equivalent(&a, &b, ErrorMode::Strict)).status, Status::Found(_)));
    // non-bool expressions
    let a = c("x > 3 ? x : 3");
    let b = c("[x, 3].max()");
    assert!(matches!(run(Query::Equivalent(&a, &b, ErrorMode::Strict)).status, Status::NotFound));
}

#[test]
fn strings_and_regex() {
    let w = sat("s.startsWith('ab') && s.endsWith('yz') && size(s) == 5");
    let Value::String(v) = &w["s"] else { panic!() };
    assert!(v.starts_with("ab") && v.ends_with("yz") && v.chars().count() == 5);
    unsat("s.matches('^[0-9]+$') && s.contains('a')");
    sat("s.matches('^[a-c]{3}$') && s != 'abc'");
    proved("!s.matches('^x$') || s == 'x'");
}

#[test]
fn lists_and_comprehensions() {
    proved("user.roles.all(r, r != 'x') || user.roles.exists(r, r == 'x')");
    unsat("user.roles.filter(r, r == 'admin').size() > 3");
    let w = sat("'admin' in user.roles && user.roles.size() == 2");
    let Value::Struct(u) = &w["user"] else { panic!() };
    assert!(matches!(&u.fields["roles"], Value::List(l) if l.len() == 2));
    proved("[1, 2, 3].map(v, v * 2) == [2, 4, 6]");
    proved("[1, 2, 3].exists_one(v, v == 2)");
    // unbounded list: proofs degrade to UNKNOWN with bounded=true
    let o = run(Query::AlwaysTrue(&c("xs.all(v, v > 0) || xs.exists(v, v <= 0)")));
    assert!(o.bounded);
    assert!(matches!(o.status, Status::Unknown(_)));
    // but counterexamples are still real
    let w = refuted("xs.all(v, v < 10)");
    assert!(matches!(&w["xs"], Value::List(l) if !l.is_empty()));
}

#[test]
fn nullable_and_dates() {
    let w = sat("user.nick == null && user.age == 3");
    let Value::Struct(u) = &w["user"] else { panic!() };
    assert_eq!(u.fields["nick"], Value::Null);
    refuted("user.nick != null");
    // non-equality builtins see through nullable; a null operand is an evaluation error
    let w = sat("user.nick != null && size(user.nick) > 3 && user.nick.startsWith('z')");
    let Value::Struct(u) = &w["user"] else { panic!() };
    assert!(matches!(&u.fields["nick"], Value::String(s) if s.starts_with('z') && s.chars().count() > 3));
    proved("user.nick == null || size(user.nick) >= 0");
    refuted("size(user.nick) >= 0");
    let w = sat("user.born.ageOn(today) >= 18 && user.born.ageOn(today) < 19 && user.born.year() == 2000");
    let Value::Struct(u) = &w["user"] else { panic!() };
    let Value::Date(b) = u.fields["born"] else { panic!() };
    assert_eq!(celspresso_eval::date::civil_from_days(b).0, 2000);
    proved("date('2024-03-01') - date('2024-02-01') == 29");
    proved("user.born.ageOn(today) >= 18 || user.born.ageOn(today) < 18");
}

#[test]
fn vacuous_assumptions_are_unknown() {
    let p = c("x > 0");
    let a1 = c("x > 10");
    let a2 = c("x < 5");
    let o = verify(&Query::AlwaysTrue(&p), &[&a1, &a2], Options::default(), &NoFunctions);
    assert!(matches!(o.status, Status::Unknown(ref r) if r.contains("assumptions")), "{:?}", o.status);
    let o = verify(&Query::AlwaysTrue(&p), &[&a1], Options::default(), &NoFunctions);
    assert!(matches!(o.status, Status::NotFound));
}

#[test]
fn variables_hidden_by_approximations_never_fake_a_counterexample() {
    // `at` and `s` appear only under approximated calls, so the solver's model may
    // omit them; an unbound variable must not be read as "the predicate failed"
    for src in ["at.getHours('America/New_York') < 24", "at.getHours('Europe/Paris') >= 0 || s != s"] {
        match run(Query::AlwaysTrue(&c(src))).status {
            Status::Unknown(_) => {}
            s => panic!("{src}: expected UNKNOWN, got {s:?}"),
        }
    }
    // any counterexample that is reported must carry every variable and replay
    if let Status::Found(w) = run(Query::AlwaysTrue(&c("at.getHours('Asia/Tokyo') < 24 && x > 0"))).status {
        assert!(w.contains_key("at") && w.contains_key("x"));
    }
}

#[test]
fn block_and_two_variable_macros() {
    proved("cel.block([s + 'x', size(cel.index(0))], cel.index(1) > 0)");
    match run(Query::AlwaysTrue(&c("xs.all(i, v, v > i)"))).status {
        Status::Unknown(_) | Status::Found(_) => {}
        s => panic!("two-variable comprehensions must not be PROVED: {s:?}"),
    }
}

#[test]
fn maps() {
    // lookups, membership, presence and size
    exact("!('a' in bm) || bm['a'] == bm.a");
    exact("has(bm.a) == ('a' in bm)");
    exact("size(bm) >= 0 && size(bm) <= 3");
    // an unbounded map can't support a universal claim: UNKNOWN, never PROVED
    let o = run(Query::AlwaysTrue(&c("m.all(k, k in m)")));
    assert!(matches!(o.status, Status::Unknown(_)) && o.bounded, "{:?}", o.status);
    let w = sat("'a' in m && m['a'] > 5 && size(m) == 2");
    let Value::Map(mv) = &w["m"] else { panic!("{w:?}") };
    assert_eq!(mv.len(), 2);
    // a missing key is an error
    let w = match run(Query::CanError(&c("m['a'] > 0"))).status {
        Status::Found(w) => w,
        s => panic!("{s:?}"),
    };
    assert!(matches!(&w["m"], Value::Map(mv) if mv.is_empty() || !mv.keys().any(|k| k.to_value() == Value::str("a"))));
    // literals: lookups and duplicate keys
    exact("{'x': 1, 'y': 2}['y'] == 2");
    exact("{'x': x}.x == x");
    assert!(matches!(run(Query::CanError(&c("{s: 1, 'k': 2}.k == 2"))).status, Status::Found(_)));
    exact("size({1: 'a', 2: 'b'}) == 2");
    exact("{'a': 1} == {'a': 1} && {'a': 1, 'b': 2} == {'b': 2, 'a': 1} && {'a': 1} != {'a': 2}");
    // comprehensions over maps visit keys
    exact("bm.all(k, k in bm)");
    exact("bids.exists(k, bids[k] == s) == (s in bids.map(k, bids[k]))");
    // transformMap and friends use @mapInsert
    exact("bm.transformMap(k, v, v + 0) == bm");
}

#[test]
fn two_variable_comprehensions() {
    exact("[10, 20, 30].all(i, v, v == (i + 1) * 10)");
    exact("[5, 6].exists(i, v, i == 1 && v == 6)");
    exact("bxs.all(i, v, bxs[i] == v)");
    exact("bm.all(k, v, bm[k] == v)");
    let w = refuted("m.all(k, v, v > 0)");
    assert!(matches!(&w["m"], Value::Map(mv) if mv.values().any(|v| matches!(v, Value::Int(i) if *i <= 0))));
    exact("{'a': 1, 'b': 2}.transformList(k, v, v).size() == 2");
}

#[test]
fn optionals() {
    exact("optional.of(x).hasValue() && optional.of(x).value() == x");
    exact("!optional.none().hasValue() && optional.none().orValue(x) == x");
    exact("optional.ofNonZeroValue(x).hasValue() == (x != 0)");
    exact("optional.none().or(optional.of(s)).value() == s");
    exact("optional.of(s) == optional.of(s) && optional.none() == optional.none()");
    // value() of an empty optional is an error
    assert!(matches!(run(Query::CanError(&c("optional.ofNonZeroValue(x).value() > 0"))).status, Status::Found(_)));
    // optional selection and indexing
    exact("user.?age.value() == user.age");
    exact("user.?nick.hasValue()");
    exact("bm.?a.hasValue() == has(bm.a)");
    exact("bm[?'a'].orValue(0) == ('a' in bm ? bm['a'] : 0)");
    exact("bxs[?x].hasValue() == (x >= 0 && x < size(bxs))");
    exact("bm.?a.orValue(1) >= 1 || bm.a < 1");
    // optional entries in literals
    exact("size([?optional.ofNonZeroValue(x), 1]) == (x == 0 ? 1 : 2)");
    exact("size({?'a': bm.?a, 'b': 1}) == (has(bm.a) ? 2 : 1)");
    let w = sat("bm.?a.orValue(0) == 7");
    assert!(matches!(&w["bm"], Value::Map(mv) if mv.values().any(|v| *v == Value::Int(7))));
}

#[test]
fn timestamps_and_durations() {
    exact("timestamp('2024-03-01T00:00:00Z') - timestamp('2024-02-28T00:00:00Z') == duration('48h')");
    exact("timestamp('2024-12-31T23:59:59Z').getDayOfYear() == 365 && timestamp('2023-12-31T00:00:00Z').getDayOfYear() == 364");
    exact("timestamp('2024-07-04T15:30:00Z').getHours('-05:00') == 10 && timestamp('2024-07-04T15:30:00Z').getDayOfWeek() == 4");
    exact("timestamp('1969-12-31T23:59:59.5Z').getSeconds() == 59 && timestamp('1969-12-31T23:59:59.5Z').getMilliseconds() == 500");
    exact("duration('-90m').getHours() == -1 && duration('1.5s').getMilliseconds() == 500 && duration('-1.5s').getMilliseconds() == -500");
    proved("at + dur - dur == at || true");
    exact("until - at == duration('0s') || until != at");
    // ordering and arithmetic agree
    unsat("dur > duration('0s') && dur < duration('24h') && at < timestamp('9000-01-01T00:00:00Z') && at + dur <= at");
    let w = refuted("until < at + duration('24h')");
    assert!(
        matches!((&w["until"], &w["at"]), (Value::Timestamp(u), Value::Timestamp(a)) if u - a >= 86_400 * 1_000_000_000 || *a > 253_402_000_000 * 1_000_000_000)
    );
    // overflow past year 9999 is an error
    assert!(matches!(run(Query::CanError(&c("at + duration('1h') > at"))).status, Status::Found(_)));
    exact("timestamp(0) == timestamp('1970-01-01T00:00:00Z') && int(timestamp('1970-01-01T00:00:01.9Z')) == 1");
    // a named zone isn't modeled: UNKNOWN, never a guess
    assert!(matches!(run(Query::AlwaysTrue(&c("at.getHours('America/New_York') < 24"))).status, Status::Unknown(_)));
    unsat("at.getFullYear() == 2025 && at.getMonth() == 1 && at.getDate() == 29 || at.getHours() == 25");
    let w = sat("at.getFullYear() == 2024 && at.getMonth() == 1 && at.getDate() == 29 && at.getHours('+09:00') == 0");
    assert!(matches!(w["at"], Value::Timestamp(_)));
}

#[test]
fn doubles() {
    // NaN breaks reflexivity and trichotomy; the witness is a real NaN
    let w = refuted("d == d");
    assert!(matches!(w["d"], Value::Double(v) if v.is_nan()));
    let w = refuted("d < e || d >= e");
    assert!(matches!((&w["d"], &w["e"]), (Value::Double(a), Value::Double(b)) if a.is_nan() || b.is_nan()));
    // constraints exclude NaN
    exact("price == price && price >= 0.0");
    // -0.0 == 0.0, yet they differ under division
    exact("-0.0 == 0.0 && 1.0 / -0.0 < 0.0 && 1.0 / 0.0 > 1.0e308");
    // rounding is IEEE round-to-nearest-even
    exact("0.1 + 0.2 != 0.3 && 0.5 + 0.25 == 0.75");
    let w = refuted("d + 1.0 > d");
    assert!(matches!(w["d"], Value::Double(v) if v.is_nan() || v.is_infinite() || v + 1.0 == v));
    // mixed int/double comparisons convert the int (lossily, as the spec says)
    exact("dyn(9007199254740993) == 9007199254740992.0 && !(9223372036854775807 < dyn(9223372036854775808.0))");
    exact("x < 2 || dyn(x) >= 2.0");
    // conversions
    exact("int(2.9) == 2 && int(-2.9) == -2 && uint(3.5) == 3u && double(3) == 3.0");
    assert!(matches!(run(Query::CanError(&c("int(d) > 0"))).status, Status::Found(_)));
    exact("price < 1.0 || int(price) >= 1");
    exact("double(x) - double(x) == 0.0");
    let w = sat("d * 3.0 == 7.5");
    assert!(matches!(w["d"], Value::Double(v) if v * 3.0 == 7.5));
}

/// Host functions for the tests: `risk(x)` is `2 * x` and fails on negatives.
struct Host;
impl celspresso_eval::Functions for Host {
    fn call(&self, function: &str, args: &[Value]) -> Option<Result<Value, String>> {
        match (function, args) {
            ("risk", [Value::Int(x)]) if *x < 0 => Some(Err("negative".into())),
            ("risk", [Value::Int(x)]) => Some(x.checked_mul(2).map(Value::Int).ok_or_else(|| "overflow".into())),
            ("scale", [Value::Double(d)]) => Some(Ok(Value::Double(d * 2.0))),
            ("words", [Value::String(s)]) => Some(Ok(Value::list(s.split(' ').map(Value::str).collect()))),
            _ => None,
        }
    }
}

fn run_host(q: Query) -> Outcome {
    verify(&q, &[], Options::default(), &Host)
}

#[test]
fn host_functions_are_opaque() {
    // the solver can't see inside risk(), so a universal claim is UNKNOWN, naming it
    match run_host(Query::AlwaysTrue(&c("x < 0 || x > 1000 || risk(x) == 2 * x"))).status {
        Status::Unknown(r) => assert!(r.contains("'risk'") && r.contains("ensures=") && r.contains("env.define"), "{r}"),
        s => panic!("{s:?}"),
    }
    // the solver's guess at risk() is never checked against it and retried: one replay,
    // then UNKNOWN with the same actionable reason
    match run_host(Query::Satisfiable(&c("risk(x) == 7"))).status {
        Status::Unknown(r) => assert!(r.contains("'risk'"), "{r}"),
        s => panic!("{s:?}"),
    }
    // a witness that happens to replay is still real
    for src in ["risk(x) > 0 || x == 3", "scale(d) == 4.0 || d == 1.0", "size(words(s)) == 2 || s == 'a'"] {
        let _ = run_host(Query::Satisfiable(&c(src)));
    }
    // deterministic: equal arguments give equal results, with no call needed
    assert!(matches!(run_host(Query::Satisfiable(&c("risk(x) != risk(x + 0)"))).status, Status::NotFound));
}

/// `risk` tabulated on -2..=5 with its real values (an error below 0), as Python does it.
fn tabulated_schema() -> Arc<Schema> {
    use celspresso_syntax::Literal as L;
    let mut s = (*schema()).clone();
    let table = (-2..=5).map(|i| (vec![L::Int(i)], if i < 0 { None } else { Some(L::Int(2 * i)) })).collect();
    s.contracts.insert(
        "risk_int".into(),
        Arc::new(celspresso_check::Contract { params: vec!["x".into()], ensures: None, total: false, table: Some(table) }),
    );
    Arc::new(s)
}

#[test]
fn tabulated_functions_are_exact_on_their_table() {
    let s = tabulated_schema();
    let c = |src: &str| check(celspresso_syntax::parse(src).unwrap(), s.clone()).unwrap();
    let go = |src: &str, kind: &str| {
        let e = c(src);
        let q = match kind {
            "prove" => Query::AlwaysTrue(&e),
            "sat" => Query::Satisfiable(&e),
            _ => Query::CanError(&e),
        };
        verify(&q, &[], Options::default(), &Host).status
    };
    // on the table: proofs, witnesses and errors are exact
    assert!(matches!(go("x < 0 || x > 5 || risk(x) == 2 * x", "prove"), Status::NotFound));
    match go("x >= 0 && x <= 5 && risk(x) == 8", "sat") {
        Status::Found(w) => assert_eq!(w["x"], Value::Int(4)),
        st => panic!("{st:?}"),
    }
    assert!(matches!(go("x >= 0 && x <= 5 && risk(x) == 7", "sat"), Status::NotFound));
    match go("x >= -2 && x <= 5 && risk(x) > 0", "error") {
        Status::Found(w) => assert!(matches!(w["x"], Value::Int(-2 | -1)), "{w:?}"),
        st => panic!("{st:?}"),
    }
    // off the table it is opaque again, and the reason says so
    match go("x < 0 || risk(x) == 2 * x", "prove") {
        Status::Unknown(r) => assert!(r.contains("outside its tabulated inputs"), "{r}"),
        st => panic!("{st:?}"),
    }
}

#[test]
fn list_aggregates() {
    exact("[1, 5, 3].sum() == 9 && [1, 5, 3].min() == 1 && [1, 5, 3].max() == 5");
    exact("[2u, 3u].sum() == 5u && [7u].max() == 7u");
    exact("bxs.size() == 0 || bxs.min() <= bxs.max()");
    assert!(matches!(run(Query::CanError(&c("bxs.max() > 0"))).status, Status::Found(_)));
    assert!(matches!(run(Query::CanError(&c("bxs.sum() > 0"))).status, Status::Found(_)));
    // overflow
}

#[test]
fn input_shapes_and_constraints() {
    exact("code >= 1 && code <= 9 && level in [1, 2, 3] && n >= 0u");
    unsat("code == 0 || code == 10 || level == 4");
    let w = sat("zip.startsWith('9')");
    assert!(matches!(&w["zip"], Value::String(z) if z.len() == 5 && z.starts_with('9') && z.chars().all(|c| c.is_ascii_digit())));
    unsat("zip.contains('a')");
    exact("size(flags) >= 1 && size(tags) >= 1");
    let w = sat("flags[0] && tags.exists(k, tags[k])");
    assert!(matches!(&w["flags"], Value::List(l) if !l.is_empty()));
    let w = sat("n > 5u && uint(x) == n");
    assert!(matches!((&w["n"], &w["x"]), (Value::Uint(a), Value::Int(b)) if *a as i64 == *b));
    // unmodeled pieces stay sound: fresh values of every shape, UNKNOWN verdicts
    for src in
        ["string(d) == s", "s.lowerAscii() == s", "blob == b'abc'", "words(s).size() >= 0", "optional.ofNonZeroValue(blob).hasValue()"]
    {
        assert!(matches!(run(Query::AlwaysTrue(&c(src))).status, Status::Unknown(_) | Status::Found(_)), "{src}");
    }
}

#[test]
fn bounds_of_numeric_expressions() {
    let b = |src: &str| bounds(&c(src), &[], Options::default(), &NoFunctions);
    let r = b("user.tier == 'pro' ? 1000 : 10");
    let (lo, hi) = (r.min.unwrap(), r.max.unwrap());
    assert_eq!((lo.value.clone(), hi.value.clone()), (Value::Int(10), Value::Int(1000)));
    assert!(lo.sound && lo.attained && hi.sound && hi.attained && r.reason.is_none());
    assert!(matches!(&hi.witness["user"], Value::Struct(u) if u.fields["tier"] == Value::str("pro")));
    // schema constraints bound inputs; errors (here: overflow) are excluded
    let r = b("user.age * 2 + 1");
    assert_eq!((r.min.unwrap().value, r.max.unwrap().value), (Value::Int(1), Value::Int(301)));
    let r = b("x + 1");
    assert_eq!(r.max.unwrap().value, Value::Int(i64::MAX));
    let r = b("size(user.roles)");
    assert_eq!((r.min.unwrap().value, r.max.unwrap().value), (Value::Int(0), Value::Int(3)));
    // assumptions narrow the range
    let a = c("x >= 3 && x <= 7");
    let r = bounds(&c("x * x"), &[&a], Options::default(), &NoFunctions);
    assert_eq!((r.min.unwrap().value, r.max.unwrap().value), (Value::Int(9), Value::Int(49)));
    // dates and durations
    let r = b("user.born.daysUntil(date('2024-01-01'))");
    assert!(r.min.is_some_and(|m| m.sound));
    // unbounded collections: the bound is not sound, and the reason says why
    let r = b("size(xs)");
    assert!(!r.max.unwrap().sound && r.reason.unwrap().contains("unroll"));
    assert!(b("s").reason.unwrap().contains("integer-valued"));
    assert!(b("1 / 0").reason.unwrap().contains("errors on every"));
}

#[test]
fn index_of_matches_the_evaluator() {
    let cases = [
        "'hello world'.indexOf('o')",
        "'hello world'.indexOf('o', 5)",
        "'hello'.indexOf('z')",
        "'hello'.indexOf('')",
        "'hello'.indexOf('', 5)",
        "'hello'.indexOf('lo', 4)",
        "'ab'.indexOf('abc')",
        "'héllo wörld'.indexOf('l')",
        "'héllo wörld'.indexOf('ö')",
        "'hello world'.lastIndexOf('o')",
        "'hello world'.lastIndexOf('o', 6)",
        "'hello world'.lastIndexOf('o', 7)",
        "'hello'.lastIndexOf('')",
        "'hello'.lastIndexOf('', 2)",
        "'hello'.lastIndexOf('l', 0)",
        "'aaa'.lastIndexOf('aa')",
        "'aaa'.lastIndexOf('aa', 0)",
        "'ab'.lastIndexOf('abc')",
        "'héllo'.lastIndexOf('l', 3)",
        "size('héllo wörld'.substring(2, 8))",
        "'héllo wörld'.substring(7).indexOf('r')",
        "'abc'.substring(3).size()",
        "'héllo'.charAt(1).size() + 'héllo'.charAt(5).size() * 10",
        "'héllo'.indexOf('héllo'.charAt(4))",
    ];
    for src in cases {
        let want = celspresso_eval::evaluate(&c(src), &BTreeMap::new(), &NoFunctions, celspresso_eval::Limits::default());
        let Ok(Value::Int(n)) = want else { panic!("{src}: {want:?}") };
        exact(&format!("{src} == {n}"));
    }
    exact("'héllo wörld'.substring(1, 4) == 'éll' && 'abc'.substring(1) == 'bc' && 'abc'.substring(2, 2) == ''");
    for src in [
        "'abc'.charAt(4) == ''",
        "'abc'.charAt(-1) == ''",
        "'abc'.substring(2, 1) == ''",
        "'abc'.substring(4) == ''",
        "'abc'.substring(0, 4) == ''",
        "'abc'.substring(-1) == ''",
    ] {
        assert!(matches!(run(Query::CanError(&c(src))).status, Status::Found(_)), "{src}");
    }
    for src in ["'hello'.indexOf('l', 6) == 0", "'hello'.indexOf('l', -1) == 0", "'hello'.lastIndexOf('l', 6) == 0"] {
        assert!(matches!(run(Query::CanError(&c(src))).status, Status::Found(_)), "{src}");
    }
    // symbolic: a found index really is an occurrence, and the first one
    exact("s.indexOf('@') == -1 || s.charAt(s.indexOf('@')) == '@'");
    exact("s.indexOf('@') < 0 || !s.substring(0, s.indexOf('@')).contains('@')");
    exact("!s.contains('-') || s.substring(0, s.indexOf('-')).size() < s.size()");
    exact("(s.indexOf('ab') >= 0) == s.contains('ab')");
    exact("s.lastIndexOf('a') >= s.indexOf('a')");
    exact("(s.lastIndexOf('x') == -1) == (s.indexOf('x') == -1)");
    let w = sat("s.substring(0, s.indexOf('-')) == 'CPT' && s.size() == 9");
    assert!(matches!(&w["s"], Value::String(v) if v.starts_with("CPT-") && v.chars().count() == 9));
    let w = sat("s.indexOf('@') > 2 && s.endsWith('.com') && size(s) < 10");
    assert!(matches!(&w["s"], Value::String(v) if v.find('@').is_some_and(|i| v[..i].chars().count() > 2) && v.ends_with(".com")));
    assert!(matches!(run(Query::CanError(&c("s.indexOf('x', x) >= 0"))).status, Status::Found(_)));
}

#[test]
fn unknown_reasons_name_unmodeled_builtins() {
    // a builtin the verifier doesn't model: say so, and never suggest a contract for it
    for (src, name) in [("s.trim() == 'b'", "'trim'"), ("s.replace('a', 'b') == 'bb'", "'replace'")] {
        match run(Query::Satisfiable(&c(src))).status {
            Status::Unknown(r) => {
                assert!(r.contains(name) && r.contains("doesn't model") && !r.contains("ensures") && !r.contains("internal"), "{r}")
            }
            st => panic!("{src}: {st:?}"),
        }
    }
    // a builtin and a host function together: both named, each with its own advice
    match run_host(Query::Satisfiable(&c("risk(x) == 3 && s.trim() == 'b'"))).status {
        Status::Unknown(r) => assert!(r.contains("'trim'") && r.contains("it also depends on what 'risk' returns"), "{r}"),
        st => panic!("{st:?}"),
    }
}

#[test]
fn operator_names_in_reasons_are_as_written() {
    // a builtin operator on unmodeled operands is named as in the source, never '_>_'
    match run(Query::Satisfiable(&c("[1] + [2] == [3] && s.split(' ').size() > 1"))).status {
        Status::Unknown(r) => assert!(!r.contains("'_"), "{r}"),
        st => panic!("{st:?}"),
    }
}

#[test]
fn math_greatest_and_least() {
    proved("math.greatest(x, y) >= x && math.greatest(x, y) >= y");
    proved("math.least(x, y, 3) <= 3");
    proved("math.greatest(x, y) == (x > y ? x : y)");
    proved("math.greatest(5) == 5");
    proved("x == -9223372036854775807 - 1 || math.abs(x) >= 0");
    let w = refuted("math.abs(x) >= 0"); // abs(i64 min) overflows
    assert_eq!(w["x"], Value::Int(i64::MIN));
    let w = refuted("math.least(x, y) == x");
    assert!(matches!((&w["x"], &w["y"]), (Value::Int(a), Value::Int(b)) if b < a));
    // over a list: errors when empty, like the evaluator
    proved("math.greatest([x, y]) == math.greatest(x, y)");
    assert!(matches!(run(Query::CanError(&c("math.greatest(xs)"))).status, Status::Found(_)));
    // still unmodeled: reported as a builtin, never with advice meant for host functions
    match run(Query::Satisfiable(&c("math.greatest(1.5, double(x)) > 2.0"))).status {
        Status::Unknown(r) => assert!(r.contains("'math.greatest'") && !r.contains("ensures") && r.contains("doesn't model"), "{r}"),
        st => panic!("{st:?}"),
    }
}
