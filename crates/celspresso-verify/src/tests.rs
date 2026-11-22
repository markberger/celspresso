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
    for (n, t) in [("user", CelType::Struct("User".into())), ("x", CelType::Int), ("y", CelType::Int), ("s", CelType::String), ("xs", CelType::list(CelType::Int)), ("today", CelType::Date)] {
        s.vars.insert(n.into(), VarDecl { name: n.into(), ty: t, constraints: Default::default() });
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
    // `s` and `user` appear only under approximated optionals, so the solver's model
    // omits them; an unbound variable must not be read as "the predicate failed"
    for src in ["optional.of(s).hasValue()", "optional.of(user).hasValue()", "optional.of(s).orValue('') == s"] {
        match run(Query::AlwaysTrue(&c(src))).status {
            Status::Unknown(_) => {}
            s => panic!("{src}: expected UNKNOWN, got {s:?}"),
        }
    }
    // any counterexample that is reported must carry every variable and replay
    if let Status::Found(w) = run(Query::AlwaysTrue(&c("optional.of(s).hasValue() && x > 0"))).status {
        assert!(w.contains_key("s") && w.contains_key("x"));
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
