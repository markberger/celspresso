use crate::*;
use celspresso_check::{check, CelType, Schema, VarDecl};
use std::collections::HashMap;
use std::sync::Arc;

fn run(src: &str, vars: &[(&str, CelType, Value)]) -> Result<Value, String> {
    let mut s = Schema::with_stdlib();
    let mut act = HashMap::new();
    for (n, t, v) in vars {
        s.vars.insert(n.to_string(), VarDecl { name: n.to_string(), ty: t.clone(), constraints: Default::default() });
        act.insert(n.to_string(), v.clone());
    }
    let c = check(celspresso_syntax::parse(src).unwrap(), Arc::new(s)).map_err(|e| format!("check: {}", e[0].message))?;
    evaluate(&c, &act, &NoFunctions, Limits::default()).map_err(|e| e.message)
}

fn ok(src: &str) -> String {
    run(src, &[]).unwrap_or_else(|e| panic!("{src}: {e}")).to_string()
}

fn fails(src: &str) -> String {
    run(src, &[]).expect_err(src)
}

#[test]
fn arithmetic() {
    assert_eq!(ok("1 + 2 * 3"), "7");
    assert_eq!(ok("-7 / 2"), "-3");
    assert_eq!(ok("-7 % 2"), "-1");
    assert_eq!(ok("7 / -2"), "-3");
    assert_eq!(fails("1 / 0"), "division by zero");
    assert_eq!(fails("9223372036854775807 + 1"), "integer overflow");
    assert_eq!(fails("-9223372036854775808 / -1"), "integer overflow");
    assert_eq!(fails("1u - 2u"), "integer overflow");
    assert_eq!(ok("1.5 * 2.0"), "3.0");
}

#[test]
fn logic_absorbs_errors() {
    assert_eq!(ok("1/0 == 1 && false"), "false");
    assert_eq!(ok("false && 1/0 == 1"), "false");
    assert_eq!(ok("1/0 == 1 || true"), "true");
    assert_eq!(fails("1/0 == 1 && true"), "division by zero");
    assert_eq!(ok("[0, 1, -1].all(x, 1 / x > 0)"), "false");
    assert_eq!(fails("[1, 0].all(x, 1 / x > 0)"), "division by zero");
    assert_eq!(ok("[0, 1].exists(x, 1 / x > 0)"), "true");
}

#[test]
fn equality_and_ordering() {
    assert_eq!(ok("1 < 2.5"), "true");
    assert_eq!(ok("[1, 2] == [1, 2]"), "true");
    assert_eq!(ok("{'a': 1} == {'a': 1}"), "true");
    assert_eq!(ok("dyn(1) == dyn(1.0)"), "true");
    assert_eq!(ok("dyn(1) == dyn(1u)"), "true");
    assert_eq!(ok("'abc' < 'abd'"), "true");
}

#[test]
fn strings_and_lists() {
    assert_eq!(ok("size('héllo')"), "5");
    assert_eq!(ok("'hello'.startsWith('he') && 'hello'.contains('ll')"), "true");
    assert_eq!(ok("'abc123'.matches('^[a-z]+[0-9]+$')"), "true");
    assert_eq!(ok("[1, 2, 3].map(x, x * 2)"), "[2, 4, 6]");
    assert_eq!(ok("[1, 2, 3].filter(x, x > 1)"), "[2, 3]");
    assert_eq!(ok("[1, 2, 3].exists_one(x, x > 2)"), "true");
    assert_eq!(ok("[1, 2, 3].sum()"), "6");
    assert_eq!(ok("[3, 1, 2].min()"), "1");
    assert_eq!(fails("[1][1]"), "index out of range: 1");
    assert_eq!(fails("{'a': 1}['b']"), "no such key: \"b\"");
    assert_eq!(ok("2 in [1, 2]"), "true");
    assert_eq!(ok("'a' in {'a': 1}"), "true");
}

#[test]
fn conversions() {
    assert_eq!(ok("int('42') + 1"), "43");
    assert_eq!(ok("int(2.9)"), "2");
    assert_eq!(fails("int(1e20)"), "int range error");
    assert_eq!(ok("string(42)"), "\"42\"");
    assert_eq!(ok("uint(3)"), "3u");
}

#[test]
fn dates() {
    assert_eq!(ok("date('2000-02-29').ageOn(date('2018-03-01'))"), "18");
    assert_eq!(ok("date('2024-01-01') + 31"), "date(\"2024-02-01\")");
    assert_eq!(ok("date('2024-03-01') - date('2024-02-01')"), "29");
    assert_eq!(ok("date('2024-03-01') > date('2024-02-01')"), "true");
}

#[test]
fn variables_and_limits() {
    let xs = Value::list((0..10).map(Value::Int).collect());
    let r = run("xs.map(x, x * x).sum()", &[("xs", CelType::list(CelType::Int), xs)]).unwrap();
    assert_eq!(r.to_string(), "285");
    let mut s = Schema::with_stdlib();
    s.vars.insert("n".into(), VarDecl { name: "n".into(), ty: CelType::Int, constraints: Default::default() });
    let c = check(celspresso_syntax::parse("[1,2,3,4,5,6,7,8,9,10].map(x, [1,2,3,4,5,6,7,8,9,10].map(y, x * y))").unwrap(), Arc::new(s))
        .unwrap();
    let limits = Limits { max_iterations: 50, ..Limits::default() };
    let r = evaluate(&c, &HashMap::new(), &NoFunctions, limits);
    assert_eq!(r.unwrap_err().message, "comprehension iteration limit exceeded");
}
