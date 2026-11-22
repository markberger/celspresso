use crate::*;
use celspresso_syntax::parse;
use std::sync::Arc;

fn schema() -> Arc<Schema> {
    let mut s = Schema::with_stdlib();
    s.structs.insert(
        "User".into(),
        StructDecl {
            name: "User".into(),
            fields: vec![
                FieldDecl { name: "age".into(), ty: CelType::Int, constraints: Default::default() },
                FieldDecl { name: "roles".into(), ty: CelType::list(CelType::String), constraints: Default::default() },
                FieldDecl { name: "nick".into(), ty: CelType::nullable(CelType::String), constraints: Default::default() },
            ],
        },
    );
    s.vars.insert("user".into(), VarDecl { name: "user".into(), ty: CelType::Struct("User".into()), constraints: Default::default() });
    s.vars.insert("xs".into(), VarDecl { name: "xs".into(), ty: CelType::list(CelType::Int), constraints: Default::default() });
    s.vars
        .insert("m".into(), VarDecl { name: "m".into(), ty: CelType::map(CelType::String, CelType::Int), constraints: Default::default() });
    s.vars.insert("d".into(), VarDecl { name: "d".into(), ty: CelType::Dyn, constraints: Default::default() });
    Arc::new(s)
}

fn ty(src: &str) -> String {
    match check(parse(src).unwrap(), schema()) {
        Ok(c) => c.output_type().to_string(),
        Err(es) => panic!("{src}: {}", es.iter().map(|e| e.message.clone()).collect::<Vec<_>>().join("; ")),
    }
}

fn err(src: &str) -> String {
    match check(parse(src).unwrap(), schema()) {
        Ok(c) => panic!("{src}: expected error, got {}", c.output_type()),
        Err(es) => es[0].message.clone(),
    }
}

#[test]
fn basics() {
    assert_eq!(ty("1 + 2"), "int");
    assert_eq!(ty("1u + 2u"), "uint");
    assert_eq!(ty("'a' + 'b'"), "string");
    assert_eq!(ty("user.age >= 18 && 'admin' in user.roles"), "bool");
    assert_eq!(ty("[1, 2, 3]"), "list(int)");
    assert_eq!(ty("[]"), "list(dyn)");
    assert_eq!(ty("{'a': 1}"), "map(string, int)");
    assert_eq!(ty("m['a'] + 1"), "int");
    assert_eq!(ty("m.a"), "int");
    assert_eq!(ty("size(user.roles) > 1"), "bool");
    assert_eq!(ty("user.roles.size()"), "int");
    assert_eq!(ty("true ? 1 : 2"), "int");
    assert_eq!(ty("d.foo.bar"), "dyn");
    assert_eq!(ty("1 < 2.0"), "bool");
    assert_eq!(ty("xs.sum()"), "int");
}

#[test]
fn nullable() {
    assert_eq!(ty("user.nick"), "string?");
    assert_eq!(ty("user.nick == null"), "bool");
    assert_eq!(ty("user.nick.startsWith('a')"), "bool");
    assert_eq!(ty("user.nick != null ? user.nick : 'anon'"), "string?");
}

#[test]
fn macros() {
    assert_eq!(ty("xs.all(x, x > 0)"), "bool");
    assert_eq!(ty("xs.exists_one(x, x > 0)"), "bool");
    assert_eq!(ty("xs.map(x, x * 2)"), "list(int)");
    assert_eq!(ty("xs.map(x, x > 0, string(x))"), "list(string)");
    assert_eq!(ty("xs.filter(x, x > 0)"), "list(int)");
    assert_eq!(ty("m.all(k, k.startsWith('a'))"), "bool");
    assert_eq!(ty("has(user.age)"), "bool");
    assert_eq!(ty("user.roles.map(r, size(r)).sum()"), "int");
}

#[test]
fn errors() {
    assert_eq!(err("user.agee"), "undefined field 'agee' on User (did you mean 'age'?)");
    assert_eq!(err("usr.age"), "undeclared reference to 'usr' (did you mean 'user'?)");
    assert_eq!(err("1 + 'a'"), "found no matching overload for '+' applied to '(int, string)'");
    assert_eq!(err("xs.all(x, x)"), "found no matching overload for '&&' applied to '(bool, int)'");
    assert_eq!(err("sise(xs)"), "undeclared reference to function 'sise' (did you mean 'size'?)");
    assert_eq!(err("user.age.foo"), "type 'int' does not support field selection");
    assert_eq!(err("1 == 'a'"), "found no matching overload for '==' applied to '(int, string)'");
}

#[test]
fn refs_and_paths() {
    let c = check(parse("user.age >= 18 && xs.exists(x, x == user.age)").unwrap(), schema()).unwrap();
    assert_eq!(c.references(), vec!["user.age".to_string(), "xs".to_string()]);
}

#[test]
fn definitions() {
    let mut defs = std::collections::BTreeMap::new();
    defs.insert("adult".to_string(), Definition::constant(parse("user.age >= 18").unwrap()));
    defs.insert("ok".to_string(), Definition::constant(parse("adult && size(user.roles) > 0").unwrap()));
    let e = expand_definitions(parse("ok || xs.exists(adult, adult > 1)").unwrap(), &defs);
    assert_eq!(celspresso_syntax::unparse(&e), "user.age >= 18 && size(user.roles) > 0 || xs.exists(adult, adult > 1)");
    let c = check(e, schema()).unwrap();
    assert_eq!(c.output_type().to_string(), "bool");
}

#[test]
fn parameterized_definitions() {
    let def =
        |params: &[&str], src: &str| Definition { params: Some(params.iter().map(|p| p.to_string()).collect()), body: parse(src).unwrap() };
    let mut defs = std::collections::BTreeMap::new();
    defs.insert("clamp".to_string(), def(&["v"], "v < 0 ? 0 : (v > 100 ? 100 : v)"));
    defs.insert("between".to_string(), def(&["x", "lo", "hi"], "x >= lo && x <= hi"));
    // a body comprehension variable named like an argument's variable, and an argument
    // that mentions a parameter name: hygiene keeps them apart
    defs.insert("anyAbove".to_string(), def(&["xs", "x"], "xs.exists(v, v > x)"));
    let e = expand_definitions(
        parse("clamp(user.age - 10) == 5 && between(user.age, 18, 65) && xs.exists(v, anyAbove(xs, v))").unwrap(),
        &defs,
    );
    let text = celspresso_syntax::unparse(&e);
    assert!(text.contains("@arg:clamp:v") && text.contains("@arg:anyAbove:x"), "{text}");
    let c = check(e, schema()).unwrap();
    assert_eq!(c.output_type().to_string(), "bool");
    // the wrong number of arguments is left as a call (and reported by the checker)
    let e = expand_definitions(parse("clamp(1, 2)").unwrap(), &defs);
    assert!(matches!(e.kind, celspresso_syntax::ast::ExprKind::Call { .. }));
}
