use crate::*;

fn roundtrip(src: &str) -> String {
    unparse(&parse(src).unwrap_or_else(|e| panic!("parse {src:?}: {e}")))
}

#[test]
fn precedence_and_unparse() {
    assert_eq!(roundtrip("1 + 2 * 3"), "1 + 2 * 3");
    assert_eq!(roundtrip("(1 + 2) * 3"), "(1 + 2) * 3");
    assert_eq!(roundtrip("a || b && c"), "a || b && c");
    assert_eq!(roundtrip("(a || b) && c"), "(a || b) && c");
    assert_eq!(roundtrip("a ? b : c ? d : e"), "a ? b : c ? d : e");
    assert_eq!(roundtrip("!a.b"), "!a.b");
    assert_eq!(roundtrip("-x"), "-x");
    assert_eq!(roundtrip("1 - (2 - 3)"), "1 - (2 - 3)");
    assert_eq!(roundtrip("user.age >= 18 && 'admin' in user.roles"), "user.age >= 18 && \"admin\" in user.roles");
}

#[test]
fn literals() {
    assert_eq!(roundtrip("-9223372036854775808"), "-9223372036854775808");
    assert!(parse("9223372036854775808").is_err());
    assert_eq!(roundtrip("18446744073709551615u"), "18446744073709551615u");
    assert_eq!(roundtrip("0x1F"), "31");
    assert_eq!(roundtrip("1.5e3"), "1500.0");
    assert_eq!(roundtrip(r#"'a\n\x41é'"#), "\"a\\nAé\"");
    assert_eq!(roundtrip(r#"r'\d+'"#), r#""\\d+""#);
    assert_eq!(roundtrip(r#"b'\xff'"#), r#"b"\xff""#);
    assert_eq!(roundtrip("'''multi\nline'''"), "\"multi\\nline\"");
    assert_eq!(roundtrip("[1, 2][0]"), "[1, 2][0]");
    assert_eq!(roundtrip("{'a': 1}"), "{\"a\": 1}");
    assert_eq!(roundtrip("pkg.Msg{x: 1}"), "pkg.Msg{x: 1}");
}

#[test]
fn macros_roundtrip() {
    for src in [
        "xs.all(x, x > 0)",
        "xs.exists(x, x > 0)",
        "xs.exists_one(x, x > 0)",
        "xs.map(x, x * 2)",
        "xs.map(x, x > 0, x * 2)",
        "xs.filter(x, x > 0)",
        "has(user.name)",
        "xs.all(i, x, x > i)",
        "m.transformMap(k, v, v + 1)",
        "m.transformList(k, v, k > 0, v)",
        "cel.bind(x, 1, x + 1)",
        "xs.sortBy(e, -e)",
        "m.?a.b[?0]",
        "[?a, b]",
        r#"{?"k": v, "j": w}"#,
        "cel.block([1, cel.index(0) + 1], [cel.index(1)].map(cel.iterVar(0, 0), cel.iterVar(0, 0) * 2))",
        "o.optMap(x, x + 1).optFlatMap(y, optional.of(y)) == optional.none()",
    ] {
        assert_eq!(roundtrip(src), src);
    }
}

#[test]
fn errors_have_spans() {
    let e = parse("a +").unwrap_err();
    assert_eq!(e.span, Span::new(3, 3));
    let e = parse("a.all(1, true)").unwrap_err();
    assert!(e.message.contains("simple identifier"));
    let e = parse("if").unwrap_err();
    assert!(e.message.contains("reserved"));
    let e = parse("'abc").unwrap_err();
    assert!(e.message.contains("unterminated"));
}

#[test]
fn depth_limit() {
    let src = "(".repeat(500) + "1" + &")".repeat(500);
    assert!(parse(&src).unwrap_err().message.contains("depth"));
}

#[test]
fn diagnostic_rendering() {
    let r = render_diagnostic("user.agee >= 18", Span::new(0, 9), "undefined field 'agee'");
    assert_eq!(r, "1:1: undefined field 'agee'\n  | user.agee >= 18\n  | ^^^^^^^^^");
}

#[test]
fn unique_ids() {
    let e = parse("xs.map(x, x > 0, x * 2) + [a.b[c]]").unwrap();
    let mut ids = std::collections::HashSet::new();
    e.walk(&mut |n| assert!(ids.insert(n.id), "duplicate id {}", n.id));
}

#[test]
fn macro_copies_have_fresh_ids() {
    for src in ["a.b.sortBy(e, e)", "a.b.optMap(x, x)"] {
        let e = parse(src).unwrap();
        let mut ids = Vec::new();
        e.walk(&mut |n| ids.push(n.id));
        let n = ids.len();
        ids.sort_unstable();
        ids.dedup();
        assert_eq!(ids.len(), n, "{src}");
    }
}
