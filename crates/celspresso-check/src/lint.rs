//! Warnings about expressions that type-check but are almost certainly wrong.
//!
//! Today: comparing a field whose schema restricts it to a few values (`Literal`, `Enum`,
//! `one_of`) against a literal outside that set, e.g. `order.tier == 'Gold'` when the tier
//! is `'standard' | 'gold'`. CEL accepts it; the branch can just never fire.

use crate::checker::{CheckError, CheckedExpr, Reference};
use crate::decls::Constraints;
use crate::CelType;
use celspresso_syntax::ast::{ops, Expr, ExprKind, Literal};

pub fn lint(c: &CheckedExpr) -> Vec<CheckError> {
    let mut out = Vec::new();
    c.expr.walk(&mut |e| {
        let ExprKind::Call { target: None, function, args } = &e.kind else { return };
        match (function.as_str(), args.as_slice()) {
            (ops::EQUALS | ops::NOT_EQUALS, [a, b]) => {
                let (path, lit) = match (&a.kind, &b.kind) {
                    (_, ExprKind::Literal(l)) => (a, l),
                    (ExprKind::Literal(l), _) => (b, l),
                    _ => return,
                };
                if let Some((name, opts)) = restricted(c, path) {
                    if !matches!(lit, Literal::Null) && !opts.iter().any(|o| same(o, lit)) {
                        let always = if function == ops::EQUALS { "never true" } else { "always true" };
                        out.push(warn(
                            e,
                            format!("{} is not a possible value of {name} ({}), so this comparison is {always}", text(lit), one_of(opts)),
                        ));
                    }
                }
            }
            (ops::IN, [a, b]) => {
                let (Some((name, opts)), ExprKind::List(items)) = (restricted(c, a), &b.kind) else { return };
                for item in items {
                    if let ExprKind::Literal(lit) = &item.kind {
                        if !opts.iter().any(|o| same(o, lit)) {
                            out.push(warn(item, format!("{} is not a possible value of {name} ({})", text(lit), one_of(opts))));
                        }
                    }
                }
            }
            _ => {}
        }
    });
    out
}

fn warn(e: &Expr, message: String) -> CheckError {
    CheckError { message, span: e.span, expr_id: e.id }
}

/// `path` as written, and its allowed values, if the schema restricts it to a finite set.
fn restricted<'c>(c: &'c CheckedExpr, path: &Expr) -> Option<(String, &'c [Literal])> {
    let (name, cons) = constraints(c, path)?;
    cons.one_of.as_deref().map(|o| (name, o))
}

fn constraints<'c>(c: &'c CheckedExpr, e: &Expr) -> Option<(String, &'c Constraints)> {
    match &e.kind {
        ExprKind::Ident(n) => match c.refs.get(&e.id) {
            Some(Reference::Var(v)) => c.schema.vars.get(v).map(|d| (n.clone(), &d.constraints)),
            _ => None,
        },
        ExprKind::Select { operand, field, test_only: false } => {
            let base = path_name(c, operand)?;
            let CelType::Struct(s) = c.type_of(operand.id).non_null().clone() else { return None };
            let f = c.schema.structs.get(&s)?.field(field)?;
            Some((format!("{base}.{field}"), &f.constraints))
        }
        _ => None,
    }
}

/// A variable or field path (only those name a schema-declared value).
fn path_name(c: &CheckedExpr, e: &Expr) -> Option<String> {
    match &e.kind {
        ExprKind::Ident(n) => matches!(c.refs.get(&e.id), Some(Reference::Var(_))).then(|| n.clone()),
        ExprKind::Select { operand, field, test_only: false } => path_name(c, operand).map(|b| format!("{b}.{field}")),
        _ => None,
    }
}

fn same(a: &Literal, b: &Literal) -> bool {
    match (a, b) {
        (Literal::Int(x), Literal::Uint(y)) | (Literal::Uint(y), Literal::Int(x)) => *x >= 0 && *x as u64 == *y,
        (Literal::Int(x), Literal::Double(y)) | (Literal::Double(y), Literal::Int(x)) => *x as f64 == *y,
        _ => a == b,
    }
}

fn text(l: &Literal) -> String {
    match l {
        Literal::String(s) => format!("'{s}'"),
        Literal::Int(i) => i.to_string(),
        Literal::Uint(u) => format!("{u}u"),
        Literal::Double(d) => d.to_string(),
        Literal::Bool(b) => b.to_string(),
        other => format!("{other:?}"),
    }
}

fn one_of(opts: &[Literal]) -> String {
    format!("one of {}", opts.iter().map(text).collect::<Vec<_>>().join(", "))
}
