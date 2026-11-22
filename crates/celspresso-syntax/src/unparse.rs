//! AST -> canonical CEL source. Macros are re-sugared from their comprehensions.

use crate::ast::*;

pub fn unparse(e: &Expr) -> String {
    let mut s = String::new();
    write_expr(&mut s, e, 0);
    s
}

fn prec(function: &str) -> Option<(u8, &'static str)> {
    Some(match function {
        ops::CONDITIONAL => (1, ""),
        ops::LOGICAL_OR => (2, " || "),
        ops::LOGICAL_AND => (3, " && "),
        ops::EQUALS => (4, " == "),
        ops::NOT_EQUALS => (4, " != "),
        ops::LESS => (4, " < "),
        ops::LESS_EQUALS => (4, " <= "),
        ops::GREATER => (4, " > "),
        ops::GREATER_EQUALS => (4, " >= "),
        ops::IN => (4, " in "),
        ops::ADD => (5, " + "),
        ops::SUBTRACT => (5, " - "),
        ops::MULTIPLY => (6, " * "),
        ops::DIVIDE => (6, " / "),
        ops::MODULO => (6, " % "),
        ops::LOGICAL_NOT | ops::NEGATE => (7, ""),
        _ => return None,
    })
}

/// Recognize the expansion of `t.optMap(x, e)` / `t.optFlatMap(x, e)`.
fn opt_map(e: &Expr) -> Option<(&Expr, &Comprehension)> {
    let (ops::CONDITIONAL, [has, then, _]) = call_args(e)? else { return None };
    let ExprKind::Call { target: Some(t), function, .. } = &has.kind else { return None };
    if function != "hasValue" {
        return None;
    }
    let inner = match call_args(then) {
        Some(("optional.of", [x])) => x,
        _ => then,
    };
    match &inner.kind {
        ExprKind::Comprehension(c) if c.macro_name == "optMap" || c.macro_name == "optFlatMap" => Some((t, c)),
        _ => None,
    }
}

fn expr_prec(e: &Expr) -> u8 {
    if opt_map(e).is_some() {
        return 8;
    }
    match &e.kind {
        ExprKind::Call { target: None, function, .. } => prec(function).map(|p| p.0).unwrap_or(8),
        ExprKind::Literal(Literal::Int(i)) if *i < 0 => 7,
        ExprKind::Literal(Literal::Double(d)) if *d < 0.0 => 7,
        _ => 8,
    }
}

const SORT_BY: &str = "@sortByAssociatedKeys";

fn write_expr(s: &mut String, e: &Expr, min_prec: u8) {
    let p = expr_prec(e);
    let paren = p < min_prec;
    if paren {
        s.push('(');
    }
    write_inner(s, e);
    if paren {
        s.push(')');
    }
}

fn write_list(s: &mut String, items: &[Expr]) {
    for (i, a) in items.iter().enumerate() {
        if i > 0 {
            s.push_str(", ");
        }
        write_entry(s, a);
    }
}

/// A list element or map value, with the `?` of an optional entry restored.
fn write_entry(s: &mut String, e: &Expr) {
    match call_args(e) {
        Some((ops::OPT_ENTRY, [x])) => {
            s.push('?');
            write_expr(s, x, 0);
        }
        _ => write_expr(s, e, 0),
    }
}

fn write_inner(s: &mut String, e: &Expr) {
    if let Some((t, c)) = opt_map(e) {
        write_expr(s, t, 8);
        s.push('.');
        s.push_str(&c.macro_name);
        s.push('(');
        s.push_str(&ident_source(&c.accu_var));
        s.push_str(", ");
        write_expr(s, &c.result, 0);
        s.push(')');
        return;
    }
    match &e.kind {
        ExprKind::Literal(l) => s.push_str(&l.to_string()),
        ExprKind::Ident(n) => s.push_str(&ident_source(n)),
        ExprKind::Select { operand, field, test_only } => {
            if *test_only {
                s.push_str("has(");
            }
            write_expr(s, operand, 8);
            s.push('.');
            s.push_str(field);
            if *test_only {
                s.push(')');
            }
        }
        ExprKind::Call { target: Some(t), function, args } => {
            write_expr(s, t, 8);
            s.push('.');
            s.push_str(function);
            s.push('(');
            write_list(s, args);
            s.push(')');
        }
        ExprKind::Call { target: None, function, args } => match (function.as_str(), args.as_slice()) {
            (ops::CONDITIONAL, [c, t, f]) => {
                write_expr(s, c, 2);
                s.push_str(" ? ");
                write_expr(s, t, 2);
                s.push_str(" : ");
                write_expr(s, f, 1);
            }
            (ops::LOGICAL_NOT, [a]) => {
                s.push('!');
                write_expr(s, a, 7);
            }
            (ops::NEGATE, [a]) => {
                s.push('-');
                write_expr(s, a, 7);
            }
            // xs.sortBy(e, key) expands to @sortByAssociatedKeys(xs, xs.map(e, key))
            (SORT_BY, [_, keys]) if matches!(&keys.kind, ExprKind::Comprehension(c) if c.macro_name == "map") => {
                let ExprKind::Comprehension(c) = &keys.kind else { unreachable!() };
                write_expr(s, &c.iter_range, 8);
                s.push_str(".sortBy(");
                s.push_str(&ident_source(&c.iter_var));
                s.push_str(", ");
                if let Some((_, [_, single])) = call_args(&c.loop_step) {
                    if let ExprKind::List(items) = &single.kind {
                        if let Some(k) = items.first() {
                            write_expr(s, k, 0);
                        }
                    }
                }
                s.push(')');
            }
            (ops::INDEX | ops::OPT_INDEX, [a, i]) => {
                write_expr(s, a, 8);
                s.push_str(if function == ops::INDEX { "[" } else { "[?" });
                write_expr(s, i, 0);
                s.push(']');
            }
            (ops::OPT_SELECT, [a, f]) if matches!(&f.kind, ExprKind::Literal(Literal::String(_))) => {
                let ExprKind::Literal(Literal::String(f)) = &f.kind else { unreachable!() };
                write_expr(s, a, 8);
                s.push_str(".?");
                s.push_str(f);
            }
            (f, [l, r]) if prec(f).is_some() => {
                let (p, sym) = prec(f).unwrap();
                write_expr(s, l, p);
                s.push_str(sym);
                // relations are non-associative in practice; keep left-assoc for the rest
                write_expr(s, r, p + 1);
            }
            (f, args) => {
                s.push_str(f);
                s.push('(');
                write_list(s, args);
                s.push(')');
            }
        },
        ExprKind::List(items) => {
            s.push('[');
            write_list(s, items);
            s.push(']');
        }
        ExprKind::Map(entries) => {
            s.push('{');
            for (i, (k, v)) in entries.iter().enumerate() {
                if i > 0 {
                    s.push_str(", ");
                }
                let optional = matches!(call_args(v), Some((ops::OPT_ENTRY, [_])));
                if optional {
                    s.push('?');
                }
                write_expr(s, k, 0);
                s.push_str(": ");
                match (optional, call_args(v)) {
                    (true, Some((_, [x]))) => write_expr(s, x, 0),
                    _ => write_expr(s, v, 0),
                }
            }
            s.push('}');
        }
        ExprKind::Struct { type_name, fields } => {
            s.push_str(type_name);
            s.push('{');
            for (i, (k, v)) in fields.iter().enumerate() {
                if i > 0 {
                    s.push_str(", ");
                }
                s.push_str(k);
                s.push_str(": ");
                write_expr(s, v, 0);
            }
            s.push('}');
        }
        ExprKind::Comprehension(c) => write_macro(s, c),
    }
}

fn call_args(e: &Expr) -> Option<(&str, &[Expr])> {
    match &e.kind {
        ExprKind::Call { target: None, function, args } => Some((function.as_str(), args.as_slice())),
        _ => None,
    }
}

/// Source spelling of an identifier, restoring `cel.block` variables.
fn ident_source(n: &str) -> String {
    if let Some(i) = n.strip_prefix(BLOCK_INDEX) {
        return format!("cel.index({i})");
    }
    for (prefix, f) in [(BLOCK_ITER, "iterVar"), (BLOCK_ACCU, "accuVar")] {
        if let Some((i, j)) = n.strip_prefix(prefix).and_then(|r| r.split_once(':')) {
            return format!("cel.{f}({i}, {j})");
        }
    }
    n.to_string()
}

fn write_macro(s: &mut String, c: &Comprehension) {
    if c.macro_name == "cel.block" {
        // a chain of nested binds: cel.block([e0, e1, ...], body)
        let mut inits = vec![&c.accu_init];
        let mut body = &c.result;
        while let ExprKind::Comprehension(inner) = &body.kind {
            if inner.macro_name != "cel.block" {
                break;
            }
            inits.push(&inner.accu_init);
            body = &inner.result;
        }
        s.push_str("cel.block([");
        for (i, e) in inits.iter().enumerate() {
            if i > 0 {
                s.push_str(", ");
            }
            write_expr(s, e, 0);
        }
        s.push_str("], ");
        write_expr(s, body, 0);
        s.push(')');
        return;
    }
    if c.macro_name == "cel.bind" {
        s.push_str("cel.bind(");
        s.push_str(&ident_source(&c.accu_var));
        s.push_str(", ");
        write_expr(s, &c.accu_init, 0);
        s.push_str(", ");
        write_expr(s, &c.result, 0);
        s.push(')');
        return;
    }
    write_expr(s, &c.iter_range, 8);
    s.push('.');
    s.push_str(&c.macro_name);
    s.push('(');
    s.push_str(&ident_source(&c.iter_var));
    s.push_str(", ");
    if let Some(v2) = &c.iter_var2 {
        s.push_str(&ident_source(v2));
        s.push_str(", ");
    }
    let step = &c.loop_step;
    match c.macro_name.as_str() {
        "all" | "exists" => {
            if let Some((_, [_, pred])) = call_args(step) {
                write_expr(s, pred, 0);
            }
        }
        "exists_one" => {
            if let Some((_, [pred, _, _])) = call_args(step) {
                write_expr(s, pred, 0);
            }
        }
        "filter" => {
            if let Some((_, [pred, _, _])) = call_args(step) {
                write_expr(s, pred, 0);
            }
        }
        "map" | "transformList" | "transformMap" | "transformMapEntry" => {
            let (filter, append) = match call_args(step) {
                Some((ops::CONDITIONAL, [f, app, _])) => (Some(f), app),
                _ => (None, step),
            };
            if let Some(f) = filter {
                write_expr(s, f, 0);
                s.push_str(", ");
            }
            match call_args(append) {
                // accu + [t]
                Some((ops::ADD, [_, single])) => {
                    if let ExprKind::List(items) = &single.kind {
                        if let Some(t) = items.first() {
                            write_expr(s, t, 0);
                        }
                    }
                }
                // @mapInsert(accu, k, t) or @mapInsert(accu, t)
                Some((ops::MAP_INSERT, [.., t])) => write_expr(s, t, 0),
                _ => {}
            }
        }
        _ => {}
    }
    s.push(')');
}
