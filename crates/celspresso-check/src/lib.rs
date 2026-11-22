//! CEL type system, declarations and checker.

pub mod checker;
pub mod decls;
pub mod types;

pub use checker::{check, suggest, CheckError, CheckedExpr, Reference};
pub use decls::{Constraints, FieldDecl, FunctionDecl, Overload, Schema, StructDecl, VarDecl};
pub use types::CelType;

use celspresso_syntax::ast::{Expr, ExprKind};
use std::collections::{BTreeMap, HashSet};

/// Inline named definitions (`env.define("age", "...")`) into `expr`.
///
/// Each use of a definition name that is not shadowed by a comprehension
/// variable is replaced by a copy of the definition body with fresh ids. The
/// copied nodes take the span of the identifier they replace, so diagnostics
/// point at the use site.
pub fn expand_definitions(expr: Expr, defs: &BTreeMap<String, Expr>) -> Expr {
    if defs.is_empty() {
        return expr;
    }
    let mut next = expr.max_id() + 1;
    let mut bound = Vec::new();
    expand(expr, defs, &mut next, &mut bound, &mut HashSet::new())
}

fn expand(e: Expr, defs: &BTreeMap<String, Expr>, next: &mut u32, bound: &mut Vec<String>, active: &mut HashSet<String>) -> Expr {
    let Expr { id, span, kind } = e;
    let kind = match kind {
        ExprKind::Ident(name) if !bound.contains(&name) && defs.contains_key(&name) && !active.contains(&name) => {
            let body = defs[&name].clone();
            active.insert(name.clone());
            let mut outer_bound = Vec::new();
            let mut b = expand(body, defs, next, &mut outer_bound, active);
            active.remove(&name);
            renumber(&mut b, next, span);
            return b;
        }
        ExprKind::Select { operand, field, test_only } => {
            ExprKind::Select { operand: Box::new(expand(*operand, defs, next, bound, active)), field, test_only }
        }
        ExprKind::Call { target, function, args } => ExprKind::Call {
            target: target.map(|t| Box::new(expand(*t, defs, next, bound, active))),
            function,
            args: args.into_iter().map(|a| expand(a, defs, next, bound, active)).collect(),
        },
        ExprKind::List(items) => ExprKind::List(items.into_iter().map(|a| expand(a, defs, next, bound, active)).collect()),
        ExprKind::Map(entries) => ExprKind::Map(
            entries
                .into_iter()
                .map(|(k, v)| (expand(k, defs, next, bound, active), expand(v, defs, next, bound, active)))
                .collect(),
        ),
        ExprKind::Struct { type_name, fields } => ExprKind::Struct {
            type_name,
            fields: fields.into_iter().map(|(k, v)| (k, expand(v, defs, next, bound, active))).collect(),
        },
        ExprKind::Comprehension(c) => {
            let mut c = *c;
            c.iter_range = expand(c.iter_range, defs, next, bound, active);
            c.accu_init = expand(c.accu_init, defs, next, bound, active);
            bound.push(c.accu_var.clone());
            bound.push(c.iter_var.clone());
            c.loop_condition = expand(c.loop_condition, defs, next, bound, active);
            c.loop_step = expand(c.loop_step, defs, next, bound, active);
            c.result = expand(c.result, defs, next, bound, active);
            bound.pop();
            bound.pop();
            ExprKind::Comprehension(Box::new(c))
        }
        k => k,
    };
    Expr { id, span, kind }
}

fn renumber(e: &mut Expr, next: &mut u32, span: celspresso_syntax::Span) {
    e.id = *next;
    *next += 1;
    e.span = span;
    match &mut e.kind {
        ExprKind::Select { operand, .. } => renumber(operand, next, span),
        ExprKind::Call { target, args, .. } => {
            if let Some(t) = target {
                renumber(t, next, span);
            }
            args.iter_mut().for_each(|a| renumber(a, next, span));
        }
        ExprKind::List(items) => items.iter_mut().for_each(|a| renumber(a, next, span)),
        ExprKind::Map(entries) => entries.iter_mut().for_each(|(k, v)| {
            renumber(k, next, span);
            renumber(v, next, span)
        }),
        ExprKind::Struct { fields, .. } => fields.iter_mut().for_each(|(_, v)| renumber(v, next, span)),
        ExprKind::Comprehension(c) => {
            renumber(&mut c.iter_range, next, span);
            renumber(&mut c.accu_init, next, span);
            renumber(&mut c.loop_condition, next, span);
            renumber(&mut c.loop_step, next, span);
            renumber(&mut c.result, next, span);
        }
        _ => {}
    }
}

#[cfg(test)]
mod tests;
