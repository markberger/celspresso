//! CEL type system, declarations and checker.

pub mod checker;
pub mod decls;
pub mod lint;
pub mod types;

pub use checker::{check, check_unchecked, display_fn, suggest, CheckError, CheckedExpr, Reference};
pub use decls::{is_builtin_overload, Constraints, Contract, FieldDecl, FunctionDecl, Overload, Schema, StructDecl, VarDecl};
pub use types::CelType;

use celspresso_syntax::ast::{Comprehension, Expr, ExprKind, Literal};
use std::collections::{BTreeMap, HashSet};

/// A named definition: a constant sub-expression (`params: None`, used as `name`) or a
/// function written in CEL (`params: Some([...])`, used as `name(arg, ...)`).
#[derive(Clone, Debug)]
pub struct Definition {
    pub params: Option<Vec<String>>,
    pub body: Expr,
}

impl Definition {
    pub fn constant(body: Expr) -> Self {
        Definition { params: None, body }
    }
}

/// Inline named definitions (`env.define("age", "...")`) into `expr`.
///
/// Each use of a definition name that is not shadowed by a comprehension
/// variable is replaced by a copy of the definition body with fresh ids. The
/// copied nodes take the span of the identifier they replace, so diagnostics
/// point at the use site.
///
/// A call `f(a, b)` of a definition with parameters `(x, y)` becomes
/// `cel.bind(@arg:f:x, a, cel.bind(@arg:f:y, b, body'))`, where `body'` refers to the
/// parameters by those names. Users can't spell them, so neither an argument nor the
/// body can capture the other's variables, and each argument is evaluated once.
pub fn expand_definitions(expr: Expr, defs: &BTreeMap<String, Definition>) -> Expr {
    if defs.is_empty() {
        return expr;
    }
    let mut next = expr.max_id() + 1;
    let mut bound = Vec::new();
    expand(expr, defs, &mut next, &mut bound, &mut HashSet::new())
}

fn hygienic(def: &str, param: &str) -> String {
    format!("@arg:{def}:{param}")
}

/// Rename free occurrences of `from` (not shadowed by an inner comprehension) to `to`.
fn rename(e: &mut Expr, from: &str, to: &str) {
    match &mut e.kind {
        ExprKind::Ident(n) if n == from => *n = to.to_string(),
        ExprKind::Select { operand, .. } => rename(operand, from, to),
        ExprKind::Call { target, args, .. } => {
            if let Some(t) = target {
                rename(t, from, to);
            }
            args.iter_mut().for_each(|a| rename(a, from, to));
        }
        ExprKind::List(items) => items.iter_mut().for_each(|a| rename(a, from, to)),
        ExprKind::Map(entries) => entries.iter_mut().for_each(|(k, v)| {
            rename(k, from, to);
            rename(v, from, to)
        }),
        ExprKind::Struct { fields, .. } => fields.iter_mut().for_each(|(_, v)| rename(v, from, to)),
        ExprKind::Comprehension(c) => {
            rename(&mut c.iter_range, from, to);
            rename(&mut c.accu_init, from, to);
            if c.accu_var == from || c.iter_var == from || c.iter_var2.as_deref() == Some(from) {
                return; // shadowed in the loop body
            }
            rename(&mut c.loop_condition, from, to);
            rename(&mut c.loop_step, from, to);
            rename(&mut c.result, from, to);
        }
        _ => {}
    }
}

fn bind(span: celspresso_syntax::Span, name: String, init: Expr, body: Expr) -> Expr {
    let mk = |kind| Expr { id: 0, span, kind };
    mk(ExprKind::Comprehension(Box::new(Comprehension {
        iter_var: "#unused".into(),
        iter_var2: None,
        iter_range: mk(ExprKind::List(vec![])),
        accu_var: name.clone(),
        accu_init: init,
        loop_condition: mk(ExprKind::Literal(Literal::Bool(false))),
        loop_step: mk(ExprKind::Ident(name)),
        result: body,
        macro_name: "cel.bind".into(),
    })))
}

fn expand(e: Expr, defs: &BTreeMap<String, Definition>, next: &mut u32, bound: &mut Vec<String>, active: &mut HashSet<String>) -> Expr {
    let Expr { id, span, kind } = e;
    let kind = match kind {
        ExprKind::Call { target: None, function, args }
            if !active.contains(&function)
                && defs.get(&function).and_then(|d| d.params.as_ref()).is_some_and(|p| p.len() == args.len()) =>
        {
            let def = &defs[&function];
            let params = def.params.as_ref().expect("checked above");
            let args: Vec<Expr> = args.into_iter().map(|a| expand(a, defs, next, bound, active)).collect();
            let mut body = def.body.clone();
            for p in params {
                rename(&mut body, p, &hygienic(&function, p));
            }
            active.insert(function.clone());
            let mut body = expand(body, defs, next, &mut Vec::new(), active);
            active.remove(&function);
            renumber(&mut body, next, span);
            // innermost binding first, so the outermost evaluates the first argument
            let mut out = body;
            for (p, a) in params.iter().zip(args).rev() {
                // arguments keep their own ids and spans; only the new wrapper is numbered
                out = bind(span, hygienic(&function, p), a, out);
                renumber_shell(&mut out, next);
            }
            return out;
        }
        ExprKind::Ident(name)
            if !bound.contains(&name) && defs.get(&name).is_some_and(|d| d.params.is_none()) && !active.contains(&name) =>
        {
            let body = defs[&name].body.clone();
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
            entries.into_iter().map(|(k, v)| (expand(k, defs, next, bound, active), expand(v, defs, next, bound, active))).collect(),
        ),
        ExprKind::Struct { type_name, fields } => {
            ExprKind::Struct { type_name, fields: fields.into_iter().map(|(k, v)| (k, expand(v, defs, next, bound, active))).collect() }
        }
        ExprKind::Comprehension(c) => {
            let mut c = *c;
            c.iter_range = expand(c.iter_range, defs, next, bound, active);
            c.accu_init = expand(c.accu_init, defs, next, bound, active);
            bound.push(c.accu_var.clone());
            bound.push(c.iter_var.clone());
            bound.extend(c.iter_var2.clone());
            c.loop_condition = expand(c.loop_condition, defs, next, bound, active);
            c.loop_step = expand(c.loop_step, defs, next, bound, active);
            c.result = expand(c.result, defs, next, bound, active);
            bound.truncate(bound.len() - 2 - usize::from(c.iter_var2.is_some()));
            ExprKind::Comprehension(Box::new(c))
        }
        k => k,
    };
    Expr { id, span, kind }
}

/// Number a `bind` wrapper's own nodes (not its init or body, which are numbered already).
fn renumber_shell(e: &mut Expr, next: &mut u32) {
    let mut id = |x: &mut Expr| {
        x.id = *next;
        *next += 1;
    };
    id(e);
    if let ExprKind::Comprehension(c) = &mut e.kind {
        id(&mut c.iter_range);
        id(&mut c.loop_condition);
        id(&mut c.loop_step);
    }
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
