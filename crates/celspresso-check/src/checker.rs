//! Type checker: resolves identifiers, fields and overloads, producing a CheckedExpr.

use crate::decls::{Overload, Schema};
use crate::types::{assignable, join, CelType, Subst};
use celspresso_syntax::ast::{ops, Comprehension, Expr, ExprId, ExprKind, Literal, Span};
use std::collections::HashMap;
use std::fmt;
use std::sync::Arc;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckError {
    pub message: String,
    pub span: Span,
    pub expr_id: ExprId,
}

impl fmt::Display for CheckError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.message)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Reference {
    /// A declared environment variable.
    Var(String),
    /// A comprehension-local variable.
    Local(String),
    /// The overload ids that may be selected at runtime (usually exactly one).
    Function(Vec<String>),
}

/// A type-checked expression: the AST plus a type for every node and a
/// reference for every identifier and call.
#[derive(Debug)]
pub struct CheckedExpr {
    pub expr: Expr,
    pub types: HashMap<ExprId, CelType>,
    pub refs: HashMap<ExprId, Reference>,
    pub schema: Arc<Schema>,
}

impl CheckedExpr {
    pub fn type_of(&self, id: ExprId) -> &CelType {
        self.types.get(&id).unwrap_or(&CelType::Dyn)
    }
    pub fn output_type(&self) -> &CelType {
        self.type_of(self.expr.id)
    }
    /// The single resolved overload id for a call node, if unambiguous.
    pub fn overload(&self, id: ExprId) -> Option<&str> {
        match self.refs.get(&id) {
            Some(Reference::Function(ids)) if ids.len() == 1 => Some(&ids[0]),
            _ => None,
        }
    }
    /// Environment variables referenced (sorted, deduplicated), with field paths.
    pub fn references(&self) -> Vec<String> {
        let mut out = std::collections::BTreeSet::new();
        collect_paths(&self.expr, self, &mut out);
        out.into_iter().collect()
    }
}

fn collect_paths(e: &Expr, c: &CheckedExpr, out: &mut std::collections::BTreeSet<String>) {
    fn path(e: &Expr, c: &CheckedExpr) -> Option<String> {
        match &e.kind {
            ExprKind::Ident(n) if matches!(c.refs.get(&e.id), Some(Reference::Var(_))) => Some(n.clone()),
            ExprKind::Select { operand, field, .. } => path(operand, c).map(|p| format!("{p}.{field}")),
            _ => None,
        }
    }
    if let Some(p) = path(e, c) {
        out.insert(p);
        return;
    }
    match &e.kind {
        ExprKind::Select { operand, .. } => collect_paths(operand, c, out),
        ExprKind::Call { target, args, .. } => {
            if let Some(t) = target {
                collect_paths(t, c, out);
            }
            args.iter().for_each(|a| collect_paths(a, c, out));
        }
        ExprKind::List(items) => items.iter().for_each(|a| collect_paths(a, c, out)),
        ExprKind::Map(entries) => entries.iter().for_each(|(k, v)| {
            collect_paths(k, c, out);
            collect_paths(v, c, out)
        }),
        ExprKind::Struct { fields, .. } => fields.iter().for_each(|(_, v)| collect_paths(v, c, out)),
        ExprKind::Comprehension(comp) => {
            for x in [&comp.iter_range, &comp.accu_init, &comp.loop_condition, &comp.loop_step, &comp.result] {
                collect_paths(x, c, out);
            }
        }
        _ => {}
    }
}

pub fn check(expr: Expr, schema: Arc<Schema>) -> Result<CheckedExpr, Vec<CheckError>> {
    let mut c = Checker {
        schema: &schema,
        types: HashMap::new(),
        refs: HashMap::new(),
        subst: Subst::new(),
        scopes: Vec::new(),
        errors: Vec::new(),
        fresh: 0,
    };
    c.check(&expr);
    if !c.errors.is_empty() {
        return Err(c.errors);
    }
    let subst = c.subst;
    let types = c.types.into_iter().map(|(id, t)| (id, t.finalize(&subst))).collect();
    let refs = c.refs;
    Ok(CheckedExpr { expr, types, refs, schema: schema.clone() })
}

struct Checker<'a> {
    schema: &'a Schema,
    types: HashMap<ExprId, CelType>,
    refs: HashMap<ExprId, Reference>,
    subst: Subst,
    scopes: Vec<HashMap<String, CelType>>,
    errors: Vec<CheckError>,
    fresh: u32,
}

impl<'a> Checker<'a> {
    fn error(&mut self, e: &Expr, message: String) -> CelType {
        self.errors.push(CheckError { message, span: e.span, expr_id: e.id });
        CelType::Error
    }

    fn set(&mut self, e: &Expr, t: CelType) -> CelType {
        self.types.insert(e.id, t.clone());
        t
    }

    fn resolved(&self, t: &CelType) -> CelType {
        t.finalize(&self.subst)
    }

    fn check(&mut self, e: &Expr) -> CelType {
        let t = match &e.kind {
            ExprKind::Literal(l) => match l {
                Literal::Null => CelType::Null,
                Literal::Bool(_) => CelType::Bool,
                Literal::Int(_) => CelType::Int,
                Literal::Uint(_) => CelType::Uint,
                Literal::Double(_) => CelType::Double,
                Literal::String(_) => CelType::String,
                Literal::Bytes(_) => CelType::Bytes,
            },
            ExprKind::Ident(name) => self.ident(e, name),
            ExprKind::Select { operand, field, test_only } => self.select(e, operand, field, *test_only),
            ExprKind::Call { target, function, args } => self.call(e, target.as_deref(), function, args),
            ExprKind::List(items) => {
                let mut elem = self.fresh_param();
                for it in items {
                    let t = self.check(it);
                    elem = join(&elem, &t, &mut self.subst);
                }
                CelType::list(elem)
            }
            ExprKind::Map(entries) => {
                let mut kt = self.fresh_param();
                let mut vt = self.fresh_param();
                for (k, v) in entries {
                    let t = self.check(k);
                    if !matches!(self.resolved(&t), CelType::String | CelType::Int | CelType::Uint | CelType::Bool | CelType::Dyn | CelType::Error | CelType::Param(_)) {
                        self.error(k, format!("unsupported map key type '{}'", self.resolved(&t)));
                    }
                    kt = join(&kt, &t, &mut self.subst);
                    let t = self.check(v);
                    vt = join(&vt, &t, &mut self.subst);
                }
                CelType::map(kt, vt)
            }
            ExprKind::Struct { type_name, fields } => self.struct_lit(e, type_name, fields),
            ExprKind::Comprehension(c) => self.comprehension(c),
        };
        self.set(e, t)
    }

    fn fresh_param(&mut self) -> CelType {
        self.fresh += 1;
        CelType::Param(format!("_T{}", self.fresh))
    }

    fn lookup_local(&self, name: &str) -> Option<CelType> {
        self.scopes.iter().rev().find_map(|s| s.get(name).cloned())
    }

    fn ident(&mut self, e: &Expr, name: &str) -> CelType {
        if let Some(t) = self.lookup_local(name) {
            self.refs.insert(e.id, Reference::Local(name.to_string()));
            return t;
        }
        if let Some(v) = self.schema.vars.get(name) {
            self.refs.insert(e.id, Reference::Var(name.to_string()));
            return v.ty.clone();
        }
        let mut msg = format!("undeclared reference to '{name}'");
        if let Some(s) = suggest(name, self.schema.vars.keys().map(|s| s.as_str())) {
            msg.push_str(&format!(" (did you mean '{s}'?)"));
        }
        self.error(e, msg)
    }

    fn select(&mut self, e: &Expr, operand: &Expr, field: &str, test_only: bool) -> CelType {
        let ot = self.check(operand);
        let ft = match self.resolved(&ot).non_null().clone() {
            CelType::Struct(name) => match self.schema.structs.get(&name) {
                Some(sd) => match sd.field(field) {
                    Some(f) => f.ty.clone(),
                    None => {
                        let mut msg = format!("undefined field '{field}' on {name}");
                        if let Some(s) = suggest(field, sd.fields.iter().map(|f| f.name.as_str())) {
                            msg.push_str(&format!(" (did you mean '{s}'?)"));
                        }
                        self.error(e, msg)
                    }
                },
                None => self.error(e, format!("unknown type '{name}'")),
            },
            CelType::Map(k, v) => {
                if !assignable(&k, &CelType::String, &mut self.subst) {
                    self.error(e, format!("field selection on map with key type '{k}'"));
                }
                *v
            }
            CelType::Dyn | CelType::Error | CelType::Param(_) => CelType::Dyn,
            other => self.error(e, format!("type '{other}' does not support field selection")),
        };
        if test_only {
            CelType::Bool
        } else {
            ft
        }
    }

    fn struct_lit(&mut self, e: &Expr, type_name: &str, fields: &[(String, Expr)]) -> CelType {
        let Some(sd) = self.schema.structs.get(type_name).cloned() else {
            for (_, v) in fields {
                self.check(v);
            }
            return self.error(e, format!("unknown type '{type_name}'"));
        };
        for (name, v) in fields {
            let vt = self.check(v);
            match sd.field(name) {
                Some(f) => {
                    if !assignable(&f.ty, &vt, &mut self.subst) {
                        self.error(v, format!("field '{name}' expects '{}', got '{}'", f.ty, self.resolved(&vt)));
                    }
                }
                None => {
                    self.error(v, format!("undefined field '{name}' on {type_name}"));
                }
            }
        }
        CelType::Struct(type_name.to_string())
    }

    fn comprehension(&mut self, c: &Comprehension) -> CelType {
        let rt = self.check(&c.iter_range);
        let var_t = match self.resolved(&rt).non_null().clone() {
            CelType::List(e) => *e,
            CelType::Map(k, _) => *k,
            CelType::Dyn | CelType::Error | CelType::Param(_) => CelType::Dyn,
            other => {
                self.error(&c.iter_range, format!("expression of type '{other}' cannot be the range of a comprehension (must be list, map, or dynamic)"));
                CelType::Error
            }
        };
        let accu_t = self.check(&c.accu_init);
        let mut scope = HashMap::new();
        scope.insert(c.accu_var.clone(), accu_t.clone());
        self.scopes.push(scope);
        let cond_t = self.check(&c.loop_condition);
        if !assignable(&CelType::Bool, &cond_t, &mut self.subst) {
            self.error(&c.loop_condition, "loop condition must be bool".into());
        }
        let mut scope = HashMap::new();
        scope.insert(c.iter_var.clone(), var_t);
        self.scopes.push(scope);
        let step_t = self.check(&c.loop_step);
        self.scopes.pop();
        if !assignable(&accu_t, &step_t, &mut self.subst) {
            let msg = format!("comprehension step type '{}' does not match accumulator type '{}'", self.resolved(&step_t), self.resolved(&accu_t));
            self.error(&c.loop_step, msg);
        }
        let result_t = self.check(&c.result);
        self.scopes.pop();
        // macro predicates must be bool
        if matches!(c.macro_name.as_str(), "all" | "exists" | "exists_one" | "filter") {
            // their predicate types were enforced through logical_and/or/conditional overloads
        }
        result_t
    }

    fn call(&mut self, e: &Expr, target: Option<&Expr>, function: &str, args: &[Expr]) -> CelType {
        let mut arg_types = Vec::with_capacity(args.len() + 1);
        if let Some(t) = target {
            arg_types.push(self.check(t));
        }
        for a in args {
            arg_types.push(self.check(a));
        }
        let Some(decl) = self.schema.functions.get(function).cloned() else {
            let all = self.schema.functions.keys().filter(|k| !k.starts_with('_') && !k.starts_with('@') && !k.starts_with('!') && !k.starts_with('-')).map(|s| s.as_str());
            let mut msg = format!("undeclared reference to function '{function}'");
            if let Some(s) = suggest(function, all) {
                msg.push_str(&format!(" (did you mean '{s}'?)"));
            }
            return self.error(e, msg);
        };
        let receiver = target.is_some();
        let mut matched: Vec<(Overload, CelType, Subst)> = Vec::new();
        for o in decl.overloads.iter().filter(|o| o.receiver == receiver && o.params.len() == arg_types.len()) {
            let o = self.instantiate(o);
            let mut s = self.subst.clone();
            if o.params.iter().zip(&arg_types).all(|(p, a)| assignable(p, a, &mut s)) {
                matched.push((o.clone(), o.result.clone(), s));
            }
        }
        // Prefer exact (non-dyn) matches when several overloads accept dyn args.
        if matched.len() > 1 {
            let exact: Vec<_> = matched
                .iter()
                .filter(|(o, _, s)| o.params.iter().zip(&arg_types).all(|(p, a)| strictly_matches(p, a, s)))
                .cloned()
                .collect();
            if !exact.is_empty() {
                matched = exact;
            }
        }
        match matched.len() {
            0 => {
                let shown: Vec<String> = arg_types.iter().map(|t| self.resolved(t).to_string()).collect();
                let name = display_fn(function);
                let msg = if receiver {
                    format!("found no matching overload for '{name}' applied to '{}.({})'", shown[0], shown[1..].join(", "))
                } else {
                    format!("found no matching overload for '{name}' applied to '({})'", shown.join(", "))
                };
                self.error(e, msg)
            }
            1 => {
                let (o, result, s) = matched.pop().unwrap();
                self.subst = s;
                self.refs.insert(e.id, Reference::Function(vec![o.id]));
                result
            }
            _ => {
                // ambiguous due to dyn: runtime dispatch over the candidates
                let ids = matched.iter().map(|(o, _, _)| o.id.clone()).collect();
                let mut rt = matched[0].1.clone();
                for (_, r, s) in &matched[1..] {
                    let mut s2 = s.clone();
                    rt = join(&rt, r, &mut s2);
                }
                self.refs.insert(e.id, Reference::Function(ids));
                rt
            }
        }
    }

    fn instantiate(&mut self, o: &Overload) -> Overload {
        let mut map = HashMap::new();
        let mut rename = |t: &CelType, this: &mut Self| -> CelType { rename_params(t, &mut map, this) };
        let params = o.params.iter().map(|p| rename(p, self)).collect();
        let result = rename(&o.result, self);
        Overload { id: o.id.clone(), receiver: o.receiver, params, result }
    }
}

fn rename_params(t: &CelType, map: &mut HashMap<String, CelType>, c: &mut Checker) -> CelType {
    match t {
        CelType::Param(p) => {
            if let Some(n) = map.get(p) {
                return n.clone();
            }
            let n = c.fresh_param();
            map.insert(p.clone(), n.clone());
            n
        }
        CelType::List(e) => CelType::list(rename_params(e, map, c)),
        CelType::Map(k, v) => {
            let k = rename_params(k, map, c);
            CelType::map(k, rename_params(v, map, c))
        }
        CelType::Nullable(e) => CelType::nullable(rename_params(e, map, c)),
        t => t.clone(),
    }
}

fn strictly_matches(p: &CelType, a: &CelType, s: &Subst) -> bool {
    let p = p.finalize(s);
    let a = a.finalize(s);
    !a.is_dyn_like() || p.is_dyn_like()
}

fn display_fn(f: &str) -> &str {
    match f {
        ops::ADD => "+",
        ops::SUBTRACT => "-",
        ops::MULTIPLY => "*",
        ops::DIVIDE => "/",
        ops::MODULO => "%",
        ops::EQUALS => "==",
        ops::NOT_EQUALS => "!=",
        ops::LESS => "<",
        ops::LESS_EQUALS => "<=",
        ops::GREATER => ">",
        ops::GREATER_EQUALS => ">=",
        ops::LOGICAL_AND => "&&",
        ops::LOGICAL_OR => "||",
        ops::LOGICAL_NOT => "!",
        ops::NEGATE => "-",
        ops::IN => "in",
        ops::INDEX => "[]",
        ops::CONDITIONAL => "?:",
        f => f,
    }
}

/// Closest candidate within a small edit distance.
pub fn suggest<'s>(name: &str, candidates: impl Iterator<Item = &'s str>) -> Option<&'s str> {
    let max = (name.len() / 3).max(1);
    candidates
        .map(|c| (levenshtein(name, c), c))
        .filter(|(d, _)| *d <= max)
        .min_by_key(|(d, _)| *d)
        .map(|(_, c)| c)
}

fn levenshtein(a: &str, b: &str) -> usize {
    let a: Vec<char> = a.chars().collect();
    let b: Vec<char> = b.chars().collect();
    let mut prev: Vec<usize> = (0..=b.len()).collect();
    for i in 1..=a.len() {
        let mut cur = vec![i; b.len() + 1];
        for j in 1..=b.len() {
            let cost = usize::from(a[i - 1] != b[j - 1]);
            cur[j] = (prev[j] + 1).min(cur[j - 1] + 1).min(prev[j - 1] + cost);
        }
        prev = cur;
    }
    prev[b.len()]
}
