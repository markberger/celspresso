//! Formal verification of checked CEL expressions with Z3.
//!
//! Every query is phrased as "find an input such that <goal>". `Found` carries a
//! witness that has been replayed through the evaluator; `NotFound` is a proof
//! (unless the encoding was bounded, in which case it degrades to `Unknown`).

mod encode;
mod sym;
mod zutil;

use celspresso_check::CheckedExpr;
use celspresso_eval::{evaluate, Functions, Limits, Value};
use encode::Encoder;
use std::cell::RefCell;
use std::collections::BTreeMap;
use std::time::Instant;
use sym::*;
use z3::ast::Bool;
use z3::{Config, Params, SatResult, Solver};

#[derive(Clone, Copy, Debug)]
pub struct Options {
    pub timeout_ms: u64,
    pub unroll_limit: usize,
    pub schema_constraints: bool,
}

impl Default for Options {
    fn default() -> Self {
        Options { timeout_ms: 5_000, unroll_limit: 5, schema_constraints: true }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ErrorMode {
    /// Errors are a distinct outcome: equivalent expressions must error on the same inputs.
    Strict,
    /// An error counts as `false` (typical policy semantics).
    AsFalse,
}

pub enum Query<'a> {
    /// Find an input where the predicate is true.
    Satisfiable(&'a CheckedExpr),
    /// Find an input where the predicate is not true (false or error).
    AlwaysTrue(&'a CheckedExpr),
    /// Find an input where the two expressions disagree.
    Equivalent(&'a CheckedExpr, &'a CheckedExpr, ErrorMode),
    /// Find an input where `a` is true but `b` is not.
    Implies(&'a CheckedExpr, &'a CheckedExpr),
    /// Find an input where the expression errors.
    CanError(&'a CheckedExpr),
}

#[derive(Clone, Debug)]
pub enum Status {
    Found(BTreeMap<String, Value>),
    NotFound,
    Unknown(String),
}

#[derive(Clone, Debug)]
pub struct Outcome {
    pub status: Status,
    /// The result relied on the comprehension unroll limit.
    pub bounded: bool,
    pub elapsed_ms: f64,
    /// Where the encoding over-approximated CEL semantics.
    pub approximations: Vec<String>,
}

fn holds(sv: &SV) -> Bool {
    match sv.v.as_bool() {
        Some(b) => and(&[b, &sv.err.not()]),
        None => ff(),
    }
}

fn goal(enc: &mut Encoder, q: &Query) -> Result<Bool, String> {
    Ok(match q {
        Query::Satisfiable(p) => holds(&enc.encode(p)),
        Query::AlwaysTrue(p) => holds(&enc.encode(p)).not(),
        Query::CanError(e) => enc.encode(e).err,
        Query::Implies(a, b) => {
            let a = enc.encode(a);
            let b = enc.encode(b);
            and(&[&holds(&a), &holds(&b).not()])
        }
        Query::Equivalent(a, b, mode) => {
            let a = enc.encode(a);
            let b = enc.encode(b);
            match mode {
                ErrorMode::AsFalse => holds(&a).xor(holds(&b)),
                ErrorMode::Strict => {
                    let Some(eq) = sym_eq(&a.v, &b.v) else {
                        return Err("cannot compare values of these types".into());
                    };
                    or(&[&a.err.xor(&b.err), &and(&[&a.err.not(), &b.err.not(), &eq.not()])])
                }
            }
        }
    })
}

fn unknown_reason(r: Option<String>) -> String {
    match r.as_deref() {
        Some("timeout") | Some("canceled") => "solver timeout".into(),
        Some(other) => format!("solver gave up: {other}"),
        None => "solver gave up".into(),
    }
}

/// Rounds of "replay failed -> learn the custom functions' real values -> re-solve".
const MAX_REFINEMENTS: usize = 8;

fn solve(q: &Query, assumptions: &[&CheckedExpr], opts: Options, funcs: &(dyn Functions + Sync)) -> (Status, bool, Vec<String>) {
    let schema = match q {
        Query::Satisfiable(e) | Query::AlwaysTrue(e) | Query::CanError(e) | Query::Implies(e, _) | Query::Equivalent(e, _, _) => {
            e.schema.clone()
        }
    };
    let mut enc = Encoder::new(schema, opts.unroll_limit, opts.schema_constraints);
    let g = match goal(&mut enc, q) {
        Ok(g) => g,
        Err(why) => return (Status::Unknown(why), false, vec![]),
    };
    let user: Vec<Bool> = assumptions.iter().map(|a| holds(&enc.encode(a))).collect();
    let approximations: Vec<String> = enc.approximations.iter().cloned().collect();
    let bounded = enc.bounded;

    let mut params = Params::new();
    params.set_u32("timeout", opts.timeout_ms.min(u32::MAX as u64) as u32);
    let solver = Solver::new();
    let _ = solver.set_params(&params);
    for a in enc.assumptions.iter().chain(&user) {
        solver.assert(a);
    }
    solver.assert(&g);
    let readable = ReadablePass::new(&enc.soft);

    let mut refinements = 0;
    let status = loop {
        match solver.check() {
            SatResult::Sat => {
                let mut model = solver.get_model().expect("model");
                if let Some(m) = readable.run(&solver, &model, opts.timeout_ms) {
                    model = m;
                }
                let _ = solver.set_params(&params); // restore the full timeout
                let w = enc.witness(&model);
                let rec = Recording { inner: funcs, calls: RefCell::new(Vec::new()) };
                if replay(q, assumptions, &w, &rec) {
                    break Status::Found(w);
                }
                let facts: Vec<Bool> =
                    rec.calls.borrow().iter().filter_map(|(f, args, res)| enc.refine(f, args, res)).collect();
                if facts.is_empty() || refinements == MAX_REFINEMENTS {
                    break Status::Unknown(if approximations.is_empty() {
                        "internal: solver witness did not replay in the evaluator".to_string()
                    } else {
                        format!("candidate witness did not replay; approximations: {}", approximations.join("; "))
                    });
                }
                for f in &facts {
                    solver.assert(f);
                }
                refinements += 1;
            }
            SatResult::Unsat => {
                // vacuity: if the assumptions alone are contradictory, the "proof" means nothing
                let s2 = Solver::new();
                let _ = s2.set_params(&params);
                for a in enc.assumptions.iter().chain(&user) {
                    s2.assert(a);
                }
                break match s2.check() {
                    SatResult::Unsat => Status::Unknown("assumptions are unsatisfiable".into()),
                    _ if bounded => Status::Unknown(format!(
                        "a list may be longer than the unroll limit ({}); declare max_length or raise unroll_limit",
                        opts.unroll_limit
                    )),
                    _ => Status::NotFound,
                };
            }
            SatResult::Unknown => break Status::Unknown(unknown_reason(solver.get_reason_unknown())),
        }
    };
    (status, bounded, approximations)
}

/// Records every host-function call made while replaying a witness.
struct Recording<'a> {
    inner: &'a dyn Functions,
    calls: RefCell<Vec<(String, Vec<Value>, Result<Value, String>)>>,
}

impl Functions for Recording<'_> {
    fn call(&self, function: &str, args: &[Value]) -> Option<Result<Value, String>> {
        let r = self.inner.call(function, args)?;
        self.calls.borrow_mut().push((function.to_string(), args.to_vec(), r.clone()));
        Some(r)
    }
}

/// Prefer small, readable witness values (soft constraints) without a fresh MaxSAT search.
///
/// Only preferences the solver's model *violates* are worked on (none, in the common case,
/// which makes this free). Each is guarded by an indicator literal, created on first use
/// so it never burdens the main search. We ask the incremental solver to satisfy the
/// violated set, drop members of the unsat core until it succeeds, and keep the new model
/// only if it violates fewer preferences overall. Greedy and bounded, not optimal.
struct ReadablePass<'a> {
    soft: &'a [Bool],
    indicators: RefCell<Option<Vec<Bool>>>,
}

impl<'a> ReadablePass<'a> {
    const MAX_ROUNDS: usize = 4;

    fn new(soft: &'a [Bool]) -> Self {
        ReadablePass { soft, indicators: RefCell::new(None) }
    }

    fn violations(&self, model: &z3::Model) -> Vec<usize> {
        (0..self.soft.len())
            .filter(|&i| model.eval(&self.soft[i], true).and_then(|b| b.as_bool()) != Some(true))
            .collect()
    }

    /// May leave a short timeout on the solver; the caller restores its own params.
    fn run(&self, solver: &Solver, model: &z3::Model, timeout_ms: u64) -> Option<z3::Model> {
        let violated = self.violations(model);
        if violated.is_empty() {
            return None;
        }
        let mut slot = self.indicators.borrow_mut();
        let indicators = slot.get_or_insert_with(|| {
            self.soft
                .iter()
                .enumerate()
                .map(|(i, s)| {
                    let ind = Bool::new_const(format!("!soft{i}"));
                    solver.assert(&ind.implies(s));
                    ind
                })
                .collect()
        });
        let mut p = Params::new();
        p.set_u32("timeout", timeout_ms.clamp(20, 100) as u32);
        let _ = solver.set_params(&p);
        let mut active: Vec<Bool> = violated.iter().map(|&i| indicators[i].clone()).collect();
        for _ in 0..Self::MAX_ROUNDS {
            if active.is_empty() {
                return None;
            }
            match solver.check_assumptions(&active) {
                SatResult::Sat => {
                    let m = solver.get_model()?;
                    return (self.violations(&m).len() < violated.len()).then_some(m);
                }
                SatResult::Unsat => {
                    let core = solver.get_unsat_core();
                    if core.is_empty() {
                        return None;
                    }
                    active.retain(|a| !core.contains(a));
                }
                SatResult::Unknown => return None,
            }
        }
        None
    }
}

fn replay(q: &Query, assumptions: &[&CheckedExpr], w: &BTreeMap<String, Value>, funcs: &dyn Functions) -> bool {
    let run = |e: &CheckedExpr| evaluate(e, w, funcs, Limits::default());
    let is_true = |e: &CheckedExpr| matches!(run(e), Ok(Value::Bool(true)));
    if !assumptions.iter().all(|a| is_true(a)) {
        return false;
    }
    match q {
        Query::Satisfiable(p) => is_true(p),
        Query::AlwaysTrue(p) => !is_true(p),
        Query::CanError(e) => run(e).is_err(),
        Query::Implies(a, b) => is_true(a) && !is_true(b),
        Query::Equivalent(a, b, ErrorMode::AsFalse) => is_true(a) != is_true(b),
        Query::Equivalent(a, b, ErrorMode::Strict) => match (run(a), run(b)) {
            (Ok(x), Ok(y)) => x != y,
            (Err(_), Err(_)) => false,
            _ => true,
        },
    }
}

/// Run a verification query. `funcs` is used to replay witnesses through the evaluator.
pub fn verify(q: &Query, assumptions: &[&CheckedExpr], opts: Options, funcs: &(dyn Functions + Sync)) -> Outcome {
    let start = Instant::now();
    let mut cfg = Config::new();
    cfg.set_timeout_msec(opts.timeout_ms);
    cfg.set_model_generation(true);
    let (status, bounded, approximations) = z3::with_z3_config(&cfg, || solve(q, assumptions, opts, funcs));
    Outcome { status, bounded, elapsed_ms: start.elapsed().as_secs_f64() * 1000.0, approximations }
}

#[cfg(test)]
mod tests;
