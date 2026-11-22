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
use std::collections::BTreeMap;
use std::time::Instant;
use sym::*;
use z3::ast::Bool;
use z3::{Config, Optimize, Params, SatResult, Solver};

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

enum Raw {
    Sat(BTreeMap<String, Value>),
    Unsat,
    Unknown(String),
}

struct RawOutcome {
    raw: Raw,
    bounded: bool,
    approximations: Vec<String>,
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

fn solve(q: &Query, assumptions: &[&CheckedExpr], opts: Options) -> RawOutcome {
    let schema = match q {
        Query::Satisfiable(e) | Query::AlwaysTrue(e) | Query::CanError(e) | Query::Implies(e, _) | Query::Equivalent(e, _, _) => {
            e.schema.clone()
        }
    };
    let mut enc = Encoder::new(schema, opts.unroll_limit, opts.schema_constraints);
    let g = match goal(&mut enc, q) {
        Ok(g) => g,
        Err(why) => return RawOutcome { raw: Raw::Unknown(why), bounded: false, approximations: vec![] },
    };
    let user: Vec<Bool> = assumptions.iter().map(|a| holds(&enc.encode(a))).collect();

    let mut params = Params::new();
    params.set_u32("timeout", opts.timeout_ms.min(u32::MAX as u64) as u32);
    let solver = Solver::new();
    let _ = solver.set_params(&params);
    for a in enc.assumptions.iter().chain(&user) {
        solver.assert(a);
    }
    solver.assert(&g);
    let approximations: Vec<String> = enc.approximations.iter().cloned().collect();
    let raw = match solver.check() {
        SatResult::Sat => {
            let mut model = solver.get_model().expect("model");
            // second pass: prefer small, readable values
            let opt = Optimize::new();
            let mut p2 = Params::new();
            p2.set_u32("timeout", opts.timeout_ms.clamp(50, 500) as u32);
            let _ = opt.set_params(&p2);
            for a in enc.assumptions.iter().chain(&user) {
                opt.assert(a);
            }
            opt.assert(&g);
            for s in &enc.soft {
                opt.assert_soft(s, 1, None);
            }
            if opt.check(&[]) == SatResult::Sat {
                if let Some(m) = opt.get_model() {
                    model = m;
                }
            }
            Raw::Sat(enc.witness(&model))
        }
        SatResult::Unsat => {
            // vacuity: if the assumptions alone are contradictory, the "proof" means nothing
            let s2 = Solver::new();
            let _ = s2.set_params(&params);
            for a in enc.assumptions.iter().chain(&user) {
                s2.assert(a);
            }
            match s2.check() {
                SatResult::Unsat => Raw::Unknown("assumptions are unsatisfiable".into()),
                _ if enc.bounded => Raw::Unknown(format!(
                    "a list may be longer than the unroll limit ({}); declare max_length or raise unroll_limit",
                    opts.unroll_limit
                )),
                _ => Raw::Unsat,
            }
        }
        SatResult::Unknown => Raw::Unknown(unknown_reason(solver.get_reason_unknown())),
    };
    RawOutcome { raw, bounded: enc.bounded, approximations }
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
pub fn verify(q: &Query, assumptions: &[&CheckedExpr], opts: Options, funcs: &dyn Functions) -> Outcome {
    let start = Instant::now();
    let mut cfg = Config::new();
    cfg.set_timeout_msec(opts.timeout_ms);
    cfg.set_model_generation(true);
    let r = z3::with_z3_config(&cfg, || solve(q, assumptions, opts));
    let status = match r.raw {
        Raw::Sat(w) => {
            if replay(q, assumptions, &w, funcs) {
                Status::Found(w)
            } else {
                let why = if r.approximations.is_empty() {
                    "internal: solver witness did not replay in the evaluator".to_string()
                } else {
                    format!("candidate witness did not replay; approximations: {}", r.approximations.join("; "))
                };
                Status::Unknown(why)
            }
        }
        Raw::Unsat => Status::NotFound,
        Raw::Unknown(why) => Status::Unknown(why),
    };
    Outcome { status, bounded: r.bounded, elapsed_ms: start.elapsed().as_secs_f64() * 1000.0, approximations: r.approximations }
}

#[cfg(test)]
mod tests;
