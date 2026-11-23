//! Formal verification of checked CEL expressions with Z3.
//!
//! Every query is phrased as "find an input such that <goal>". `Found` carries a
//! witness that has been replayed through the evaluator; `NotFound` is a proof
//! (unless the encoding was bounded, in which case it degrades to `Unknown`).

mod encode;
pub mod strict;
mod sym;
mod zutil;

use celspresso_check::{CelType, CheckedExpr, Reference};
use celspresso_eval::{evaluate, Functions, Limits, Value};
use encode::Encoder;
use std::cell::RefCell;
use std::collections::BTreeMap;
use std::time::Instant;
use sym::*;
use z3::ast::{Bool, Int};
use z3::{Config, Optimize, Params, SatResult, Solver};

#[derive(Clone, Copy, Debug)]
pub struct Options {
    pub timeout_ms: u64,
    pub unroll_limit: usize,
    pub schema_constraints: bool,
    /// After a proof, replay the query on this many diverse valid inputs (a soundness
    /// self-check). Any input that replays as a counterexample is returned as one.
    pub sample_proofs: usize,
}

impl Default for Options {
    fn default() -> Self {
        Options { timeout_ms: 5_000, unroll_limit: 5, schema_constraints: true, sample_proofs: 0 }
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

/// Whether the assumptions allow a value the encoding cut off at the unroll bound.
/// Encode the user assumptions. Returns them all, plus the ones that don't read a split:
/// in a model where a split overflows, its last piece is the unsplit remainder, so facts
/// about its pieces are false there and must not be used to rule the overflow out.
fn encode_user(enc: &mut Encoder, assumptions: &[&CheckedExpr]) -> (Vec<Bool>, Vec<Bool>) {
    let (mut all, mut real) = (Vec::new(), Vec::new());
    for a in assumptions {
        let before = enc.overflow.len();
        let b = holds(&enc.encode(a));
        if enc.overflow.len() == before {
            real.push(b.clone());
        }
        all.push(b);
    }
    (all, real)
}

/// Whether some real input may make a split produce more pieces than its slots, judged by
/// the encoding facts (true of any value, truncated pieces included) and `real`, the user
/// assumptions that don't read a split. Anything but a proof that none can counts as yes.
fn overflows(enc: &Encoder, real: &[Bool], params: &Params) -> bool {
    if enc.overflow.is_empty() {
        return false;
    }
    let s = Solver::new();
    let _ = s.set_params(params);
    for a in enc.assumptions.iter().chain(real) {
        s.assert(a);
    }
    s.assert(or(&enc.overflow.iter().collect::<Vec<_>>()));
    s.check() != SatResult::Unsat
}

fn unknown_reason(r: Option<String>) -> String {
    match r.as_deref() {
        Some("timeout") | Some("canceled") => "solver timeout".into(),
        Some(other) => format!("solver gave up: {other}"),
        None => "solver gave up".into(),
    }
}

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
    let (user, real) = encode_user(&mut enc, assumptions);
    let approximations: Vec<String> = enc.approximations.iter().cloned().collect();
    // whether the encoding was cut off at the unroll limit; reported only if the result relied on it
    let truncated = enc.bounded;
    let mut bounded = false;

    let mut params = Params::new();
    params.set_u32("timeout", opts.timeout_ms.min(u32::MAX as u64) as u32);
    let solver = Solver::new();
    let _ = solver.set_params(&params);
    for a in enc.assumptions.iter().chain(&user) {
        solver.assert(a);
    }
    solver.assert(&g);
    let readable = ReadablePass::new(&enc.soft);

    // One solve, one replay. Host functions are never called during solving: they are
    // opaque (plus contracts) or tabulated, so a witness that doesn't replay is UNKNOWN.
    let status = match solver.check() {
        SatResult::Sat => {
            let mut model = solver.get_model().expect("model");
            if let Some(m) = readable.run(&solver, &model, opts.timeout_ms) {
                model = m;
            }
            let w = complete_witness(q, assumptions, enc.witness(&model));
            match w.filter(|w| replay(q, assumptions, w, funcs)) {
                Some(w) => Status::Found(w),
                None => Status::Unknown(enc.unreplayed_reason()),
            }
        }
        SatResult::Unsat => {
            // vacuity: if the assumptions alone are contradictory, the "proof" means nothing
            let s2 = Solver::new();
            let _ = s2.set_params(&params);
            for a in enc.assumptions.iter().chain(&user) {
                s2.assert(a);
            }
            match s2.check() {
                SatResult::Unsat => Status::Unknown("assumptions are unsatisfiable".into()),
                _ if truncated || overflows(&enc, &real, &params) => {
                    bounded = true;
                    Status::Unknown(format!(
                        "a list or map may be longer than the unroll limit ({}); declare max_length or raise unroll_limit",
                        opts.unroll_limit
                    ))
                }
                _ => match sample_proofs(&enc, q, assumptions, &user, &params, funcs, opts) {
                    Some(w) => Status::Found(w),
                    None => Status::NotFound,
                },
            }
        }
        SatResult::Unknown => Status::Unknown(unknown_reason(solver.get_reason_unknown())),
    };
    (status, bounded, approximations)
}

/// Proof sampling: draw diverse models of the assumptions alone (random targets for every
/// integer leaf, as soft preferences) and replay the query on each. The encoding said no
/// counterexample exists, so one that replays exposes a verifier bug, and is the true answer.
fn sample_proofs(
    enc: &Encoder,
    q: &Query,
    assumptions: &[&CheckedExpr],
    user: &[Bool],
    params: &Params,
    funcs: &(dyn Functions + Sync),
    opts: Options,
) -> Option<BTreeMap<String, Value>> {
    let mut leaves = Vec::new();
    for s in enc.vars.values() {
        s.int_leaves(&mut leaves);
    }
    let mut seed: u64 = 0x9E37_79B9_7F4A_7C15;
    let mut next = move || {
        seed = seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1_442_695_040_888_963_407);
        seed >> 33
    };
    for _ in 0..opts.sample_proofs {
        let s = Solver::new();
        let _ = s.set_params(params);
        for a in enc.assumptions.iter().chain(user) {
            s.assert(a);
        }
        if s.check() != SatResult::Sat {
            return None;
        }
        let m = s.get_model()?;
        // half the targets near zero (boundaries), half anywhere in a wider range
        let soft: Vec<Bool> = leaves
            .iter()
            .map(|x| {
                let r = next() as i64;
                let t = if r % 2 == 0 { r % 33 - 2 } else { r % 20_001 - 10_000 };
                x.eq(Int::from_i64(t))
            })
            .collect();
        let m = ReadablePass::new(&soft).run(&s, &m, opts.timeout_ms).unwrap_or(m);
        if let Some(w) = complete_witness(q, assumptions, enc.witness(&m)) {
            if replay(q, assumptions, &w, funcs) {
                return Some(w);
            }
        }
    }
    None
}

/// Prefer small, readable witness values (soft constraints) without a fresh MaxSAT search.
///
/// Runs only when the solver's model violates some preference (never, in the common case,
/// which makes this free). Each preference is guarded by an indicator literal, created on
/// first use so it never burdens the main search. We ask the incremental solver for all
/// of them, drop members of the unsat core until it succeeds, and keep the new model only
/// if it violates fewer preferences overall. Greedy and bounded, not optimal.
struct ReadablePass<'a> {
    soft: &'a [Bool],
    indicators: RefCell<Option<Vec<Bool>>>,
}

impl<'a> ReadablePass<'a> {
    const MAX_ROUNDS: usize = 6;

    fn new(soft: &'a [Bool]) -> Self {
        ReadablePass { soft, indicators: RefCell::new(None) }
    }

    fn violations(&self, model: &z3::Model) -> Vec<usize> {
        (0..self.soft.len()).filter(|&i| model.eval(&self.soft[i], true).and_then(|b| b.as_bool()) != Some(true)).collect()
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
                    solver.assert(ind.implies(s));
                    ind
                })
                .collect()
        });
        let mut p = Params::new();
        p.set_u32("timeout", timeout_ms.clamp(20, 100) as u32);
        let _ = solver.set_params(&p);
        // assume every preference, not just the violated ones: satisfying those alone
        // tends to break others. Drop unsat-core members (or, on a timeout, the
        // lower-priority half; preferences are pushed outermost-first) and retry.
        let mut active: Vec<Bool> = indicators.clone();
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
                SatResult::Unknown => active.truncate(active.len() / 2),
            }
        }
        None
    }
}

/// The encoding only sees variables it modeled: one referenced only under an
/// approximation (`optional.of(s).hasValue()`) is absent from the model. Give each such
/// variable a concrete default so the replay below checks the witness for real; without
/// a default the variable stays unbound, replay fails, and the verdict is UNKNOWN.
fn complete_witness(q: &Query, assumptions: &[&CheckedExpr], w: BTreeMap<String, Value>) -> Option<BTreeMap<String, Value>> {
    let exprs: Vec<&CheckedExpr> = match q {
        Query::Satisfiable(p) | Query::AlwaysTrue(p) | Query::CanError(p) => vec![p],
        Query::Equivalent(a, b, _) | Query::Implies(a, b) => vec![a, b],
    };
    complete_vars(&exprs, assumptions, w)
}

fn complete_vars(exprs: &[&CheckedExpr], assumptions: &[&CheckedExpr], mut w: BTreeMap<String, Value>) -> Option<BTreeMap<String, Value>> {
    for c in exprs.iter().copied().chain(assumptions.iter().copied()) {
        for r in c.refs.values() {
            if let Reference::Var(name) = r {
                if !w.contains_key(name) {
                    match c.schema.vars.get(name).and_then(|d| default_value(&d.ty)) {
                        Some(v) => {
                            w.insert(name.clone(), v);
                        }
                        // an unbound variable would make evaluation error, which replay could
                        // mistake for a confirmed counterexample: mark the witness unusable
                        None => return None,
                    }
                }
            }
        }
    }
    Some(w)
}

fn default_value(t: &CelType) -> Option<Value> {
    Some(match t {
        CelType::Bool => Value::Bool(false),
        CelType::Int => Value::Int(0),
        CelType::Uint => Value::Uint(0),
        CelType::Double => Value::Double(0.0),
        CelType::String => Value::str(""),
        CelType::Bytes => Value::Bytes(std::sync::Arc::from(&b""[..])),
        CelType::Null | CelType::Nullable(_) | CelType::Dyn => Value::Null,
        CelType::Date => Value::Date(0),
        CelType::Timestamp => Value::Timestamp(0),
        CelType::Duration => Value::Duration(0),
        CelType::List(_) => Value::list(vec![]),
        CelType::Map(..) => Value::Map(std::sync::Arc::new(BTreeMap::new())),
        _ => return None,
    })
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

/// One end of an expression's range.
#[derive(Clone, Debug)]
pub struct Extreme {
    pub value: Value,
    /// An input where the expression evaluates to `value` (replayed when `attained`).
    pub witness: BTreeMap<String, Value>,
    /// The witness replays through the evaluator to exactly `value`.
    pub attained: bool,
    /// No input gives a value beyond this one (UNSAT check), so it is a sound bound.
    pub sound: bool,
}

#[derive(Clone, Debug)]
pub struct BoundsOutcome {
    pub min: Option<Extreme>,
    pub max: Option<Extreme>,
    /// Why a bound is missing or not exact.
    pub reason: Option<String>,
    pub bounded: bool,
    pub elapsed_ms: f64,
    pub approximations: Vec<String>,
}

/// The smallest and largest values a numeric expression takes over every valid input on
/// which it evaluates without error. Each end is found with Z3 Optimize, then confirmed
/// by an UNSAT check (nothing beyond it) and by replaying its witness in the evaluator.
pub fn bounds(e: &CheckedExpr, assumptions: &[&CheckedExpr], opts: Options, funcs: &(dyn Functions + Sync)) -> BoundsOutcome {
    let start = Instant::now();
    let mut cfg = Config::new();
    cfg.set_timeout_msec(opts.timeout_ms);
    cfg.set_model_generation(true);
    let mut out = z3::with_z3_config(&cfg, || bounds_inner(e, assumptions, opts, funcs));
    out.elapsed_ms = start.elapsed().as_secs_f64() * 1000.0;
    out
}

fn bounds_inner(e: &CheckedExpr, assumptions: &[&CheckedExpr], opts: Options, funcs: &(dyn Functions + Sync)) -> BoundsOutcome {
    let mut enc = Encoder::new(e.schema.clone(), opts.unroll_limit, opts.schema_constraints);
    let sv = enc.encode(e);
    let (user, real) = encode_user(&mut enc, assumptions);
    let mut out = BoundsOutcome {
        min: None,
        max: None,
        reason: None,
        bounded: enc.bounded,
        elapsed_ms: 0.0,
        approximations: enc.approximations.iter().cloned().collect(),
    };
    let Some(x) = sv.v.as_int().cloned().or(match &sv.v {
        Sym::Timestamp(i) | Sym::Duration(i) => Some(i.clone()),
        _ => None,
    }) else {
        out.reason = Some(format!("bounds() needs an integer-valued expression, not {}", e.output_type()));
        return out;
    };
    let mut params = Params::new();
    params.set_u32("timeout", opts.timeout_ms.min(u32::MAX as u64) as u32);
    let base: Vec<Bool> = enc.assumptions.iter().chain(&user).cloned().chain([sv.err.not()]).collect();
    let mut reasons = Vec::new();
    let readable = ReadablePass::new(&enc.soft);
    // a split with more pieces than slots makes every bound below a guess
    // (not under "no error": an error term may read a truncated piece, like the claim)
    let truncated = enc.bounded || overflows(&enc, &real, &params);
    out.bounded = truncated;
    for maximize in [false, true] {
        let opt = Optimize::new();
        opt.set_params(&params).ok();
        for b in &base {
            opt.assert(b);
        }
        if maximize {
            opt.maximize(&x);
        } else {
            opt.minimize(&x);
        }
        match opt.check(&[]) {
            SatResult::Sat => {}
            SatResult::Unsat => {
                out.reason = Some("the expression errors on every valid input (or the assumptions are unsatisfiable)".into());
                return out;
            }
            SatResult::Unknown => {
                reasons.push(unknown_reason(opt.get_reason_unknown()));
                continue;
            }
        }
        let Some(model) = opt.get_model() else { continue };
        let Some(v) = model.eval(&x, true) else { continue };
        // confirm: no valid input lies beyond v (Optimize alone may stop early or report infinity)
        let s = Solver::new();
        let _ = s.set_params(&params);
        for b in &base {
            s.assert(b);
        }
        s.push();
        s.assert(if maximize { x.gt(&v) } else { x.lt(&v) });
        let beyond = s.check();
        let _ = s.pop(1);
        let sound = match beyond {
            SatResult::Unsat => !truncated,
            SatResult::Sat => {
                reasons
                    .push(format!("no {} bound: the expression is unbounded in this encoding", if maximize { "upper" } else { "lower" }));
                false
            }
            SatResult::Unknown => {
                reasons.push(unknown_reason(s.get_reason_unknown()));
                false
            }
        };
        // re-solve at exactly v so the witness can prefer small, readable values
        s.assert(x.eq(&v));
        let mut model = model;
        if s.check() == SatResult::Sat {
            if let Some(m) = s.get_model() {
                model = readable.run(&s, &m, opts.timeout_ms).unwrap_or(m);
            }
        }
        let value = enc.value(&model, &sv.v);
        let witness = complete_vars(&[e], assumptions, enc.witness(&model));
        let attained = witness.as_ref().is_some_and(|w| {
            assumptions.iter().all(|a| matches!(evaluate(a, w, funcs, Limits::default()), Ok(Value::Bool(true))))
                && evaluate(e, w, funcs, Limits::default()).is_ok_and(|r| r == value)
        });
        let ext = Extreme { value, witness: witness.unwrap_or_default(), attained, sound };
        if maximize {
            out.max = Some(ext);
        } else {
            out.min = Some(ext);
        }
    }
    if truncated {
        reasons.push(format!(
            "a list or map may be longer than the unroll limit ({}); declare max_length or raise unroll_limit",
            opts.unroll_limit
        ));
    }
    let exact = |x: &Option<Extreme>| x.as_ref().is_some_and(|x| x.sound && x.attained);
    if exact(&out.min) && exact(&out.max) {
        return out;
    }
    if reasons.is_empty() {
        reasons.push(if out.approximations.is_empty() {
            "a solver witness did not replay in the evaluator".into()
        } else {
            format!("approximations: {}", out.approximations.join("; "))
        });
    }
    reasons.dedup();
    out.reason = Some(reasons.join("; "));
    out
}

#[cfg(test)]
mod tests;
