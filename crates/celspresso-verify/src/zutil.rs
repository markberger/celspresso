//! Low-level Z3 helpers: exact string literals/model values and RE2 → Z3 regex translation.

use regex_syntax::hir::{Class, Hir, HirKind, Look};
use z3::ast::{Ast, Char, Regexp, String as ZStr};

/// Largest code point in Z3's default unicode alphabet.
const Z3_MAX_CHAR: u32 = 0x2FFFF;

/// Exact Z3 string literal (no escape interpretation).
pub fn str_lit(s: &str) -> ZStr {
    if s.is_empty() {
        return ZStr::from("");
    }
    if s.chars().all(|c| c.is_ascii_alphanumeric() || c == ' ' || c == '_' || c == '-' || c == '.') {
        return ZStr::from(s);
    }
    let units: Vec<ZStr> = s.chars().map(|c| Char::from_u32(c as u32).to_string()).collect();
    ZStr::concat(&units)
}

/// Read a concrete string value out of a model term.
pub fn str_value(s: &ZStr) -> Option<String> {
    let s = &s.simplify();
    unsafe {
        let ctx = s.get_ctx().get_z3_context();
        let ast = s.get_z3_ast();
        if !z3_sys::Z3_is_string(ctx, ast) {
            return None;
        }
        let n = z3_sys::Z3_get_string_length(ctx, ast);
        let mut buf = vec![0u32; n as usize];
        z3_sys::Z3_get_string_contents(ctx, ast, n, buf.as_mut_ptr());
        Some(buf.into_iter().map(|c| char::from_u32(c).unwrap_or('\u{FFFD}')).collect())
    }
}

fn re_range(lo: u32, hi: u32) -> Option<Regexp> {
    if lo > Z3_MAX_CHAR {
        return None;
    }
    let hi = hi.min(Z3_MAX_CHAR);
    let a = Char::from_u32(lo).to_string();
    let b = Char::from_u32(hi).to_string();
    unsafe {
        let ctx = a.get_ctx();
        let raw = z3_sys::Z3_mk_re_range(ctx.get_z3_context(), a.get_z3_ast(), b.get_z3_ast())?;
        Some(Regexp::wrap(ctx, raw))
    }
}

fn re_literal(s: &str) -> Regexp {
    unsafe {
        let lit = str_lit(s);
        let ctx = lit.get_ctx();
        let raw = z3_sys::Z3_mk_seq_to_re(ctx.get_z3_context(), lit.get_z3_ast()).unwrap();
        Regexp::wrap(ctx, raw)
    }
}

/// Translate a CEL (RE2) pattern into a Z3 regex matching *whole strings* that
/// `matches()` would accept (CEL `matches` is an unanchored search).
pub fn translate_search(pattern: &str) -> Result<Regexp, String> {
    let hir = regex_syntax::ParserBuilder::new().build().parse(pattern).map_err(|e| format!("regex parse error: {e}"))?;
    // peel top-level anchors
    let mut parts: Vec<Hir> = match hir.kind() {
        HirKind::Concat(xs) => xs.clone(),
        _ => vec![hir.clone()],
    };
    let anchored_start = matches!(parts.first().map(|h| h.kind()), Some(HirKind::Look(Look::Start)));
    if anchored_start {
        parts.remove(0);
    }
    let anchored_end = matches!(parts.last().map(|h| h.kind()), Some(HirKind::Look(Look::End)));
    if anchored_end {
        parts.pop();
    }
    let body: Vec<Regexp> = parts.iter().map(tr).collect::<Result<_, _>>()?;
    let mut seq = Vec::new();
    if !anchored_start {
        seq.push(Regexp::full());
    }
    seq.extend(body);
    if !anchored_end {
        seq.push(Regexp::full());
    }
    Ok(concat(seq))
}

/// Translate a pattern that must match the *entire* string (Pydantic `pattern` uses search too,
/// so callers normally want `translate_search`).
fn concat(mut xs: Vec<Regexp>) -> Regexp {
    match xs.len() {
        0 => re_literal(""),
        1 => xs.pop().unwrap(),
        _ => Regexp::concat(&xs),
    }
}

fn tr(h: &Hir) -> Result<Regexp, String> {
    Ok(match h.kind() {
        HirKind::Empty => re_literal(""),
        HirKind::Literal(l) => {
            let s = std::str::from_utf8(&l.0).map_err(|_| "non-UTF-8 regex literal".to_string())?;
            re_literal(s)
        }
        HirKind::Class(Class::Unicode(c)) => {
            let rs: Vec<Regexp> = c.ranges().iter().filter_map(|r| re_range(r.start() as u32, r.end() as u32)).collect();
            if rs.is_empty() {
                Regexp::empty()
            } else if rs.len() == 1 {
                rs.into_iter().next().unwrap()
            } else {
                Regexp::union(&rs)
            }
        }
        HirKind::Class(Class::Bytes(c)) => {
            let rs: Vec<Regexp> = c.ranges().iter().filter_map(|r| re_range(r.start() as u32, r.end() as u32)).collect();
            if rs.is_empty() {
                Regexp::empty()
            } else {
                Regexp::union(&rs)
            }
        }
        HirKind::Look(l) => return Err(format!("regex assertion {l:?} is not supported by the verifier")),
        HirKind::Repetition(r) => {
            let inner = tr(&r.sub)?;
            match (r.min, r.max) {
                (0, None) => inner.star(),
                (1, None) => inner.plus(),
                (0, Some(1)) => inner.option(),
                (lo, Some(hi)) if hi <= 1000 => inner.r#loop(lo, hi),
                (lo, None) if lo <= 1000 => concat(vec![inner.power(lo), inner.star()]),
                _ => return Err("regex repetition bound too large".into()),
            }
        }
        HirKind::Capture(c) => tr(&c.sub)?,
        HirKind::Concat(xs) => concat(xs.iter().map(tr).collect::<Result<_, _>>()?),
        HirKind::Alternation(xs) => Regexp::union(&xs.iter().map(tr).collect::<Result<Vec<_>, _>>()?),
    })
}

/// `double(x)` for an integer term: round to nearest, ties to even (Rust's `as f64`).
pub fn int_to_double(x: &z3::ast::Int) -> z3::ast::Float {
    use z3::ast::{Ast, Float, Real, RoundingMode};
    let real = Real::from_int(x);
    let rm = RoundingMode::round_nearest_ties_to_even();
    let ctx = z3::Context::thread_local();
    let sort = z3::Sort::double();
    // SAFETY: every handle comes from the thread-local context, and the result is
    // wrapped (and reference counted) immediately.
    unsafe {
        let raw = z3_sys::Z3_mk_fpa_to_fp_real(ctx.get_z3_context(), rm.get_z3_ast(), real.get_z3_ast(), sort.get_z3_sort())
            .expect("fp conversion");
        Float::wrap(&ctx, raw)
    }
}

/// Truncate a finite double to an integer term (meaningful only for finite inputs).
pub fn double_trunc(d: &z3::ast::Float) -> z3::ast::Int {
    use z3::ast::{Int, RoundingMode};
    Int::from_real(&d.round_to_integral_with_rounding_mode(&RoundingMode::round_towards_zero()).to_real())
}

/// Z3 `str.indexof(s, t, i)`: first occurrence of `t` in `s` at or after `i` (in
/// characters), `i` itself when `t` is empty and `0 <= i <= |s|`, -1 otherwise.
pub fn str_index_of(s: &ZStr, t: &ZStr, start: &z3::ast::Int) -> z3::ast::Int {
    let ctx = z3::Context::thread_local();
    // SAFETY: handles from the thread-local context; the result is wrapped immediately.
    unsafe {
        let raw = z3_sys::Z3_mk_seq_index(ctx.get_z3_context(), s.get_z3_ast(), t.get_z3_ast(), start.get_z3_ast()).expect("seq index");
        z3::ast::Int::wrap(&ctx, raw)
    }
}

/// Z3 `str.lastindexof(s, t)`: last occurrence of `t` in `s`, `|s|` when `t` is empty, -1 if none.
pub fn str_last_index_of(s: &ZStr, t: &ZStr) -> z3::ast::Int {
    let ctx = z3::Context::thread_local();
    // SAFETY: as above.
    unsafe {
        let raw = z3_sys::Z3_mk_seq_last_index(ctx.get_z3_context(), s.get_z3_ast(), t.get_z3_ast()).expect("seq last index");
        z3::ast::Int::wrap(&ctx, raw)
    }
}
