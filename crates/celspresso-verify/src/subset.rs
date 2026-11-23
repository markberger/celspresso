//! celspresso's CEL subset: the part of CEL the verifier decides exactly and quickly.
//! Expressions outside it are compile errors; there is no opt-out.
//!
//! Builtins are allowed by overload id, so a builtin added later is outside the profile
//! until it is measured and listed here. Host functions are always allowed (they are
//! opaque or tabulated, which the user chose). The tiers come from probing every builtin:
//! see `benchmarks/bench_strings.py` and TECH_DEBT.md ("The subset leaves out ...").

use celspresso_check::{display_fn, is_builtin, CelType, CheckedExpr, Reference, Schema};
use celspresso_syntax::ast::{ops, Expr, ExprKind, Literal};
use celspresso_syntax::Span;

/// Overload ids inside the profile, unconditionally.
const ALLOWED: &[&str] = &[
    // logic, equality, conditionals, internals of macros and map literals
    "logical_and",
    "logical_or",
    "logical_not",
    "conditional",
    "not_strictly_false",
    "equals",
    "not_equals",
    "map_insert_entry",
    "map_insert_map",
    "to_dyn",
    "select_optional_field",
    // int / uint arithmetic (CEL truncation; overflow and /0 are errors)
    "add_int64",
    "add_uint64",
    "subtract_int64",
    "subtract_uint64",
    "multiply_int64",
    "multiply_uint64",
    "divide_int64",
    "divide_uint64",
    "modulo_int64",
    "modulo_uint64",
    "negate_int64",
    "math_greatest",
    "math_least",
    "math_abs_int",
    "math_abs_uint",
    "math_sign_int",
    "math_sign_uint",
    // conversions between ints, uints and strings
    "int64_to_int64",
    "uint64_to_int64",
    "string_to_int64",
    "uint64_to_uint64",
    "int64_to_uint64",
    "string_to_uint64",
    "string_to_string",
    "int64_to_string",
    "uint64_to_string",
    "bool_to_string",
    "bool_to_bool",
    // strings
    "add_string",
    "size_string",
    "string_size",
    "contains_string",
    "starts_with_string",
    "ends_with_string",
    "string_char_at_int",
    "string_index_of_string",
    "string_index_of_string_int",
    "string_last_index_of_string",
    "string_last_index_of_string_int",
    "string_substring_int",
    "string_substring_int_int",
    "string_lower_ascii",
    "string_upper_ascii",
    "list_join",
    "list_join_string",
    // lists and maps (bounded by max_length or the unroll limit)
    "add_list",
    "index_list",
    "index_map",
    "in_list",
    "in_map",
    "size_list",
    "size_map",
    "list_size",
    "map_size",
    "list_sum_int64",
    "list_sum_uint64",
    "list_min_int64",
    "list_min_uint64",
    "list_max_int64",
    "list_max_uint64",
    // optionals
    "optional_of",
    "optional_none",
    "optional_ofNonZeroValue",
    "optional_hasValue",
    "optional_value",
    "optional_or_optional",
    "optional_orValue_value",
    // dates, timestamps, durations (UTC accessors only)
    "add_date_int64",
    "subtract_date_date",
    "subtract_date_int64",
    "date_year",
    "date_age_on",
    "date_days_until",
    "add_timestamp_duration",
    "add_duration_timestamp",
    "add_duration_duration",
    "subtract_timestamp_timestamp",
    "subtract_timestamp_duration",
    "subtract_duration_duration",
    "timestamp_to_timestamp",
    "duration_to_duration",
    "timestamp_to_int64",
    "int64_to_timestamp",
    "timestamp_to_date",
    "timestamp_to_day_of_month",
    "timestamp_to_day_of_week",
    "timestamp_to_day_of_year",
    "timestamp_to_full_year",
    "timestamp_to_month",
    "timestamp_to_hours",
    "timestamp_to_minutes",
    "timestamp_to_seconds",
    "timestamp_to_milliseconds",
    "duration_to_hours",
    "duration_to_minutes",
    "duration_to_seconds",
    "duration_to_milliseconds",
];

/// Overload ids inside the profile when their marked argument is a literal.
const LITERAL_ARG: &[(&str, usize, &str)] = &[
    ("string_split_string", 1, "a literal, non-empty separator"),
    ("matches", 1, "a literal pattern"),
    ("matches_string", 1, "a literal pattern"),
    ("string_to_timestamp", 0, "a literal timestamp"),
    ("string_to_duration", 0, "a literal duration"),
    ("string_to_date", 0, "a literal date"),
];

fn is_comparison(id: &str) -> bool {
    let rest = ["less_equals_", "greater_equals_", "less_", "greater_"].iter().find_map(|p| id.strip_prefix(p));
    rest.is_some_and(|t| COMPARED.contains(&t))
}

/// A builtin overload, as opposed to a host function. Operator and internal names (`_+_`,
/// `_?._`, `@in`) contain characters no declared function name can, so overloads the checker
/// synthesizes for those count as builtins too.
fn builtin(function: &str, id: &str) -> bool {
    let internal = !function.chars().all(|ch| ch.is_alphanumeric() || ch == '_' || ch == '.');
    is_builtin(function, id) || internal
}

/// Modeled internal calls the checker records without an overload id.
const ID_LESS: &[&str] = &[ops::OPT_ENTRY, ops::OPT_INDEX, ops::OPT_SELECT];

/// `<`, `<=`, `>`, `>=` on these operand types (`less_int64`, `greater_equals_int64_uint64`, ...).
#[rustfmt::skip]
const COMPARED: &[&str] = &[
    "int64", "uint64", "string", "bool", "date", "timestamp", "duration", "int64_uint64", "uint64_int64",
];

/// Why a builtin outside the profile is left out, for the error message.
fn why(id: &str) -> &'static str {
    match id {
        _ if id.contains("bytes") || id.starts_with("base64") => "bytes are not modeled",
        _ if id.ends_with("_with_tz") => "time zones are not modeled; use the UTC accessor",
        "double_to_string" | "string_to_double" | "double_to_int64" | "double_to_uint64" => {
            "doubles aren't in the subset; use fixed-point numbers (T.fixed)"
        }
        _ if id.starts_with("math_") => "this math function is not modeled",
        "string_format" | "string_trim" | "string_replace_string_string" | "string_replace_string_string_int" => "not modeled yet",
        "date_to_string" | "timestamp_to_string" | "duration_to_string" => "not modeled yet",
        _ if id.starts_with("list_") || id.starts_with("lists_") => "this list function is not modeled",
        _ if id.contains("ip") || id.contains("cidr") => "the network extension is not modeled",
        _ => "the verifier can't decide it quickly and exactly",
    }
}

/// Most ranges a character class may have: Unicode classes (`\d`, `\w`, `\p{L}`) have
/// dozens to hundreds and make Z3 crawl (`^\d{5}$` alone takes seconds).
const MAX_CLASS_RANGES: usize = 16;

/// Most copies nested repetitions may make of a subpattern (`(a{10}){10}` makes 100).
const MAX_REPEAT: u32 = 1000;

/// Whether the verifier translates a `matches` pattern exactly and solves it quickly; mirrors
/// `zutil::translate_search`, which accepts only top-level `^` and `$` anchors.
pub fn pattern_in_profile(pattern: &str) -> Result<(), String> {
    use regex_syntax::hir::{Class, Hir, HirKind, Look};
    let hir = regex_syntax::ParserBuilder::new().build().parse(pattern).map_err(|e| format!("invalid pattern: {e}"))?;
    if let Some(e) = celspresso_eval::validate::pattern_error(pattern) {
        return Err(e);
    }
    // `copies`: how many times the enclosing repetitions repeat this node
    fn walk(h: &Hir, copies: u32) -> Result<(), String> {
        match h.kind() {
            HirKind::Class(c) => {
                let n = match c {
                    Class::Unicode(u) => u.ranges().len(),
                    Class::Bytes(b) => b.ranges().len(),
                };
                if n > MAX_CLASS_RANGES {
                    return Err("a large Unicode class (\\d, \\w, \\p{..}) is slow to \
                                solve; spell out ASCII ranges such as [0-9] or [A-Za-z0-9_]"
                        .into());
                }
                Ok(())
            }
            HirKind::Look(_) => Err("anchors and word boundaries are allowed only at the start and end".into()),
            HirKind::Repetition(r) => {
                let copies = copies.saturating_mul(r.max.unwrap_or(r.min).max(1));
                if copies > MAX_REPEAT {
                    return Err(format!("repetition bounds multiply to more than {MAX_REPEAT}"));
                }
                walk(&r.sub, copies)
            }
            HirKind::Capture(c) => walk(&c.sub, copies),
            HirKind::Concat(xs) | HirKind::Alternation(xs) => xs.iter().try_for_each(|x| walk(x, copies)),
            HirKind::Empty | HirKind::Literal(_) => Ok(()),
        }
    }
    let mut parts: Vec<Hir> = match hir.kind() {
        HirKind::Concat(xs) => xs.clone(),
        _ => vec![hir.clone()],
    };
    if matches!(parts.first().map(|h| h.kind()), Some(HirKind::Look(Look::Start))) {
        parts.remove(0);
    }
    if matches!(parts.last().map(|h| h.kind()), Some(HirKind::Look(Look::End))) {
        parts.pop();
    }
    parts.iter().try_for_each(|p| walk(p, 1))
}

const DOUBLES: &str = "doubles are not part of celspresso's CEL subset (their arithmetic is slow to verify and rounds); \
     use ints or fixed-point numbers (T.fixed, or Decimal with decimal_places)";
const BYTES: &str = "bytes values are not part of celspresso's CEL subset";
const DYN: &str = "values of unknown type (dyn, or Any in Python) are not part of celspresso's CEL subset; \
     give the field, variable or function result a concrete type";

/// The unmodeled type a value of type `t` holds, looking through containers. With a
/// schema, struct fields count too (for comparing whole structs).
fn unmodeled(t: &CelType, schema: Option<&Schema>, seen: &mut Vec<String>) -> Option<&'static str> {
    match t {
        CelType::Bytes => Some(BYTES),
        CelType::Double => Some(DOUBLES),
        CelType::List(a) | CelType::Nullable(a) | CelType::Optional(a) | CelType::Type(a) => unmodeled(a, schema, seen),
        CelType::Map(k, v) => unmodeled(k, schema, seen).or_else(|| unmodeled(v, schema, seen)),
        CelType::Struct(n) if !seen.contains(n) => {
            seen.push(n.clone());
            schema?.structs.get(n).and_then(|d| d.fields.iter().find_map(|f| unmodeled(&f.ty, schema, seen)))
        }
        _ => None,
    }
}

/// Why the value of `e` is outside the subset, if it is. A container of `dyn` only counts
/// when written as a literal (`[1, 'a']`); a `dict[str, Any]` may be tested with `in`, and
/// its values are caught where they are read out.
fn bad(c: &CheckedExpr, e: &Expr) -> Option<&'static str> {
    let t = c.type_of(e.id);
    if let Some(why) = unmodeled(t, None, &mut Vec::new()) {
        return Some(why);
    }
    let dyn_items = |t: &CelType| match t {
        CelType::List(a) => matches!(**a, CelType::Dyn),
        CelType::Map(k, v) => matches!(**k, CelType::Dyn) || matches!(**v, CelType::Dyn),
        _ => false,
    };
    match &e.kind {
        _ if matches!(t, CelType::Dyn) => Some(DYN),
        ExprKind::List(items) if !items.is_empty() && dyn_items(t) => Some(DYN),
        ExprKind::Map(entries) if !entries.is_empty() && dyn_items(t) => Some(DYN),
        _ => None,
    }
}

fn children(e: &Expr) -> Vec<&Expr> {
    match &e.kind {
        ExprKind::Literal(_) | ExprKind::Ident(_) => Vec::new(),
        ExprKind::Select { operand, .. } => vec![&**operand],
        ExprKind::Call { target, args, .. } => target.iter().map(|t| &**t).chain(args).collect(),
        ExprKind::List(items) => items.iter().collect(),
        ExprKind::Map(entries) => entries.iter().flat_map(|(k, v)| [k, v]).collect(),
        ExprKind::Struct { fields, .. } => fields.iter().map(|(_, v)| v).collect(),
        ExprKind::Comprehension(c) => vec![&c.iter_range, &c.accu_init, &c.loop_condition, &c.loop_step, &c.result],
    }
}

fn literal(e: &Expr) -> Option<&Literal> {
    match &e.kind {
        ExprKind::Literal(l) => Some(l),
        _ => None,
    }
}

/// Uses of CEL outside the subset, as (message, span), in source order.
pub fn violations(c: &CheckedExpr) -> Vec<(String, Span)> {
    let mut out = Vec::new();
    c.expr.walk(&mut |e: &Expr| {
        // report an unmodeled value where it originates, not at every expression it flows into
        if let Some(why) = bad(c, e) {
            if !children(e).iter().any(|k| bad(c, k).is_some()) {
                out.push((why.to_string(), e.span));
            }
            return;
        }
        let ExprKind::Call { target, function, args } = &e.kind else { return };
        let all: Vec<&Expr> = target.iter().map(|t| &**t).chain(args).collect();
        // an unmodeled operand is reported where it originates; one error is enough
        if all.iter().any(|a| bad(c, a).is_some()) {
            return;
        }
        // comparing whole structs compares every field, including unread ones
        if [ops::EQUALS, ops::NOT_EQUALS, ops::IN].contains(&function.as_str()) {
            if let Some(why) = all.iter().find_map(|a| unmodeled(c.type_of(a.id), Some(&c.schema), &mut Vec::new())) {
                out.push((format!("{why} (comparing these values compares every field; compare the fields you need)"), e.span));
                return;
            }
        }
        let ids = match c.refs.get(&e.id) {
            Some(Reference::Function(ids)) => ids.clone(),
            _ => Vec::new(),
        };
        if ids.is_empty() {
            if builtin(function, "") && !ID_LESS.contains(&function.as_str()) {
                out.push((outside(function, "the verifier can't decide it quickly and exactly"), e.span));
            }
            return;
        }
        for id in ids.iter().filter(|id| builtin(function, id)) {
            if ALLOWED.contains(&id.as_str()) || is_comparison(id) {
                continue;
            }
            if let Some((_, at, need)) = LITERAL_ARG.iter().find(|(o, ..)| o == id) {
                let ok = all.get(*at).and_then(|a| literal(a)).is_some_and(|l| match l {
                    Literal::String(s) => !(s.is_empty() && *id == "string_split_string"),
                    _ => false,
                });
                // point at the argument that has to change
                let span = all.get(*at).map_or(e.span, |a| a.span);
                if !ok {
                    out.push((format!("'{}' needs {need} in celspresso's CEL subset", display_fn(function)), span));
                } else if let (true, Some(Literal::String(p))) = (id.starts_with("matches"), all.get(*at).and_then(|a| literal(a))) {
                    if let Err(why) = pattern_in_profile(p) {
                        out.push((format!("this pattern is outside celspresso's CEL subset: {why}"), span));
                    }
                }
                continue;
            }
            out.push((outside(function, why(id)), e.span));
        }
    });
    out
}

fn outside(function: &str, why: &str) -> String {
    format!("'{}' is not part of celspresso's CEL subset: {why}", display_fn(function))
}

#[cfg(test)]
mod tests {
    use super::*;
    use celspresso_check::{check, CelType, Schema, VarDecl};
    use std::sync::Arc;

    fn outside(src: &str) -> Vec<String> {
        let mut s = Schema::with_stdlib();
        for (n, t) in [
            ("s", CelType::String),
            ("n", CelType::Int),
            ("d", CelType::Double),
            ("xs", CelType::list(CelType::Int)),
            ("at", CelType::Timestamp),
            ("day", CelType::Date),
        ] {
            s.vars.insert(n.into(), VarDecl { name: n.into(), ty: t, constraints: Default::default() });
        }
        let checked = check(celspresso_syntax::parse(src).unwrap(), Arc::new(s)).unwrap();
        violations(&checked).into_iter().map(|(m, _)| m).collect()
    }

    #[test]
    fn unmodeled_values_are_reported_once_where_they_originate() {
        for (src, want) in [
            ("[1, 'a'][0] == 1", "unknown type"),
            ("{'a': 1, 'b': 'x'}['a'] == 1", "unknown type"),
            ("dyn(n) + 1 == 2", "unknown type"),
            ("double(n) > 0.0 || n > 1", "fixed-point"),
            ("int(d) == n", "fixed-point"),
            ("size([d, d]) == 2", "fixed-point"),
        ] {
            let got = outside(src);
            assert!(got.iter().all(|m| m.contains(want)) && !got.is_empty(), "{src}: {got:?}");
        }
        assert_eq!(outside("double(n) == double(n)").len(), 2);
        assert_eq!(outside("[1, 'a'][0] == 1").len(), 1);
        assert!(outside("[] == xs && {} == {'a': n}").is_empty());
    }

    #[test]
    fn every_listed_overload_exists() {
        let s = Schema::with_stdlib();
        let ids: Vec<&str> = s.functions.values().flat_map(|f| f.overloads.iter().map(|o| o.id.as_str())).collect();
        let special = ["math_greatest", "math_least", "select_optional_field"];
        for t in COMPARED {
            for p in ["less_", "less_equals_", "greater_", "greater_equals_"] {
                assert!(ids.contains(&format!("{p}{t}").as_str()), "unknown comparison {p}{t}");
            }
        }
        for id in ALLOWED.iter().chain(LITERAL_ARG.iter().map(|(o, ..)| o)) {
            assert!(ids.contains(id) || special.contains(id), "unknown overload id {id}");
        }
    }

    #[test]
    fn the_profile_accepts_formatting_logic() {
        for src in [
            "s.startsWith('A') && size(s) <= 30 ? s.upperAscii() : s.substring(0, 3)",
            "(n < 10 ? '0' : '') + string(n) + '.' + string(n % 100)",
            "[s, 'x'].join(' ') == s + ' x' && int('12') == 12 && s.matches('^[0-9]+$')",
            r"s.matches(r'(?i)^[a-z]{2}\s*[0-9]{5}(-[0-9]{4})?$') && s.matches('.*') && s.matches('^(x+)?$')",
            "s.split(',').size() > 1 && xs.all(x, x > 0) && xs.sum() < math.greatest(n, 3)",
            "at.getFullYear() == 2024 && at < timestamp('2025-01-01T00:00:00Z') && day.year() > 1900",
            "n * 2 < 10 && n < 3 ? 1u < 2u : -n < 7",
            "optional.of(s).orValue('') == s && {'a': n}['a'] == n",
        ] {
            assert_eq!(outside(src), Vec::<String>::new(), "{src}");
        }
    }

    #[test]
    fn the_profile_rejects_slow_or_unmodeled_builtins_with_a_reason() {
        for (src, want) in [
            ("string(d) == '1.5'", "fixed-point"),
            ("d < 2.0", "doubles are not part"),
            ("n < 2.5", "doubles are not part"),
            ("[1.5].size() == 1", "doubles are not part"),
            ("dyn(n) > 1", "unknown type"),
            ("at.getHours('UTC') == 1", "time zones"),
            ("b'ab' == b'ab'", "bytes"),
            ("math.bitAnd(n, 3) == 1", "math function"),
            ("[3, 1].sort() == [1, 3]", "list function"),
            ("type(n) == int", "not part of celspresso's CEL subset"),
            ("s.split(s).size() == 1", "literal, non-empty separator"),
            ("s.split('').size() == 1", "literal, non-empty separator"),
            ("s.matches(s)", "literal pattern"),
            ("s.matches(r'^\\d{5}$')", "[0-9]"),
            ("s.matches('a(?=b)')", "invalid pattern"),
            ("s.matches('[')", "invalid pattern"),
            ("s.matches('a\\\\bb')", "start and end"),
            ("s.matches('a{2000}')", "repetition"),
            ("s.matches('^(a{100}){100}$')", "multiply"),
            ("timestamp(s) < at", "literal timestamp"),
        ] {
            let errs = outside(src);
            assert!(!errs.is_empty(), "{src}");
            assert!(errs[0].contains(want), "{src}: {}", errs[0]);
        }
    }
}
