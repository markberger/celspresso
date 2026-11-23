//! The strict profile: the part of CEL the verifier decides exactly and quickly.
//!
//! Builtins are allowed by overload id, so a builtin added later is outside the profile
//! until it is measured and listed here. Host functions are always allowed (they are
//! opaque or tabulated, which the user chose). The tiers come from probing every builtin:
//! see `benchmarks/bench_strings.py` and TECH_DEBT.md ("Strict profile").

use celspresso_check::{display_fn, is_builtin, CheckedExpr, Reference};
use celspresso_syntax::ast::{Expr, ExprKind, Literal};
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
    // int / uint / double arithmetic (CEL truncation; overflow and /0 are errors)
    "add_int64",
    "add_uint64",
    "add_double",
    "subtract_int64",
    "subtract_uint64",
    "subtract_double",
    "multiply_int64",
    "multiply_uint64",
    "multiply_double",
    "divide_int64",
    "divide_uint64",
    "divide_double",
    "modulo_int64",
    "modulo_uint64",
    "negate_int64",
    "negate_double",
    "math_greatest",
    "math_least",
    "math_abs_int",
    "math_abs_uint",
    "math_abs_double",
    "math_sign_int",
    "math_sign_uint",
    "math_sign_double",
    // conversions between ints, uints and strings
    "int64_to_int64",
    "uint64_to_int64",
    "string_to_int64",
    "uint64_to_uint64",
    "int64_to_uint64",
    "string_to_uint64",
    "int64_to_double",
    "uint64_to_double",
    "double_to_double",
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
    "list_sum_double",
    "list_min_int64",
    "list_min_uint64",
    "list_min_double",
    "list_max_int64",
    "list_max_uint64",
    "list_max_double",
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
    rest.is_some_and(|t| t != "bytes")
}

/// Why a builtin outside the profile is left out, for the error message.
fn why(id: &str) -> &'static str {
    match id {
        _ if id.contains("bytes") || id.starts_with("base64") => "bytes are not modeled",
        _ if id.ends_with("_with_tz") => "time zones are not modeled; use the UTC accessor",
        "double_to_string" | "string_to_double" | "double_to_int64" | "double_to_uint64" => {
            "converting doubles to strings or ints is slow or unmodeled; use fixed-point numbers (T.fixed)"
        }
        _ if id.starts_with("math_") => "this math function is not modeled",
        "string_format" | "string_trim" | "string_replace_string_string" | "string_replace_string_string_int" => "not modeled yet",
        "date_to_string" | "timestamp_to_string" | "duration_to_string" => "not modeled yet",
        _ if id.starts_with("list_") || id.starts_with("lists_") => "this list function is not modeled",
        _ if id.contains("ip") || id.contains("cidr") => "the network extension is not modeled",
        _ => "the verifier can't decide it quickly and exactly",
    }
}

fn literal(e: &Expr) -> Option<&Literal> {
    match &e.kind {
        ExprKind::Literal(l) => Some(l),
        _ => None,
    }
}

/// Uses of CEL outside the strict profile, as (message, span), in source order.
pub fn violations(c: &CheckedExpr) -> Vec<(String, Span)> {
    let mut out = Vec::new();
    c.expr.walk(&mut |e: &Expr| match &e.kind {
        ExprKind::Literal(Literal::Bytes(_)) => {
            out.push(("bytes literals are outside the strict profile: bytes are not modeled".to_string(), e.span));
        }
        ExprKind::Call { target, function, args } => {
            let ids = match c.refs.get(&e.id) {
                Some(Reference::Function(ids)) => ids.clone(),
                _ => Vec::new(),
            };
            if ids.is_empty() {
                if is_builtin(function, "") {
                    out.push((outside(function, "the verifier can't decide it quickly and exactly"), e.span));
                }
                return;
            }
            let all: Vec<&Expr> = target.iter().map(|t| &**t).chain(args).collect();
            for id in ids.iter().filter(|id| is_builtin(function, id)) {
                if ALLOWED.contains(&id.as_str()) || is_comparison(id) {
                    continue;
                }
                if let Some((_, at, need)) = LITERAL_ARG.iter().find(|(o, ..)| o == id) {
                    let ok = all.get(*at).and_then(|a| literal(a)).is_some_and(|l| match l {
                        Literal::String(s) => !(s.is_empty() && *id == "string_split_string"),
                        _ => false,
                    });
                    if !ok {
                        out.push((format!("'{}' needs {need} in the strict profile", display_fn(function)), e.span));
                    }
                    continue;
                }
                out.push((outside(function, why(id)), e.span));
            }
        }
        _ => {}
    });
    out
}

fn outside(function: &str, why: &str) -> String {
    format!(
        "'{}' is outside the strict profile ({why}); create the Env with strict=False to use it, \
         at the cost of UNKNOWN verdicts",
        display_fn(function)
    )
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
    fn every_listed_overload_exists() {
        let s = Schema::with_stdlib();
        let ids: Vec<&str> = s.functions.values().flat_map(|f| f.overloads.iter().map(|o| o.id.as_str())).collect();
        let special = ["math_greatest", "math_least"];
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
            "s.split(',').size() > 1 && xs.all(x, x > 0) && xs.sum() < math.greatest(n, 3)",
            "at.getFullYear() == 2024 && at < timestamp('2025-01-01T00:00:00Z') && day.year() > 1900",
            "d * 2.0 < 10.0 && n < 3u + 1u ? true : 1 < 2.5",
            "optional.of(s).orValue('') == s && {'a': n}['a'] == n",
        ] {
            assert_eq!(outside(src), Vec::<String>::new(), "{src}");
        }
    }

    #[test]
    fn the_profile_rejects_slow_or_unmodeled_builtins_with_a_reason() {
        for (src, want) in [
            ("string(d) == '1.5'", "fixed-point"),
            ("at.getHours('UTC') == 1", "time zones"),
            ("b'ab' == b'ab'", "bytes"),
            ("math.floor(d) == 1.0", "math function"),
            ("[3, 1].sort() == [1, 3]", "list function"),
            ("type(n) == int", "outside the strict profile"),
            ("s.split(s).size() == 1", "literal, non-empty separator"),
            ("s.split('').size() == 1", "literal, non-empty separator"),
            ("s.matches(s)", "literal pattern"),
            ("timestamp(s) < at", "literal timestamp"),
        ] {
            let errs = outside(src);
            assert!(!errs.is_empty(), "{src}");
            assert!(errs[0].contains(want), "{src}: {}", errs[0]);
        }
    }
}
