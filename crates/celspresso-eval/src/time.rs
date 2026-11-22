//! `google.protobuf.Timestamp` and `google.protobuf.Duration` support.
//!
//! Both are carried as signed nanosecond counts (`i128`): timestamps from the Unix
//! epoch, durations as a span. CEL restricts timestamps to years 0001..=9999 and
//! durations to roughly ±10000 years; every constructor and arithmetic result is
//! range-checked against those limits.

use jiff::tz::{Offset, TimeZone};
use jiff::Timestamp;

use crate::date;

const NANOS: i128 = 1_000_000_000;
/// 0001-01-01T00:00:00Z
const MIN_TS: i128 = -62_135_596_800 * NANOS;
/// 9999-12-31T23:59:59.999999999Z
const MAX_TS: i128 = 253_402_300_799 * NANOS + (NANOS - 1);
/// ±315,576,000,000.999999999s, the protobuf Duration limit.
const MAX_DUR: i128 = 315_576_000_000 * NANOS + (NANOS - 1);

pub fn ts_in_range(ns: i128) -> bool {
    (MIN_TS..=MAX_TS).contains(&ns)
}

pub fn dur_in_range(ns: i128) -> bool {
    (-MAX_DUR..=MAX_DUR).contains(&ns)
}

/// Nanoseconds for `seconds` since the epoch, if it is a valid timestamp.
pub fn ts_from_seconds(secs: i64) -> Option<i128> {
    let ns = i128::from(secs) * NANOS;
    ts_in_range(ns).then_some(ns)
}

/// Whole seconds since the epoch (floored, like `Timestamp.seconds`).
pub fn ts_seconds(ns: i128) -> i64 {
    ns.div_euclid(NANOS) as i64
}

/// Parse an RFC 3339 timestamp such as `2009-02-13T23:31:30.5Z` or `...+01:00`.
///
/// Parsed by hand rather than with jiff: jiff's `Timestamp` stops at 9999-12-30,
/// short of CEL's 9999-12-31T23:59:59.999999999Z.
pub fn parse_timestamp(s: &str) -> Option<i128> {
    let b = s.as_bytes();
    let num = |r: std::ops::Range<usize>| -> Option<i64> {
        let part = b.get(r)?;
        if part.iter().all(u8::is_ascii_digit) {
            std::str::from_utf8(part).ok()?.parse().ok()
        } else {
            None
        }
    };
    if b.len() < 20 || b[4] != b'-' || b[7] != b'-' || !matches!(b[10], b'T' | b't') || b[13] != b':' || b[16] != b':' {
        return None;
    }
    let (y, mo, d) = (num(0..4)?, num(5..7)?, num(8..10)?);
    let (h, mi, sec) = (num(11..13)?, num(14..16)?, num(17..19)?);
    if !(1..=12).contains(&mo) || d < 1 || d > date::days_in_month(y, mo) || h > 23 || mi > 59 || sec > 59 {
        return None;
    }
    let mut i = 19;
    let mut frac: i128 = 0;
    if b[i] == b'.' {
        let start = i + 1;
        i = start;
        while i < b.len() && b[i].is_ascii_digit() {
            i += 1;
        }
        let digits = &s[start..i];
        if digits.is_empty() || digits.len() > 9 {
            return None;
        }
        frac = format!("{digits:0<9}").parse().ok()?;
    }
    let offset_secs: i64 = match &b[i..] {
        [b'Z' | b'z'] => 0,
        [sign @ (b'+' | b'-'), _, _, b':', _, _] => {
            let (oh, om) = (num(i + 1..i + 3)?, num(i + 4..i + 6)?);
            if oh > 23 || om > 59 {
                return None;
            }
            (oh * 3600 + om * 60) * if *sign == b'-' { -1 } else { 1 }
        }
        _ => return None,
    };
    let secs = date::days_from_civil(y, mo, d) * 86_400 + h * 3600 + mi * 60 + sec - offset_secs;
    let ns = i128::from(secs) * NANOS + frac;
    ts_in_range(ns).then_some(ns)
}

/// RFC 3339 in UTC with only as many fractional digits as needed.
pub fn format_timestamp(ns: i128) -> String {
    let secs = ns.div_euclid(NANOS) as i64;
    let frac = ns.rem_euclid(NANOS);
    let (y, mo, d) = date::civil_from_days(secs.div_euclid(86_400));
    let tod = secs.rem_euclid(86_400);
    let mut out = format!("{y:04}-{mo:02}-{d:02}T{:02}:{:02}:{:02}", tod / 3600, tod / 60 % 60, tod % 60);
    if frac != 0 {
        out.push('.');
        out.push_str(format!("{frac:09}").trim_end_matches('0'));
    }
    out.push('Z');
    out
}

/// Parse a duration in Go syntax: `1h30m`, `-1.5s`, `315576000000s999999999ns`.
pub fn parse_duration(s: &str) -> Option<i128> {
    let (neg, mut rest) = match s.as_bytes().first()? {
        b'-' => (true, &s[1..]),
        b'+' => (false, &s[1..]),
        _ => (false, s),
    };
    if rest == "0" {
        return Some(0);
    }
    if rest.is_empty() {
        return None;
    }
    let mut total: i128 = 0;
    while !rest.is_empty() {
        let int_end = rest.find(|c: char| !c.is_ascii_digit()).unwrap_or(rest.len());
        let int_part = &rest[..int_end];
        rest = &rest[int_end..];
        let mut frac_part = "";
        if let Some(r) = rest.strip_prefix('.') {
            let frac_end = r.find(|c: char| !c.is_ascii_digit()).unwrap_or(r.len());
            frac_part = &r[..frac_end];
            rest = &r[frac_end..];
        }
        if int_part.is_empty() && frac_part.is_empty() {
            return None;
        }
        let unit_end = rest.find(|c: char| c.is_ascii_digit() || c == '.').unwrap_or(rest.len());
        let scale: i128 = match &rest[..unit_end] {
            "ns" => 1,
            "us" | "µs" | "μs" => 1_000,
            "ms" => 1_000_000,
            "s" => NANOS,
            "m" => 60 * NANOS,
            "h" => 3600 * NANOS,
            _ => return None,
        };
        rest = &rest[unit_end..];
        let whole: i128 = if int_part.is_empty() { 0 } else { int_part.parse().ok()? };
        let mut frac: i128 = 0;
        let mut denom: i128 = 1;
        for d in frac_part.bytes().take(30) {
            frac = frac * 10 + i128::from(d - b'0');
            denom *= 10;
        }
        total = total.checked_add(whole.checked_mul(scale)?)?.checked_add(frac * scale / denom)?;
        if total > MAX_DUR {
            return None;
        }
    }
    let ns = if neg { -total } else { total };
    dur_in_range(ns).then_some(ns)
}

/// Seconds with a trimmed fraction: `1.5s`, `-315576000000.999999999s`, `0s`.
pub fn format_duration(ns: i128) -> String {
    let sign = if ns < 0 { "-" } else { "" };
    let abs = ns.unsigned_abs();
    let (secs, frac) = (abs / NANOS as u128, abs % NANOS as u128);
    if frac == 0 {
        format!("{sign}{secs}s")
    } else {
        let digits = format!("{frac:09}");
        format!("{sign}{secs}.{}s", digits.trim_end_matches('0'))
    }
}

/// A calendar or clock field of a timestamp, as CEL's `getX()` accessors define it.
#[derive(Clone, Copy, Debug)]
pub enum TsField {
    FullYear,
    /// 0-based
    Month,
    /// 1-based day of month (`getDate`)
    Date,
    /// 0-based day of month
    DayOfMonth,
    /// 0 = Sunday
    DayOfWeek,
    /// 0-based
    DayOfYear,
    Hours,
    Minutes,
    Seconds,
    Milliseconds,
}

impl TsField {
    pub fn from_function(name: &str) -> Option<TsField> {
        Some(match name {
            "getFullYear" => TsField::FullYear,
            "getMonth" => TsField::Month,
            "getDate" => TsField::Date,
            "getDayOfMonth" => TsField::DayOfMonth,
            "getDayOfWeek" => TsField::DayOfWeek,
            "getDayOfYear" => TsField::DayOfYear,
            "getHours" => TsField::Hours,
            "getMinutes" => TsField::Minutes,
            "getSeconds" => TsField::Seconds,
            "getMilliseconds" => TsField::Milliseconds,
            _ => return None,
        })
    }
}

/// `field` of the timestamp `ns` in time zone `tz` (UTC when `None`). The zone is an
/// IANA name (`America/New_York`) or a fixed offset (`+05:30`, `-02:00`, `02:00`).
pub fn ts_field(ns: i128, field: TsField, tz: Option<&str>) -> Result<i64, String> {
    let offset = match tz {
        None => 0,
        Some(name) => {
            let zone = parse_zone(name).ok_or_else(|| format!("unknown time zone '{name}'"))?;
            // jiff's range ends a day before CEL's; zone rules are stable at the edges
            let probe = Timestamp::from_nanosecond(ns)
                .unwrap_or(if ns < 0 { Timestamp::MIN } else { Timestamp::MAX });
            i64::from(zone.to_offset(probe).seconds())
        }
    };
    let secs = ns.div_euclid(NANOS) as i64 + offset;
    let days = secs.div_euclid(86_400);
    let tod = secs.rem_euclid(86_400);
    let (y, mo, d) = date::civil_from_days(days);
    Ok(match field {
        TsField::FullYear => y,
        TsField::Month => mo - 1,
        TsField::Date => d,
        TsField::DayOfMonth => d - 1,
        // 1970-01-01 was a Thursday
        TsField::DayOfWeek => (days + 4).rem_euclid(7),
        TsField::DayOfYear => days - date::days_from_civil(y, 1, 1),
        TsField::Hours => tod / 3600,
        TsField::Minutes => tod / 60 % 60,
        TsField::Seconds => tod % 60,
        TsField::Milliseconds => (ns.rem_euclid(NANOS) / 1_000_000) as i64,
    })
}

fn parse_zone(name: &str) -> Option<TimeZone> {
    let (sign, body) = match name.as_bytes().first()? {
        b'+' => (1, &name[1..]),
        b'-' => (-1, &name[1..]),
        b'0'..=b'9' => (1, name),
        _ => return TimeZone::get(name).ok(),
    };
    let (h, m) = body.split_once(':')?;
    let (h, m): (i32, i32) = (h.parse().ok()?, m.parse().ok()?);
    if h > 23 || m > 59 {
        return None;
    }
    Offset::from_seconds(sign * (h * 3600 + m * 60)).ok().map(TimeZone::fixed)
}

/// Duration accessors: total hours/minutes/seconds, or the millisecond component.
pub fn dur_field(ns: i128, field: TsField) -> Option<i64> {
    Some(match field {
        TsField::Hours => (ns / (3600 * NANOS)) as i64,
        TsField::Minutes => (ns / (60 * NANOS)) as i64,
        TsField::Seconds => (ns / NANOS) as i64,
        TsField::Milliseconds => ((ns % NANOS) / 1_000_000) as i64,
        _ => return None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn durations_round_trip() {
        for (s, ns) in [
            ("1000000s", 1_000_000 * NANOS),
            ("1.5s", 1_500_000_000),
            ("-1h30m", -5400 * NANOS),
            ("315576000000s999999999ns", MAX_DUR),
            ("0", 0),
            ("1ms", 1_000_000),
        ] {
            assert_eq!(parse_duration(s), Some(ns), "{s}");
        }
        assert_eq!(format_duration(MAX_DUR), "315576000000.999999999s");
        assert_eq!(format_duration(-1_500_000_000), "-1.5s");
        assert_eq!(parse_duration("315576000001s"), None);
        assert_eq!(parse_duration("1x"), None);
        assert_eq!(parse_duration(""), None);
    }

    #[test]
    fn timestamps_round_trip_and_range() {
        let ns = parse_timestamp("2009-02-13T23:31:30Z").unwrap();
        assert_eq!(ts_seconds(ns), 1_234_567_890);
        assert_eq!(format_timestamp(ns), "2009-02-13T23:31:30Z");
        assert!(parse_timestamp("0000-01-01T00:00:00Z").is_none());
        assert!(parse_timestamp("2009-02-13").is_none());
        assert_eq!(ts_field(ns, TsField::DayOfWeek, None), Ok(5));
        assert_eq!(ts_field(ns, TsField::Hours, Some("02:00")), Ok(1));
        assert_eq!(ts_field(ns, TsField::Date, Some("Australia/Sydney")), Ok(14));
        assert!(ts_field(ns, TsField::Hours, Some("Mars/Base")).is_err());
        let max = parse_timestamp("9999-12-31T23:59:59.999999999Z").unwrap();
        assert_eq!(format_timestamp(max), "9999-12-31T23:59:59.999999999Z");
        assert_eq!(ts_field(max, TsField::DayOfYear, Some("UTC")), Ok(364));
        assert_eq!(parse_timestamp("2009-02-13T23:31:30+01:00"), Some(ns - 3600 * NANOS));
        assert_eq!(format_timestamp(-1), "1969-12-31T23:59:59.999999999Z");
    }
}
