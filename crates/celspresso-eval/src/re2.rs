//! CEL patterns are RE2, where `\d`, `\w`, `\s` and `\b` are ASCII-only. The `regex` crate
//! (and `regex-syntax`) make them Unicode-aware, so `'٣'.matches('\\d')` would be true here
//! and false in cel-go. `ascii_perl_classes` rewrites them to their ASCII forms; both the
//! evaluator and the verifier compile a `matches` pattern only after this rewrite.

use std::borrow::Cow;

const DIGIT: &str = "0-9";
const WORD: &str = "0-9A-Za-z_";
const SPACE: &str = "\\t\\n\\f\\r ";

/// `pattern` with each Perl class (`\d \D \w \W \s \S`) spelled as its RE2 ASCII set, and
/// `\b`/`\B` as ASCII word boundaries. Everything else is left as written.
pub fn ascii_perl_classes(pattern: &str) -> Cow<'_, str> {
    if !pattern.contains('\\') {
        return Cow::Borrowed(pattern);
    }
    let mut out = String::with_capacity(pattern.len() + 16);
    let mut chars = pattern.chars().peekable();
    // nesting depth of `[...]` (the regex crate allows nested classes), and whether the
    // next character is the first in its class, where `]` is a literal
    let mut depth = 0usize;
    let mut first = false;
    while let Some(ch) = chars.next() {
        let was_first = std::mem::take(&mut first);
        match ch {
            '\\' => {
                let Some(next) = chars.next() else {
                    out.push('\\');
                    break;
                };
                let set = match next.to_ascii_lowercase() {
                    'd' => Some(DIGIT),
                    'w' => Some(WORD),
                    's' => Some(SPACE),
                    _ => None,
                };
                match (set, next.is_ascii_uppercase(), depth > 0) {
                    (Some(set), false, true) => out.push_str(set),
                    (Some(set), false, false) => {
                        out.push('[');
                        out.push_str(set);
                        out.push(']');
                    }
                    (Some(set), true, _) => {
                        out.push_str("[^");
                        out.push_str(set);
                        out.push(']');
                    }
                    (None, _, false) if next == 'b' || next == 'B' => {
                        out.push_str("(?-u:\\");
                        out.push(next);
                        out.push(')');
                    }
                    (None, ..) => {
                        out.push('\\');
                        out.push(next);
                    }
                }
            }
            '[' => {
                out.push('[');
                depth += 1;
                if chars.peek() == Some(&'^') {
                    out.push('^');
                    chars.next();
                }
                first = true;
            }
            ']' if depth > 0 && !was_first => {
                out.push(']');
                depth -= 1;
            }
            _ => out.push(ch),
        }
    }
    Cow::Owned(out)
}

#[cfg(test)]
mod tests {
    use super::ascii_perl_classes as a;

    #[test]
    fn rewrites_perl_classes_outside_and_inside_brackets() {
        assert_eq!(a("^\\d{3}$"), "^[0-9]{3}$");
        assert_eq!(a("\\w+\\s\\S"), "[0-9A-Za-z_]+[\\t\\n\\f\\r ][^\\t\\n\\f\\r ]");
        assert_eq!(a("[\\d.]"), "[0-9.]");
        assert_eq!(a("[^\\w-]"), "[^0-9A-Za-z_-]");
        assert_eq!(a("[a\\D]"), "[a[^0-9]]");
        assert_eq!(a("\\bcat\\B"), "(?-u:\\b)cat(?-u:\\B)");
    }

    #[test]
    fn leaves_other_escapes_alone() {
        assert_eq!(a("a\\\\d"), "a\\\\d"); // an escaped backslash, then a literal d
        assert_eq!(a("\\p{L}\\.\\n"), "\\p{L}\\.\\n");
        assert_eq!(a("[]\\d]"), "[]0-9]"); // a leading ] is a literal
        assert_eq!(a("[[:alpha:]\\d]x\\d"), "[[:alpha:]0-9]x[0-9]");
        assert_eq!(a("plain"), "plain");
    }

    #[test]
    fn ascii_forms_compile_and_reject_non_ascii() {
        for (p, s, want) in [
            ("\\d", "٣", false),
            ("\\d", "7", true),
            ("^\\w+$", "é", false),
            ("^\\W$", "é", true),
            ("\\s", "\u{a0}", false),
            ("\\bx", "éx", true),
        ] {
            let re = regex::Regex::new(&a(p)).unwrap();
            assert_eq!(re.is_match(s), want, "{p} on {s:?}");
        }
    }
}
