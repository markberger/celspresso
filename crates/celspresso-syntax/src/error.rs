use crate::ast::Span;
use std::fmt;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SyntaxError {
    pub message: String,
    pub span: Span,
}

impl fmt::Display for SyntaxError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl std::error::Error for SyntaxError {}

/// Render a diagnostic with a caret line pointing at `span`, e.g.
///
/// ```text
/// ERROR: <input>:1:6: undefined field 'agee'
///  | user.agee >= 18
///  | .....^^^^
/// ```
pub fn render_diagnostic(source: &str, span: Span, message: &str) -> String {
    let start = (span.start as usize).min(source.len());
    let end = (span.end as usize).clamp(start, source.len());
    let line_start = source[..start].rfind('\n').map(|i| i + 1).unwrap_or(0);
    let line_end = source[start..].find('\n').map(|i| start + i).unwrap_or(source.len());
    let line_no = source[..start].matches('\n').count() + 1;
    let col = source[line_start..start].chars().count() + 1;
    let line = &source[line_start..line_end];
    let caret_end = end.min(line_end);
    let pad: String = source[line_start..start].chars().map(|c| if c == '\t' { '\t' } else { ' ' }).collect();
    let width = source[start..caret_end].chars().count().max(1);
    format!("{line_no}:{col}: {message}\n  | {line}\n  | {pad}{}", "^".repeat(width))
}
