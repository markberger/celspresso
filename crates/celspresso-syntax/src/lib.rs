//! CEL syntax: lexer, parser, macro expansion and unparser.

pub mod ast;
pub mod error;
pub mod lexer;
pub mod parser;
pub mod unparse;

pub use ast::{Comprehension, Expr, ExprId, ExprKind, Literal, Span};
pub use error::{render_diagnostic, SyntaxError};
pub use parser::{parse, parse_with_limits, ParseLimits};
pub use unparse::unparse;

#[cfg(test)]
mod tests;
