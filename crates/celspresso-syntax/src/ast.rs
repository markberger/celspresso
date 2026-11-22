//! CEL abstract syntax tree.
//!
//! Operators are represented as calls with cel-go style function names
//! (`_+_`, `_&&_`, `_?_:_`, `!_`, `-_`, `_[_]`, `@in`, ...), so that the
//! checker, evaluator and verifier share a single overload vocabulary.

use std::fmt;

pub type ExprId = u32;

/// Byte offsets into the source text, `start..end`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct Span {
    pub start: u32,
    pub end: u32,
}

impl Span {
    pub fn new(start: usize, end: usize) -> Self {
        Span { start: start as u32, end: end as u32 }
    }
    pub fn to(self, other: Span) -> Span {
        Span { start: self.start.min(other.start), end: self.end.max(other.end) }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Literal {
    Null,
    Bool(bool),
    Int(i64),
    Uint(u64),
    Double(f64),
    String(String),
    Bytes(Vec<u8>),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Expr {
    pub id: ExprId,
    pub span: Span,
    pub kind: ExprKind,
}

#[derive(Clone, Debug, PartialEq)]
pub enum ExprKind {
    Literal(Literal),
    Ident(String),
    /// `operand.field`; with `test_only` this is the expansion of `has(operand.field)`.
    Select { operand: Box<Expr>, field: String, test_only: bool },
    /// Global call (`target == None`) or receiver-style call.
    Call { target: Option<Box<Expr>>, function: String, args: Vec<Expr> },
    List(Vec<Expr>),
    Map(Vec<(Expr, Expr)>),
    /// Message construction `Type{field: value}`.
    Struct { type_name: String, fields: Vec<(String, Expr)> },
    Comprehension(Box<Comprehension>),
}

/// Fold-style comprehension produced by macro expansion (cel-go compatible).
#[derive(Clone, Debug, PartialEq)]
pub struct Comprehension {
    pub iter_var: String,
    pub iter_range: Expr,
    pub accu_var: String,
    pub accu_init: Expr,
    pub loop_condition: Expr,
    pub loop_step: Expr,
    pub result: Expr,
    /// Which macro produced this comprehension (`all`, `exists`, `map`, ...).
    pub macro_name: String,
}

pub const ACCU_VAR: &str = "@result";

/// Operator function names.
pub mod ops {
    pub const CONDITIONAL: &str = "_?_:_";
    pub const LOGICAL_AND: &str = "_&&_";
    pub const LOGICAL_OR: &str = "_||_";
    pub const LOGICAL_NOT: &str = "!_";
    pub const NEGATE: &str = "-_";
    pub const EQUALS: &str = "_==_";
    pub const NOT_EQUALS: &str = "_!=_";
    pub const LESS: &str = "_<_";
    pub const LESS_EQUALS: &str = "_<=_";
    pub const GREATER: &str = "_>_";
    pub const GREATER_EQUALS: &str = "_>=_";
    pub const ADD: &str = "_+_";
    pub const SUBTRACT: &str = "_-_";
    pub const MULTIPLY: &str = "_*_";
    pub const DIVIDE: &str = "_/_";
    pub const MODULO: &str = "_%_";
    pub const INDEX: &str = "_[_]";
    pub const IN: &str = "@in";
    pub const NOT_STRICTLY_FALSE: &str = "@not_strictly_false";
}

impl Expr {
    /// Visit every node, pre-order.
    pub fn walk<'a>(&'a self, f: &mut impl FnMut(&'a Expr)) {
        f(self);
        match &self.kind {
            ExprKind::Literal(_) | ExprKind::Ident(_) => {}
            ExprKind::Select { operand, .. } => operand.walk(f),
            ExprKind::Call { target, args, .. } => {
                if let Some(t) = target {
                    t.walk(f);
                }
                for a in args {
                    a.walk(f);
                }
            }
            ExprKind::List(items) => items.iter().for_each(|e| e.walk(f)),
            ExprKind::Map(entries) => {
                for (k, v) in entries {
                    k.walk(f);
                    v.walk(f);
                }
            }
            ExprKind::Struct { fields, .. } => fields.iter().for_each(|(_, v)| v.walk(f)),
            ExprKind::Comprehension(c) => {
                c.iter_range.walk(f);
                c.accu_init.walk(f);
                c.loop_condition.walk(f);
                c.loop_step.walk(f);
                c.result.walk(f);
            }
        }
    }

    pub fn max_id(&self) -> ExprId {
        let mut m = 0;
        self.walk(&mut |e| m = m.max(e.id));
        m
    }
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Literal::Null => write!(f, "null"),
            Literal::Bool(b) => write!(f, "{b}"),
            Literal::Int(i) => write!(f, "{i}"),
            Literal::Uint(u) => write!(f, "{u}u"),
            Literal::Double(d) => {
                if d.is_finite() && d.fract() == 0.0 && d.abs() < 1e15 {
                    write!(f, "{d:.1}")
                } else {
                    write!(f, "{d:?}")
                }
            }
            Literal::String(s) => write!(f, "{}", quote_string(s)),
            Literal::Bytes(b) => {
                write!(f, "b\"")?;
                for byte in b {
                    match byte {
                        b'"' => write!(f, "\\\"")?,
                        b'\\' => write!(f, "\\\\")?,
                        0x20..=0x7e => write!(f, "{}", *byte as char)?,
                        _ => write!(f, "\\x{byte:02x}")?,
                    }
                }
                write!(f, "\"")
            }
        }
    }
}

pub fn quote_string(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\x{:02x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}
