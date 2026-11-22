//! Recursive-descent / precedence-climbing parser for CEL, with macro expansion.

use crate::ast::*;
use crate::error::SyntaxError;
use crate::lexer::{lex, Tok, Token};

/// Parser limits that protect against hostile input.
#[derive(Clone, Copy, Debug)]
pub struct ParseLimits {
    pub max_source_len: usize,
    pub max_depth: usize,
}

impl Default for ParseLimits {
    fn default() -> Self {
        ParseLimits { max_source_len: 100_000, max_depth: 200 }
    }
}

pub fn parse(src: &str) -> Result<Expr, SyntaxError> {
    parse_with_limits(src, ParseLimits::default())
}

pub fn parse_with_limits(src: &str, limits: ParseLimits) -> Result<Expr, SyntaxError> {
    if src.len() > limits.max_source_len {
        return Err(SyntaxError {
            message: format!("expression exceeds maximum length of {} bytes", limits.max_source_len),
            span: Span::new(0, 0),
        });
    }
    let tokens = lex(src)?;
    let mut p = Parser { tokens, pos: 0, next_id: 1, depth: 0, limits };
    let e = p.expr()?;
    if p.peek() != &Tok::Eof {
        return Err(p.unexpected("end of expression"));
    }
    Ok(e)
}

struct Parser {
    tokens: Vec<Token>,
    pos: usize,
    next_id: ExprId,
    depth: usize,
    limits: ParseLimits,
}

type PResult = Result<Expr, SyntaxError>;

impl Parser {
    fn peek(&self) -> &Tok {
        &self.tokens[self.pos].tok
    }
    fn peek_span(&self) -> Span {
        self.tokens[self.pos].span
    }
    fn advance(&mut self) -> Token {
        let t = self.tokens[self.pos].clone();
        if t.tok != Tok::Eof {
            self.pos += 1;
        }
        t
    }
    fn eat(&mut self, t: &Tok) -> bool {
        if self.peek() == t {
            self.advance();
            true
        } else {
            false
        }
    }
    fn expect(&mut self, t: Tok, what: &str) -> Result<Span, SyntaxError> {
        if self.peek() == &t {
            Ok(self.advance().span)
        } else {
            Err(self.unexpected(what))
        }
    }
    fn unexpected(&self, expected: &str) -> SyntaxError {
        SyntaxError {
            message: format!("expected {expected}, found {}", self.peek().describe()),
            span: self.peek_span(),
        }
    }
    fn id(&mut self) -> ExprId {
        let id = self.next_id;
        self.next_id += 1;
        id
    }
    fn mk(&mut self, span: Span, kind: ExprKind) -> Expr {
        Expr { id: self.id(), span, kind }
    }
    fn call(&mut self, span: Span, function: &str, args: Vec<Expr>) -> Expr {
        self.mk(span, ExprKind::Call { target: None, function: function.to_string(), args })
    }
    fn enter(&mut self) -> Result<(), SyntaxError> {
        self.depth += 1;
        if self.depth > self.limits.max_depth {
            return Err(SyntaxError {
                message: format!("expression nesting exceeds maximum depth of {}", self.limits.max_depth),
                span: self.peek_span(),
            });
        }
        Ok(())
    }

    fn expr(&mut self) -> PResult {
        self.enter()?;
        let cond = self.or()?;
        let r = if self.eat(&Tok::Question) {
            let t = self.or()?;
            self.expect(Tok::Colon, "':'")?;
            let f = self.expr()?;
            let span = cond.span.to(f.span);
            Ok(self.call(span, ops::CONDITIONAL, vec![cond, t, f]))
        } else {
            Ok(cond)
        };
        self.depth -= 1;
        r
    }

    fn or(&mut self) -> PResult {
        let mut lhs = self.and()?;
        while self.eat(&Tok::OrOr) {
            let rhs = self.and()?;
            let span = lhs.span.to(rhs.span);
            lhs = self.call(span, ops::LOGICAL_OR, vec![lhs, rhs]);
        }
        Ok(lhs)
    }

    fn and(&mut self) -> PResult {
        let mut lhs = self.relation()?;
        while self.eat(&Tok::AndAnd) {
            let rhs = self.relation()?;
            let span = lhs.span.to(rhs.span);
            lhs = self.call(span, ops::LOGICAL_AND, vec![lhs, rhs]);
        }
        Ok(lhs)
    }

    fn relation(&mut self) -> PResult {
        let mut lhs = self.addition()?;
        loop {
            let op = match self.peek() {
                Tok::Lt => ops::LESS,
                Tok::Le => ops::LESS_EQUALS,
                Tok::Gt => ops::GREATER,
                Tok::Ge => ops::GREATER_EQUALS,
                Tok::EqEq => ops::EQUALS,
                Tok::NotEq => ops::NOT_EQUALS,
                Tok::In => ops::IN,
                _ => return Ok(lhs),
            };
            self.advance();
            let rhs = self.addition()?;
            let span = lhs.span.to(rhs.span);
            lhs = self.call(span, op, vec![lhs, rhs]);
        }
    }

    fn addition(&mut self) -> PResult {
        let mut lhs = self.multiplication()?;
        loop {
            let op = match self.peek() {
                Tok::Plus => ops::ADD,
                Tok::Minus => ops::SUBTRACT,
                _ => return Ok(lhs),
            };
            self.advance();
            let rhs = self.multiplication()?;
            let span = lhs.span.to(rhs.span);
            lhs = self.call(span, op, vec![lhs, rhs]);
        }
    }

    fn multiplication(&mut self) -> PResult {
        let mut lhs = self.unary()?;
        loop {
            let op = match self.peek() {
                Tok::Star => ops::MULTIPLY,
                Tok::Slash => ops::DIVIDE,
                Tok::Percent => ops::MODULO,
                _ => return Ok(lhs),
            };
            self.advance();
            let rhs = self.unary()?;
            let span = lhs.span.to(rhs.span);
            lhs = self.call(span, op, vec![lhs, rhs]);
        }
    }

    fn unary(&mut self) -> PResult {
        self.enter()?;
        let start = self.peek_span();
        let r = match self.peek() {
            Tok::Bang => {
                self.advance();
                let operand = self.unary()?;
                let span = start.to(operand.span);
                Ok(self.call(span, ops::LOGICAL_NOT, vec![operand]))
            }
            Tok::Minus => {
                self.advance();
                // Fold negative numeric literals so that -9223372036854775808 parses.
                match self.peek().clone() {
                    Tok::Int(v) if !self.followed_by_member_access() => {
                        let t = self.advance();
                        let span = start.to(t.span);
                        if v > (i64::MAX as u64) + 1 {
                            return Err(SyntaxError { message: "integer literal out of range".into(), span });
                        }
                        let n = if v == (i64::MAX as u64) + 1 { i64::MIN } else { -(v as i64) };
                        Ok(self.mk(span, ExprKind::Literal(Literal::Int(n))))
                    }
                    Tok::Double(v) if !self.followed_by_member_access() => {
                        let t = self.advance();
                        Ok(self.mk(start.to(t.span), ExprKind::Literal(Literal::Double(-v))))
                    }
                    _ => {
                        let operand = self.unary()?;
                        let span = start.to(operand.span);
                        Ok(self.call(span, ops::NEGATE, vec![operand]))
                    }
                }
            }
            _ => self.member(),
        };
        self.depth -= 1;
        r
    }

    fn followed_by_member_access(&self) -> bool {
        matches!(self.tokens.get(self.pos + 1).map(|t| &t.tok), Some(Tok::Dot | Tok::LBracket))
    }

    fn member(&mut self) -> PResult {
        let mut e = self.primary()?;
        loop {
            match self.peek() {
                Tok::Dot => {
                    self.advance();
                    let (name, nspan) = self.ident("field or method name")?;
                    if self.peek() == &Tok::LParen {
                        self.advance();
                        let args = self.expr_list(Tok::RParen)?;
                        let end = self.expect(Tok::RParen, "')'")?;
                        let span = e.span.to(end);
                        e = self.receiver_call(span, e, name, args)?;
                    } else {
                        let span = e.span.to(nspan);
                        e = self.mk(span, ExprKind::Select { operand: Box::new(e), field: name, test_only: false });
                    }
                }
                Tok::LBracket => {
                    self.advance();
                    let idx = self.expr()?;
                    let end = self.expect(Tok::RBracket, "']'")?;
                    let span = e.span.to(end);
                    e = self.call(span, ops::INDEX, vec![e, idx]);
                }
                Tok::LBrace if qualified_name(&e).is_some() => {
                    let type_name = qualified_name(&e).unwrap();
                    self.advance();
                    let mut fields = Vec::new();
                    while self.peek() != &Tok::RBrace {
                        let (f, _) = self.ident("field name")?;
                        self.expect(Tok::Colon, "':'")?;
                        let v = self.expr()?;
                        fields.push((f, v));
                        if !self.eat(&Tok::Comma) {
                            break;
                        }
                    }
                    let end = self.expect(Tok::RBrace, "'}'")?;
                    let span = e.span.to(end);
                    e = self.mk(span, ExprKind::Struct { type_name, fields });
                }
                _ => return Ok(e),
            }
        }
    }

    fn ident(&mut self, what: &str) -> Result<(String, Span), SyntaxError> {
        match self.peek().clone() {
            Tok::Ident(s) => {
                let t = self.advance();
                Ok((s, t.span))
            }
            _ => Err(self.unexpected(what)),
        }
    }

    fn expr_list(&mut self, close: Tok) -> Result<Vec<Expr>, SyntaxError> {
        let mut out = Vec::new();
        while self.peek() != &close {
            out.push(self.expr()?);
            if !self.eat(&Tok::Comma) {
                break;
            }
        }
        Ok(out)
    }

    fn primary(&mut self) -> PResult {
        let t = self.advance();
        let span = t.span;
        let lit = |p: &mut Self, l: Literal| Ok(p.mk(span, ExprKind::Literal(l)));
        match t.tok {
            Tok::Int(v) => {
                if v > i64::MAX as u64 {
                    return Err(SyntaxError { message: "integer literal out of range".into(), span });
                }
                lit(self, Literal::Int(v as i64))
            }
            Tok::Uint(v) => lit(self, Literal::Uint(v)),
            Tok::Double(v) => lit(self, Literal::Double(v)),
            Tok::Str(s) => lit(self, Literal::String(s)),
            Tok::Bytes(b) => lit(self, Literal::Bytes(b)),
            Tok::True => lit(self, Literal::Bool(true)),
            Tok::False => lit(self, Literal::Bool(false)),
            Tok::Null => lit(self, Literal::Null),
            Tok::Dot => {
                // leading-dot qualified identifier: `.pkg.name`
                let (name, nspan) = self.ident("identifier")?;
                self.ident_or_call(format!(".{name}"), span.to(nspan))
            }
            Tok::Ident(name) => self.ident_or_call(name, span),
            Tok::LParen => {
                let e = self.expr()?;
                self.expect(Tok::RParen, "')'")?;
                Ok(e)
            }
            Tok::LBracket => {
                let items = self.expr_list(Tok::RBracket)?;
                let end = self.expect(Tok::RBracket, "']'")?;
                Ok(self.mk(span.to(end), ExprKind::List(items)))
            }
            Tok::LBrace => {
                let mut entries = Vec::new();
                while self.peek() != &Tok::RBrace {
                    let k = self.expr()?;
                    self.expect(Tok::Colon, "':'")?;
                    let v = self.expr()?;
                    entries.push((k, v));
                    if !self.eat(&Tok::Comma) {
                        break;
                    }
                }
                let end = self.expect(Tok::RBrace, "'}'")?;
                Ok(self.mk(span.to(end), ExprKind::Map(entries)))
            }
            other => {
                self.pos -= usize::from(other != Tok::Eof);
                Err(self.unexpected("expression"))
            }
        }
    }

    fn ident_or_call(&mut self, name: String, span: Span) -> PResult {
        if self.peek() == &Tok::LParen {
            self.advance();
            let args = self.expr_list(Tok::RParen)?;
            let end = self.expect(Tok::RParen, "')'")?;
            let span = span.to(end);
            if name == "has" {
                return self.expand_has(span, args);
            }
            Ok(self.mk(span, ExprKind::Call { target: None, function: name, args }))
        } else {
            Ok(self.mk(span, ExprKind::Ident(name)))
        }
    }

    fn expand_has(&mut self, span: Span, mut args: Vec<Expr>) -> PResult {
        if args.len() != 1 {
            return Err(SyntaxError { message: "has() requires exactly one argument".into(), span });
        }
        let arg = args.pop().unwrap();
        match arg.kind {
            ExprKind::Select { operand, field, test_only: false } => {
                Ok(self.mk(span, ExprKind::Select { operand, field, test_only: true }))
            }
            _ => Err(SyntaxError { message: "invalid argument to has() macro: expected a field selection".into(), span: arg.span }),
        }
    }

    fn receiver_call(&mut self, span: Span, target: Expr, name: String, args: Vec<Expr>) -> PResult {
        let is_macro = matches!(
            (name.as_str(), args.len()),
            ("all", 2) | ("exists", 2) | ("exists_one", 2) | ("existsOne", 2) | ("map", 2) | ("map", 3) | ("filter", 2)
        );
        if !is_macro {
            return Ok(self.mk(span, ExprKind::Call { target: Some(Box::new(target)), function: name, args }));
        }
        let iter_var = match &args[0].kind {
            ExprKind::Ident(v) => v.clone(),
            _ => {
                return Err(SyntaxError {
                    message: format!("argument to {name}() must be a simple identifier"),
                    span: args[0].span,
                })
            }
        };
        if iter_var == ACCU_VAR {
            return Err(SyntaxError { message: "iteration variable overwrites accumulator variable".into(), span: args[0].span });
        }
        let mut args = args.into_iter().skip(1);
        let accu = |p: &mut Self| p.mk(span, ExprKind::Ident(ACCU_VAR.to_string()));
        let lit = |p: &mut Self, l: Literal| p.mk(span, ExprKind::Literal(l));
        let (init, cond, step, result) = match name.as_str() {
            "all" => {
                let pred = args.next().unwrap();
                let init = lit(self, Literal::Bool(true));
                let a = accu(self);
                let cond = self.call(span, ops::NOT_STRICTLY_FALSE, vec![a]);
                let a = accu(self);
                let step = self.call(span, ops::LOGICAL_AND, vec![a, pred]);
                (init, cond, step, accu(self))
            }
            "exists" => {
                let pred = args.next().unwrap();
                let init = lit(self, Literal::Bool(false));
                let a = accu(self);
                let not_a = self.call(span, ops::LOGICAL_NOT, vec![a]);
                let cond = self.call(span, ops::NOT_STRICTLY_FALSE, vec![not_a]);
                let a = accu(self);
                let step = self.call(span, ops::LOGICAL_OR, vec![a, pred]);
                (init, cond, step, accu(self))
            }
            "exists_one" | "existsOne" => {
                let pred = args.next().unwrap();
                let init = lit(self, Literal::Int(0));
                let cond = lit(self, Literal::Bool(true));
                let a = accu(self);
                let one = lit(self, Literal::Int(1));
                let inc = self.call(span, ops::ADD, vec![a, one]);
                let a = accu(self);
                let step = self.call(span, ops::CONDITIONAL, vec![pred, inc, a]);
                let a = accu(self);
                let one = lit(self, Literal::Int(1));
                let result = self.call(span, ops::EQUALS, vec![a, one]);
                (init, cond, step, result)
            }
            "map" => {
                let first = args.next().unwrap();
                let (filter, transform) = match args.next() {
                    Some(t) => (Some(first), t),
                    None => (None, first),
                };
                let init = self.mk(span, ExprKind::List(vec![]));
                let cond = lit(self, Literal::Bool(true));
                let a = accu(self);
                let single = self.mk(transform.span, ExprKind::List(vec![transform]));
                let appended = self.call(span, ops::ADD, vec![a, single]);
                let step = match filter {
                    Some(f) => {
                        let a = accu(self);
                        self.call(span, ops::CONDITIONAL, vec![f, appended, a])
                    }
                    None => appended,
                };
                (init, cond, step, accu(self))
            }
            "filter" => {
                let pred = args.next().unwrap();
                let init = self.mk(span, ExprKind::List(vec![]));
                let cond = lit(self, Literal::Bool(true));
                let a = accu(self);
                let x = self.mk(span, ExprKind::Ident(iter_var.clone()));
                let single = self.mk(span, ExprKind::List(vec![x]));
                let appended = self.call(span, ops::ADD, vec![a, single]);
                let a = accu(self);
                let step = self.call(span, ops::CONDITIONAL, vec![pred, appended, a]);
                (init, cond, step, accu(self))
            }
            _ => unreachable!(),
        };
        let macro_name = if name == "existsOne" { "exists_one".to_string() } else { name };
        Ok(self.mk(
            span,
            ExprKind::Comprehension(Box::new(Comprehension {
                iter_var,
                iter_range: target,
                accu_var: ACCU_VAR.to_string(),
                accu_init: init,
                loop_condition: cond,
                loop_step: step,
                result,
                macro_name,
            })),
        ))
    }
}

/// If `e` is a (possibly dotted) identifier, return its qualified name.
pub fn qualified_name(e: &Expr) -> Option<String> {
    match &e.kind {
        ExprKind::Ident(n) => Some(n.clone()),
        ExprKind::Select { operand, field, test_only: false } => {
            qualified_name(operand).map(|q| format!("{q}.{field}"))
        }
        _ => None,
    }
}
