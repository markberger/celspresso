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
    /// A copy of `e` with fresh ids, for macros that repeat a subexpression.
    fn renumber(&mut self, e: &Expr) -> Expr {
        let mut e = e.clone();
        e.walk_mut(&mut |n| n.id = self.id());
        e
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
                Tok::Dot if matches!(self.tokens.get(self.pos + 1).map(|t| &t.tok), Some(Tok::Question)) => {
                    e = self.opt_select(e)?;
                }
                Tok::Dot => {
                    self.advance();
                    let quoted = matches!(self.peek(), Tok::QuotedIdent(_));
                    let (name, nspan) = self.member_name()?;
                    if self.peek() == &Tok::LParen && !quoted {
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
                    let optional = self.eat(&Tok::Question);
                    let idx = self.expr()?;
                    let end = self.expect(Tok::RBracket, "']'")?;
                    let span = e.span.to(end);
                    e = self.call(span, if optional { ops::OPT_INDEX } else { ops::INDEX }, vec![e, idx]);
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
            Tok::Reserved(w) => {
                let span = self.advance().span;
                Err(SyntaxError { message: format!("reserved identifier '{w}'"), span })
            }
            _ => Err(self.unexpected(what)),
        }
    }

    /// The name after `.`: identifiers, reserved words and backtick-quoted names are all allowed.
    fn member_name(&mut self) -> Result<(String, Span), SyntaxError> {
        match self.peek().clone() {
            Tok::Ident(s) | Tok::Reserved(s) | Tok::QuotedIdent(s) => {
                let t = self.advance();
                Ok((s, t.span))
            }
            _ => Err(self.unexpected("field or method name")),
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
            Tok::Reserved(w) => Err(SyntaxError { message: format!("reserved identifier '{w}'"), span }),
            Tok::LParen => {
                let e = self.expr()?;
                self.expect(Tok::RParen, "')'")?;
                Ok(e)
            }
            Tok::LBracket => {
                let mut items = Vec::new();
                while self.peek() != &Tok::RBracket {
                    items.push(self.maybe_optional_entry()?);
                    if !self.eat(&Tok::Comma) {
                        break;
                    }
                }
                let end = self.expect(Tok::RBracket, "']'")?;
                Ok(self.mk(span.to(end), ExprKind::List(items)))
            }
            Tok::LBrace => {
                let mut entries = Vec::new();
                while self.peek() != &Tok::RBrace {
                    let optional = self.eat(&Tok::Question);
                    let k = self.expr()?;
                    self.expect(Tok::Colon, "':'")?;
                    let mut v = self.expr()?;
                    if optional {
                        v = self.call(v.span, ops::OPT_ENTRY, vec![v]);
                    }
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

    /// `e.?field` (the `.` is the current token).
    #[inline(never)]
    fn opt_select(&mut self, e: Expr) -> PResult {
        self.advance();
        self.advance();
        let (name, nspan) = self.member_name()?;
        let span = e.span.to(nspan);
        let field = self.mk(nspan, ExprKind::Literal(Literal::String(name)));
        Ok(self.call(span, ops::OPT_SELECT, vec![e, field]))
    }

    /// A list element, possibly marked optional with a leading `?`.
    fn maybe_optional_entry(&mut self) -> PResult {
        let optional = self.eat(&Tok::Question);
        let e = self.expr()?;
        Ok(if optional { self.call(e.span, ops::OPT_ENTRY, vec![e]) } else { e })
    }

    fn receiver_call(&mut self, span: Span, target: Expr, name: String, args: Vec<Expr>) -> PResult {
        if (name == "optMap" || name == "optFlatMap") && args.len() == 2 {
            return self.opt_map_macro(span, target, &name, args);
        }
        if matches!(&target.kind, ExprKind::Ident(n) if n == "cel") {
            match (name.as_str(), args.len()) {
                ("bind", 3) => return self.bind_macro(span, args),
                ("block", 2) => return self.block_macro(span, args),
                ("index", 1) | ("iterVar" | "accuVar", 2) => return self.block_var(span, &name, &args),
                _ => {}
            }
        }
        if name == "sortBy" && args.len() == 2 {
            // xs.sortBy(e, key) => @sortByAssociatedKeys(xs, xs.map(e, key))
            let copy = self.renumber(&target);
            let keys = self.receiver_call(span, copy, "map".into(), args)?;
            return Ok(self.call(span, "@sortByAssociatedKeys", vec![target, keys]));
        }
        // (macro, number of iteration variables) for every receiver-style macro
        let vars = match (name.as_str(), args.len()) {
            ("all" | "exists" | "exists_one" | "existsOne" | "filter", 2) | ("map", 2 | 3) => 1,
            ("all" | "exists" | "exists_one" | "existsOne", 3) => 2,
            ("transformList" | "transformMap" | "transformMapEntry", 3 | 4) => 2,
            _ => return Ok(self.mk(span, ExprKind::Call { target: Some(Box::new(target)), function: name, args })),
        };
        let mut names = Vec::new();
        for a in &args[..vars] {
            match &a.kind {
                ExprKind::Ident(v) if v == ACCU_VAR => {
                    return Err(SyntaxError { message: "iteration variable overwrites accumulator variable".into(), span: a.span })
                }
                ExprKind::Ident(v) => names.push(v.clone()),
                _ => {
                    return Err(SyntaxError { message: format!("argument to {name}() must be a simple identifier"), span: a.span })
                }
            }
        }
        if vars == 2 && names[0] == names[1] {
            return Err(SyntaxError { message: format!("duplicate variable name '{}' in {name}()", names[0]), span: args[1].span });
        }
        let iter_var = names[0].clone();
        let iter_var2 = names.get(1).cloned();
        let mut args = args.into_iter().skip(vars);
        let accu = |p: &mut Self| p.mk(span, ExprKind::Ident(ACCU_VAR.to_string()));
        let lit = |p: &mut Self, l: Literal| p.mk(span, ExprKind::Literal(l));
        // value bound to the element: the single variable, or the second of two
        let elem_var = iter_var2.clone().unwrap_or_else(|| iter_var.clone());
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
            "map" | "transformList" | "transformMap" | "transformMapEntry" => {
                let first = args.next().unwrap();
                let (filter, transform) = match args.next() {
                    Some(t) => (Some(first), t),
                    None => (None, first),
                };
                let to_map = name != "map" && name != "transformList";
                let init = self.mk(span, if to_map { ExprKind::Map(vec![]) } else { ExprKind::List(vec![]) });
                let cond = lit(self, Literal::Bool(true));
                let a = accu(self);
                let updated = match name.as_str() {
                    "transformMap" => {
                        let k = self.mk(span, ExprKind::Ident(iter_var.clone()));
                        self.call(span, ops::MAP_INSERT, vec![a, k, transform])
                    }
                    "transformMapEntry" => self.call(span, ops::MAP_INSERT, vec![a, transform]),
                    _ => {
                        let single = self.mk(transform.span, ExprKind::List(vec![transform]));
                        self.call(span, ops::ADD, vec![a, single])
                    }
                };
                let step = match filter {
                    Some(f) => {
                        let a = accu(self);
                        self.call(span, ops::CONDITIONAL, vec![f, updated, a])
                    }
                    None => updated,
                };
                (init, cond, step, accu(self))
            }
            "filter" => {
                let pred = args.next().unwrap();
                let init = self.mk(span, ExprKind::List(vec![]));
                let cond = lit(self, Literal::Bool(true));
                let a = accu(self);
                let x = self.mk(span, ExprKind::Ident(elem_var));
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
                iter_var2,
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

impl Parser {
    /// `cel.bind(x, init, body)`: evaluate `body` with `x` bound to `init`. Expands to a
    /// comprehension over an empty list whose accumulator is `x`.
    fn bind_macro(&mut self, span: Span, args: Vec<Expr>) -> PResult {
        let mut args = args.into_iter();
        let var = args.next().unwrap();
        let ExprKind::Ident(name) = &var.kind else {
            return Err(SyntaxError { message: "cel.bind() variable must be a simple identifier".into(), span: var.span });
        };
        let name = name.clone();
        let (init, body) = (args.next().unwrap(), args.next().unwrap());
        Ok(self.bind(span, name, init, body, "cel.bind"))
    }

    /// `cel.index(i)`, `cel.iterVar(i, j)`, `cel.accuVar(i, j)`: the slot and loop variables
    /// of `cel.block`, as identifiers user code cannot spell (`@index0`, `@it:0:0`, `@ac:0:0`).
    fn block_var(&mut self, span: Span, name: &str, args: &[Expr]) -> PResult {
        let mut nums = Vec::new();
        for a in args {
            match &a.kind {
                ExprKind::Literal(Literal::Int(i)) if *i >= 0 => nums.push(*i),
                _ => return Err(SyntaxError { message: format!("cel.{name}() requires non-negative integer literals"), span: a.span }),
            }
        }
        let ident = match (name, nums.as_slice()) {
            ("index", [i]) => format!("{BLOCK_INDEX}{i}"),
            ("iterVar", [i, j]) => format!("{BLOCK_ITER}{i}:{j}"),
            (_, [i, j]) => format!("{BLOCK_ACCU}{i}:{j}"),
            _ => unreachable!(),
        };
        Ok(self.mk(span, ExprKind::Ident(ident)))
    }

    /// `cel.block([e0, e1, ...], body)`: each slot `cel.index(i)` is bound to `ei` (which may
    /// refer to earlier slots), as nested binds.
    fn block_macro(&mut self, span: Span, args: Vec<Expr>) -> PResult {
        let mut args = args.into_iter();
        let slots = args.next().unwrap();
        let body = args.next().unwrap();
        let ExprKind::List(items) = slots.kind else {
            return Err(SyntaxError { message: "cel.block() requires a list literal of slots".into(), span: slots.span });
        };
        let mut out = body;
        for (i, init) in items.into_iter().enumerate().rev() {
            out = self.bind(span, format!("{BLOCK_INDEX}{i}"), init, out, "cel.block");
        }
        Ok(out)
    }

    /// `opt.optMap(x, e)` => `opt.hasValue() ? optional.of(bind(x, opt.value(), e)) : optional.none()`;
    /// `optFlatMap` is the same without the `optional.of` wrapper.
    fn opt_map_macro(&mut self, span: Span, target: Expr, name: &str, args: Vec<Expr>) -> PResult {
        let mut args = args.into_iter();
        let var = args.next().unwrap();
        let ExprKind::Ident(var_name) = &var.kind else {
            return Err(SyntaxError { message: format!("{name}() variable name must be a simple identifier"), span: var.span });
        };
        let var_name = var_name.clone();
        let body = args.next().unwrap();
        let mk_call = |p: &mut Self, t: &Expr, f: &str| {
            let t = p.renumber(t);
            p.mk(span, ExprKind::Call { target: Some(Box::new(t)), function: f.into(), args: vec![] })
        };
        let has = mk_call(self, &target, "hasValue");
        let value = mk_call(self, &target, "value");
        let mut then = self.bind(span, var_name, value, body, name);
        if name == "optMap" {
            then = self.call(span, "optional.of", vec![then]);
        }
        let none = self.call(span, "optional.none", vec![]);
        Ok(self.call(span, ops::CONDITIONAL, vec![has, then, none]))
    }

    fn bind(&mut self, span: Span, name: String, init: Expr, body: Expr, macro_name: &str) -> Expr {
        let range = self.mk(span, ExprKind::List(vec![]));
        let cond = self.mk(span, ExprKind::Literal(Literal::Bool(false)));
        let step = self.mk(span, ExprKind::Ident(name.clone()));
        self.mk(
            span,
            ExprKind::Comprehension(Box::new(Comprehension {
                iter_var: "#unused".into(),
                iter_var2: None,
                iter_range: range,
                accu_var: name,
                accu_init: init,
                loop_condition: cond,
                loop_step: step,
                result: body,
                macro_name: macro_name.into(),
            })),
        )
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
