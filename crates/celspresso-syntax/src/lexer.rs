//! Hand-written CEL lexer producing tokens with byte spans.

use crate::ast::Span;
use crate::error::SyntaxError;

#[derive(Clone, Debug, PartialEq)]
pub enum Tok {
    Ident(String),
    Int(u64),     // magnitude; sign handled by the parser
    Uint(u64),
    Double(f64),
    Str(String),
    Bytes(Vec<u8>),
    True,
    False,
    Null,
    In,
    // punctuation
    Dot,
    Comma,
    Colon,
    Question,
    LParen,
    RParen,
    LBracket,
    RBracket,
    LBrace,
    RBrace,
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    Bang,
    EqEq,
    NotEq,
    Lt,
    Le,
    Gt,
    Ge,
    AndAnd,
    OrOr,
    Eof,
}

impl Tok {
    pub fn describe(&self) -> String {
        match self {
            Tok::Ident(s) => format!("identifier '{s}'"),
            Tok::Int(_) | Tok::Uint(_) | Tok::Double(_) => "number".into(),
            Tok::Str(_) => "string".into(),
            Tok::Bytes(_) => "bytes".into(),
            Tok::Eof => "end of input".into(),
            other => format!("'{}'", other.text()),
        }
    }
    fn text(&self) -> &'static str {
        match self {
            Tok::True => "true",
            Tok::False => "false",
            Tok::Null => "null",
            Tok::In => "in",
            Tok::Dot => ".",
            Tok::Comma => ",",
            Tok::Colon => ":",
            Tok::Question => "?",
            Tok::LParen => "(",
            Tok::RParen => ")",
            Tok::LBracket => "[",
            Tok::RBracket => "]",
            Tok::LBrace => "{",
            Tok::RBrace => "}",
            Tok::Plus => "+",
            Tok::Minus => "-",
            Tok::Star => "*",
            Tok::Slash => "/",
            Tok::Percent => "%",
            Tok::Bang => "!",
            Tok::EqEq => "==",
            Tok::NotEq => "!=",
            Tok::Lt => "<",
            Tok::Le => "<=",
            Tok::Gt => ">",
            Tok::Ge => ">=",
            Tok::AndAnd => "&&",
            Tok::OrOr => "||",
            _ => "?",
        }
    }
}

#[derive(Clone, Debug)]
pub struct Token {
    pub tok: Tok,
    pub span: Span,
}

const RESERVED: &[&str] = &[
    "as", "break", "const", "continue", "else", "for", "function", "if", "import", "let", "loop",
    "package", "namespace", "return", "var", "void", "while",
];

pub fn lex(src: &str) -> Result<Vec<Token>, SyntaxError> {
    let mut lx = Lexer { src, bytes: src.as_bytes(), pos: 0, out: Vec::new() };
    lx.run()?;
    Ok(lx.out)
}

struct Lexer<'a> {
    src: &'a str,
    bytes: &'a [u8],
    pos: usize,
    out: Vec<Token>,
}

impl<'a> Lexer<'a> {
    fn peek(&self) -> Option<u8> {
        self.bytes.get(self.pos).copied()
    }
    fn peek_at(&self, n: usize) -> Option<u8> {
        self.bytes.get(self.pos + n).copied()
    }
    fn push(&mut self, tok: Tok, start: usize) {
        self.out.push(Token { tok, span: Span::new(start, self.pos) });
    }
    fn err(&self, start: usize, msg: impl Into<String>) -> SyntaxError {
        SyntaxError { message: msg.into(), span: Span::new(start, self.pos.max(start + 1).min(self.src.len().max(start + 1))) }
    }

    fn run(&mut self) -> Result<(), SyntaxError> {
        loop {
            self.skip_ws_and_comments();
            let start = self.pos;
            let Some(c) = self.peek() else {
                self.push(Tok::Eof, start);
                return Ok(());
            };
            match c {
                b'0'..=b'9' => self.number()?,
                b'.' if matches!(self.peek_at(1), Some(b'0'..=b'9')) => self.number()?,
                b'"' | b'\'' => {
                    let s = self.string_body(false)?;
                    self.push(Tok::Str(String::from_utf8(s).expect("utf8 string")), start);
                }
                b'r' | b'R' if matches!(self.peek_at(1), Some(b'"' | b'\'')) => {
                    self.pos += 1;
                    let s = self.string_body(true)?;
                    self.push(Tok::Str(String::from_utf8(s).expect("utf8 string")), start);
                }
                b'b' | b'B' if matches!(self.peek_at(1), Some(b'"' | b'\'')) => {
                    self.pos += 1;
                    let s = self.bytes_body(false)?;
                    self.push(Tok::Bytes(s), start);
                }
                b'b' | b'B' if matches!(self.peek_at(1), Some(b'r' | b'R')) && matches!(self.peek_at(2), Some(b'"' | b'\'')) => {
                    self.pos += 2;
                    let s = self.bytes_body(true)?;
                    self.push(Tok::Bytes(s), start);
                }
                b'r' | b'R' if matches!(self.peek_at(1), Some(b'b' | b'B')) && matches!(self.peek_at(2), Some(b'"' | b'\'')) => {
                    self.pos += 2;
                    let s = self.bytes_body(true)?;
                    self.push(Tok::Bytes(s), start);
                }
                c if c == b'_' || c.is_ascii_alphabetic() => {
                    while matches!(self.peek(), Some(c) if c == b'_' || c.is_ascii_alphanumeric()) {
                        self.pos += 1;
                    }
                    let word = &self.src[start..self.pos];
                    let tok = match word {
                        "true" => Tok::True,
                        "false" => Tok::False,
                        "null" => Tok::Null,
                        "in" => Tok::In,
                        w if RESERVED.contains(&w) => {
                            return Err(self.err(start, format!("reserved identifier '{w}'")));
                        }
                        w => Tok::Ident(w.to_string()),
                    };
                    self.push(tok, start);
                }
                _ => {
                    let two = (c, self.peek_at(1));
                    let (tok, len) = match two {
                        (b'=', Some(b'=')) => (Tok::EqEq, 2),
                        (b'!', Some(b'=')) => (Tok::NotEq, 2),
                        (b'<', Some(b'=')) => (Tok::Le, 2),
                        (b'>', Some(b'=')) => (Tok::Ge, 2),
                        (b'&', Some(b'&')) => (Tok::AndAnd, 2),
                        (b'|', Some(b'|')) => (Tok::OrOr, 2),
                        (b'.', _) => (Tok::Dot, 1),
                        (b',', _) => (Tok::Comma, 1),
                        (b':', _) => (Tok::Colon, 1),
                        (b'?', _) => (Tok::Question, 1),
                        (b'(', _) => (Tok::LParen, 1),
                        (b')', _) => (Tok::RParen, 1),
                        (b'[', _) => (Tok::LBracket, 1),
                        (b']', _) => (Tok::RBracket, 1),
                        (b'{', _) => (Tok::LBrace, 1),
                        (b'}', _) => (Tok::RBrace, 1),
                        (b'+', _) => (Tok::Plus, 1),
                        (b'-', _) => (Tok::Minus, 1),
                        (b'*', _) => (Tok::Star, 1),
                        (b'/', _) => (Tok::Slash, 1),
                        (b'%', _) => (Tok::Percent, 1),
                        (b'!', _) => (Tok::Bang, 1),
                        (b'<', _) => (Tok::Lt, 1),
                        (b'>', _) => (Tok::Gt, 1),
                        _ => {
                            let ch = self.src[start..].chars().next().unwrap();
                            self.pos += ch.len_utf8();
                            return Err(self.err(start, format!("unexpected character '{ch}'")));
                        }
                    };
                    self.pos += len;
                    self.push(tok, start);
                }
            }
        }
    }

    fn skip_ws_and_comments(&mut self) {
        loop {
            match self.peek() {
                Some(b' ' | b'\t' | b'\n' | b'\r' | 0x0c) => self.pos += 1,
                Some(b'/') if self.peek_at(1) == Some(b'/') => {
                    while !matches!(self.peek(), None | Some(b'\n')) {
                        self.pos += 1;
                    }
                }
                _ => return,
            }
        }
    }

    fn number(&mut self) -> Result<(), SyntaxError> {
        let start = self.pos;
        if self.peek() == Some(b'0') && matches!(self.peek_at(1), Some(b'x' | b'X')) {
            self.pos += 2;
            let ds = self.pos;
            while matches!(self.peek(), Some(c) if c.is_ascii_hexdigit()) {
                self.pos += 1;
            }
            let digits = &self.src[ds..self.pos];
            let v = u64::from_str_radix(digits, 16).map_err(|_| self.err(start, "invalid hex literal"))?;
            return self.int_suffix(v, start);
        }
        let mut is_float = false;
        while matches!(self.peek(), Some(b'0'..=b'9')) {
            self.pos += 1;
        }
        if self.peek() == Some(b'.') && matches!(self.peek_at(1), Some(b'0'..=b'9')) {
            is_float = true;
            self.pos += 1;
            while matches!(self.peek(), Some(b'0'..=b'9')) {
                self.pos += 1;
            }
        }
        if matches!(self.peek(), Some(b'e' | b'E')) {
            let save = self.pos;
            self.pos += 1;
            if matches!(self.peek(), Some(b'+' | b'-')) {
                self.pos += 1;
            }
            if matches!(self.peek(), Some(b'0'..=b'9')) {
                is_float = true;
                while matches!(self.peek(), Some(b'0'..=b'9')) {
                    self.pos += 1;
                }
            } else {
                self.pos = save;
            }
        }
        let text = &self.src[start..self.pos];
        if is_float {
            let v: f64 = text.parse().map_err(|_| self.err(start, "invalid floating point literal"))?;
            self.push(Tok::Double(v), start);
            Ok(())
        } else {
            let v: u64 = text.parse().map_err(|_| self.err(start, "integer literal out of range"))?;
            self.int_suffix(v, start)
        }
    }

    fn int_suffix(&mut self, v: u64, start: usize) -> Result<(), SyntaxError> {
        if matches!(self.peek(), Some(b'u' | b'U')) {
            self.pos += 1;
            self.push(Tok::Uint(v), start);
        } else {
            self.push(Tok::Int(v), start);
        }
        Ok(())
    }

    /// Lex a quoted string body starting at the quote. Returns UTF-8 bytes.
    fn string_body(&mut self, raw: bool) -> Result<Vec<u8>, SyntaxError> {
        self.quoted(raw, false)
    }

    fn bytes_body(&mut self, raw: bool) -> Result<Vec<u8>, SyntaxError> {
        self.quoted(raw, true)
    }

    fn quoted(&mut self, raw: bool, is_bytes: bool) -> Result<Vec<u8>, SyntaxError> {
        let start = self.pos;
        let q = self.peek().unwrap();
        let triple = self.peek_at(1) == Some(q) && self.peek_at(2) == Some(q);
        self.pos += if triple { 3 } else { 1 };
        let mut out = Vec::new();
        loop {
            let Some(c) = self.peek() else {
                return Err(self.err(start, "unterminated string literal"));
            };
            if c == q {
                if !triple {
                    self.pos += 1;
                    return Ok(out);
                }
                if self.peek_at(1) == Some(q) && self.peek_at(2) == Some(q) {
                    self.pos += 3;
                    return Ok(out);
                }
            }
            if !triple && (c == b'\n' || c == b'\r') {
                return Err(self.err(start, "newline in string literal"));
            }
            if c == b'\\' && !raw {
                self.escape(&mut out, is_bytes, start)?;
                continue;
            }
            // copy one UTF-8 char
            let ch = self.src[self.pos..].chars().next().unwrap();
            let mut buf = [0u8; 4];
            out.extend_from_slice(ch.encode_utf8(&mut buf).as_bytes());
            self.pos += ch.len_utf8();
        }
    }

    fn escape(&mut self, out: &mut Vec<u8>, is_bytes: bool, start: usize) -> Result<(), SyntaxError> {
        let esc_start = self.pos;
        self.pos += 1; // backslash
        let Some(c) = self.peek() else {
            return Err(self.err(start, "unterminated string literal"));
        };
        self.pos += 1;
        let simple = match c {
            b'a' => Some(0x07),
            b'b' => Some(0x08),
            b'f' => Some(0x0c),
            b'n' => Some(b'\n'),
            b'r' => Some(b'\r'),
            b't' => Some(b'\t'),
            b'v' => Some(0x0b),
            b'\\' => Some(b'\\'),
            b'\'' => Some(b'\''),
            b'"' => Some(b'"'),
            b'`' => Some(b'`'),
            b'?' => Some(b'?'),
            _ => None,
        };
        if let Some(b) = simple {
            out.push(b);
            return Ok(());
        }
        let hex = |lx: &mut Self, n: usize| -> Result<u32, SyntaxError> {
            let s = lx.src.get(lx.pos..lx.pos + n).ok_or_else(|| lx.err(esc_start, "invalid escape sequence"))?;
            let v = u32::from_str_radix(s, 16).map_err(|_| lx.err(esc_start, "invalid escape sequence"))?;
            lx.pos += n;
            Ok(v)
        };
        match c {
            b'x' | b'X' => {
                let v = hex(self, 2)?;
                if is_bytes {
                    out.push(v as u8);
                } else {
                    push_char(out, v).ok_or_else(|| self.err(esc_start, "invalid code point"))?;
                }
            }
            b'u' | b'U' => {
                if is_bytes {
                    return Err(self.err(esc_start, "unicode escape not allowed in bytes literal"));
                }
                let v = hex(self, if c == b'u' { 4 } else { 8 })?;
                push_char(out, v).ok_or_else(|| self.err(esc_start, "invalid code point"))?;
            }
            b'0'..=b'3' => {
                let s = self.src.get(self.pos - 1..self.pos + 2).ok_or_else(|| self.err(esc_start, "invalid octal escape"))?;
                let v = u32::from_str_radix(s, 8).map_err(|_| self.err(esc_start, "invalid octal escape"))?;
                self.pos += 2;
                if is_bytes {
                    out.push(v as u8);
                } else {
                    push_char(out, v).ok_or_else(|| self.err(esc_start, "invalid code point"))?;
                }
            }
            _ => return Err(self.err(esc_start, "invalid escape sequence")),
        }
        Ok(())
    }
}

fn push_char(out: &mut Vec<u8>, cp: u32) -> Option<()> {
    let ch = char::from_u32(cp)?;
    let mut buf = [0u8; 4];
    out.extend_from_slice(ch.encode_utf8(&mut buf).as_bytes());
    Some(())
}
