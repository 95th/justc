use crate::{
    err::{Handler, Result},
    token::{Span, Token, TokenKind, TokenKind::*},
};
use std::collections::HashMap;

pub struct Scanner<'a> {
    pub src: &'a str,
    pub tokens: Vec<Token>,
    start_pos: usize,
    pos: usize,
    line: usize,
    keywords: HashMap<&'static str, TokenKind>,
    handler: &'a mut Handler,
}

impl<'a> Scanner<'a> {
    pub fn new(src: &'a str, handler: &'a mut Handler) -> Self {
        Self {
            src,
            tokens: vec![],
            start_pos: 0,
            pos: 0,
            line: 1,
            keywords: keywords(),
            handler,
        }
    }

    pub fn scan_tokens(mut self) -> Result<Vec<Token>> {
        while !self.eof() {
            self.scan_token();
            self.start_pos = self.pos;
        }

        if self.handler.has_errors() {
            Err("Scan failed")
        } else {
            Ok(self.tokens)
        }
    }

    fn scan_token(&mut self) {
        let c = self.peek();
        self.advance();
        match c {
            b'(' => self.add_token(OpenParen),
            b')' => self.add_token(CloseParen),
            b'{' => self.add_token(OpenBrace),
            b'}' => self.add_token(CloseBrace),
            b',' => self.add_token(Comma),
            b'.' => self.add_token(Dot),
            b'-' => self.add_token(Minus),
            b'+' => self.add_token(Plus),
            b';' => self.add_token(SemiColon),
            b'*' => self.add_token(Star),
            b'!' => {
                if self.eat(b'=') {
                    self.add_token(Ne)
                } else {
                    self.add_token(Not)
                }
            }
            b'=' => {
                if self.eat(b'=') {
                    self.add_token(EqEq)
                } else {
                    self.add_token(Eq)
                }
            }
            b'<' => {
                if self.eat(b'=') {
                    self.add_token(Le)
                } else {
                    self.add_token(Lt)
                }
            }
            b'>' => {
                if self.eat(b'=') {
                    self.add_token(Ge)
                } else {
                    self.add_token(Gt)
                }
            }

            b'/' => {
                if self.eat(b'/') {
                    self.comment();
                } else {
                    self.add_token(Slash)
                }
            }
            b' ' | b'\r' | b'\t' => {}
            b'\n' => self.line += 1,
            b'"' => self.string(),
            b':' => self.add_token(Colon),
            c if c.is_ascii_digit() => {
                self.number();
            }
            c if c.is_ascii_alphabetic() => {
                self.ident();
            }
            _ => self
                .handler
                .error(self.line, format!("unexpected char: {}", c as char)),
        }
    }

    fn add_token(&mut self, kind: TokenKind) {
        let span = self.mk_sp();
        self.tokens.push(Token::new(kind, span, self.line));
    }

    fn mk_sp(&self) -> Span {
        Span::new(self.start_pos, self.pos)
    }

    fn eat(&mut self, c: u8) -> bool {
        if self.peek() == c {
            self.advance();
            true
        } else {
            false
        }
    }

    fn string(&mut self) {
        while self.peek() != b'"' && !self.eof() {
            if self.peek() == b'\n' {
                self.line += 1;
            }
            self.advance();
        }

        if self.eof() {
            self.handler.error(self.line, "Unterminated String");
            return;
        }

        // Eat the closing ".
        self.advance();
        self.add_token(Str)
    }

    fn number(&mut self) {
        while self.peek().is_ascii_digit() {
            self.advance();
        }

        if self.peek() == b'.' && self.peek_next().is_ascii_digit() {
            self.advance();

            while self.peek().is_ascii_digit() {
                self.advance();
            }
        }

        self.add_token(Num)
    }

    fn ident(&mut self) {
        while self.peek().is_ascii_alphanumeric() {
            self.advance();
        }

        let sp = self.mk_sp();
        let lexeme = &self.src[sp.lo..sp.hi];
        let kind = self.keywords.get(lexeme).copied().unwrap_or_else(|| Ident);
        self.add_token(kind);
    }

    fn comment(&mut self) {
        while self.peek() != b'\n' && !self.eof() {
            self.advance();
        }
    }

    fn eof(&self) -> bool {
        self.pos >= self.src.len()
    }

    fn peek(&self) -> u8 {
        self.src
            .as_bytes()
            .get(self.pos)
            .copied()
            .unwrap_or_default()
    }

    fn peek_next(&self) -> u8 {
        self.src
            .as_bytes()
            .get(self.pos + 1)
            .copied()
            .unwrap_or_default()
    }

    fn advance(&mut self) {
        self.pos += 1;
    }
}

fn keywords() -> HashMap<&'static str, TokenKind> {
    let mut m = HashMap::new();
    m.insert("and", And);
    m.insert("struct", Struct);
    m.insert("else", Else);
    m.insert("false", False);
    m.insert("fn", Fn);
    m.insert("for", For);
    m.insert("in", In);
    m.insert("if", If);
    m.insert("or", Or);
    m.insert("return", Return);
    m.insert("self", This);
    m.insert("true", True);
    m.insert("let", Let);
    m.insert("while", While);
    m.insert("loop", Loop);
    m.insert("eof", Eof);
    m
}
