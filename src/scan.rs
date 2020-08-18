use crate::{
    err::{Handler, Result},
    symbol::Symbol,
    token::{Token, TokenKind, TokenKind::*},
};
use std::collections::HashMap;

pub struct Scanner<'a> {
    src: &'a str,
    tokens: Vec<Token>,
    start_pos: usize,
    pos: usize,
    line: usize,
    keywords: HashMap<Symbol, TokenKind>,
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
            bail!("Scan failed")
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
            b'.' => {
                if self.eat(b'.') {
                    if self.eat(b'=') {
                        self.add_token(RangeClosed);
                    } else {
                        self.add_token(Range);
                    }
                } else {
                    self.add_token(Dot);
                }
            }
            b'-' => self.add_token(Minus),
            b'+' => self.add_token(Plus),
            b';' => self.add_token(SemiColon),
            b'*' => self.add_token(Star),
            b'%' => self.add_token(Percent),
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
            b'&' => {
                if self.eat(b'&') {
                    self.add_token(TokenKind::And);
                } else {
                    self.handler
                        .error(self.line, format!("unexpected char: {}", c as char));
                }
            }
            b'|' => {
                if self.eat(b'|') {
                    self.add_token(TokenKind::Or);
                } else {
                    self.handler
                        .error(self.line, format!("unexpected char: {}", c as char));
                }
            }
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
        let symbol = self.mk_symbol();
        self.add_token_with_symbol(kind, symbol);
    }

    fn add_token_with_symbol(&mut self, kind: TokenKind, symbol: Symbol) {
        self.tokens.push(Token::new(kind, symbol, self.line));
    }

    fn mk_symbol(&self) -> Symbol {
        let s = &self.src[self.start_pos..self.pos];
        Symbol::intern(s)
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
        let symbol = Symbol::intern(&self.src[self.start_pos + 1..self.pos - 1]);
        self.add_token_with_symbol(Str, symbol)
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

        let symbol = self.mk_symbol();
        let kind = self.keywords.get(&symbol).copied().unwrap_or_else(|| Ident);
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

fn keywords() -> HashMap<Symbol, TokenKind> {
    let mut m = HashMap::new();
    m.insert(Symbol::intern("struct"), Struct);
    m.insert(Symbol::intern("else"), Else);
    m.insert(Symbol::intern("false"), False);
    m.insert(Symbol::intern("fn"), Fn);
    m.insert(Symbol::intern("for"), For);
    m.insert(Symbol::intern("in"), In);
    m.insert(Symbol::intern("if"), If);
    m.insert(Symbol::intern("return"), Return);
    m.insert(Symbol::intern("self"), This);
    m.insert(Symbol::intern("true"), True);
    m.insert(Symbol::intern("let"), Let);
    m.insert(Symbol::intern("while"), While);
    m.insert(Symbol::intern("loop"), Loop);
    m.insert(Symbol::intern("break"), Break);
    m.insert(Symbol::intern("continue"), Continue);
    m.insert(Symbol::intern("print"), Print);
    m.insert(Symbol::intern("eof"), Eof);
    m
}
