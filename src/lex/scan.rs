use super::token::LiteralKind;
use crate::{
    err::ErrHandler,
    lex::{Span, Token, TokenKind, TokenKind::*},
    symbol::Symbol,
};
use std::{collections::HashMap, rc::Rc};

pub struct Lexer {
    src: Rc<str>,
    start_pos: usize,
    pos: usize,
    keywords: HashMap<Symbol, TokenKind>,
    handler: Rc<ErrHandler>,
}

impl Lexer {
    pub fn new(src: Rc<str>, handler: &Rc<ErrHandler>) -> Self {
        Self {
            src,
            start_pos: 0,
            pos: 0,
            keywords: keywords(),
            handler: handler.clone(),
        }
    }

    pub fn look_ahead<F, R>(&mut self, dist: usize, f: F) -> R
    where
        F: FnOnce(Token) -> R,
    {
        assert!(dist > 0);
        let pos = self.pos;

        let mut t = Token {
            kind: Eof,
            span: Span::DUMMY,
            symbol: Symbol::intern(""),
        };

        for _ in 0..dist {
            t = self.next_token();
            if t.kind == Eof {
                break;
            }
        }

        let result = f(t);
        self.pos = pos;
        result
    }

    pub fn next_token(&mut self) -> Token {
        while !self.eof() {
            self.start_pos = self.pos;
            if let Some(t) = self.scan_token() {
                return t;
            }
        }

        Token {
            kind: Eof,
            span: Span::new(self.src.len(), self.src.len()),
            symbol: Symbol::intern(""),
        }
    }

    fn scan_token(&mut self) -> Option<Token> {
        let c = self.peek();
        self.advance();
        let t = match c {
            b'(' => self.add_token(OpenParen),
            b')' => self.add_token(CloseParen),
            b'{' => self.add_token(OpenBrace),
            b'}' => self.add_token(CloseBrace),
            b'[' => self.add_token(OpenSquare),
            b']' => self.add_token(CloseSquare),
            b',' => self.add_token(Comma),
            b'.' => {
                if self.eat(b'.') {
                    if self.eat(b'=') {
                        self.add_token(RangeClosed)
                    } else {
                        self.add_token(Range)
                    }
                } else {
                    self.add_token(Dot)
                }
            }
            b'-' => {
                if self.eat(b'>') {
                    self.add_token(Arrow)
                } else if self.eat(b'=') {
                    self.add_token(MinusEq)
                } else {
                    self.add_token(Minus)
                }
            }
            b'+' => {
                if self.eat(b'=') {
                    self.add_token(PlusEq)
                } else {
                    self.add_token(Plus)
                }
            }
            b';' => self.add_token(SemiColon),
            b'*' => {
                if self.eat(b'=') {
                    self.add_token(StarEq)
                } else {
                    self.add_token(Star)
                }
            }
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
                    return None;
                } else if self.eat(b'=') {
                    self.add_token(SlashEq)
                } else {
                    self.add_token(Slash)
                }
            }
            b' ' | b'\r' | b'\t' | b'\n' => {
                return None;
            }
            b'"' => return self.string(),
            b':' => {
                if self.eat(b':') {
                    self.add_token(ColonColon)
                } else {
                    self.add_token(Colon)
                }
            }
            b'&' => {
                if self.eat(b'&') {
                    self.add_token(AndAnd)
                } else {
                    self.add_token(And)
                }
            }
            b'|' => {
                if self.eat(b'|') {
                    self.add_token(OrOr)
                } else {
                    self.add_token(Or)
                }
            }
            c if c.is_ascii_digit() => self.number(),
            c if is_ident_start(c) => self.ident(),
            _ => {
                self.handler.report(self.mk_span(), "Unexpected char");
                return None;
            }
        };
        Some(t)
    }

    fn add_token(&mut self, kind: TokenKind) -> Token {
        let symbol = self.mk_symbol();
        self.add_token_with_symbol(kind, symbol)
    }

    fn add_token_with_symbol(&mut self, kind: TokenKind, symbol: Symbol) -> Token {
        Token::new(kind, symbol, self.mk_span())
    }

    fn mk_span(&self) -> Span {
        Span::new(self.start_pos, self.pos)
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

    fn string(&mut self) -> Option<Token> {
        while self.peek() != b'"' && !self.eof() {
            self.advance();
        }

        if self.eof() {
            self.handler.report(self.mk_span(), "Unterminated String");
            return None;
        }

        // Eat the closing ".
        self.advance();

        let symbol = Symbol::intern(&self.src[self.start_pos + 1..self.pos - 1]);
        Some(self.add_token_with_symbol(Literal { kind: LiteralKind::Str }, symbol))
    }

    fn number(&mut self) -> Token {
        while self.peek().is_ascii_digit() {
            self.advance();
        }

        let kind = if self.peek() == b'.' && self.peek_next().is_ascii_digit() {
            self.advance();

            while self.peek().is_ascii_digit() {
                self.advance();
            }

            LiteralKind::Float
        } else {
            LiteralKind::Int
        };

        self.add_token(Literal { kind })
    }

    fn ident(&mut self) -> Token {
        while is_ident_continue(self.peek()) {
            self.advance();
        }

        let symbol = self.mk_symbol();
        let kind = self.keywords.get(&symbol).copied().unwrap_or(Ident);
        self.add_token(kind)
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
        self.src.as_bytes().get(self.pos).copied().unwrap_or_default()
    }

    fn peek_next(&self) -> u8 {
        self.src.as_bytes().get(self.pos + 1).copied().unwrap_or_default()
    }

    fn advance(&mut self) {
        self.pos += 1;
    }
}

fn is_ident_start(c: u8) -> bool {
    matches!(c, b'a'..=b'z' | b'A'..=b'Z' | b'_')
}

fn is_ident_continue(c: u8) -> bool {
    matches!(c, b'a'..=b'z' | b'A'..=b'Z' | b'_' | b'0'..=b'9')
}

fn keywords() -> HashMap<Symbol, TokenKind> {
    let mut m = HashMap::new();
    m.insert(Symbol::intern("struct"), Struct);
    m.insert(Symbol::intern("enum"), Enum);
    m.insert(Symbol::intern("else"), Else);
    m.insert(Symbol::intern("false"), False);
    m.insert(Symbol::intern("fn"), Fn);
    m.insert(Symbol::intern("for"), For);
    m.insert(Symbol::intern("in"), In);
    m.insert(Symbol::intern("if"), If);
    m.insert(Symbol::intern("return"), Return);
    m.insert(Symbol::intern("self"), SelfParam);
    m.insert(Symbol::intern("Self"), SelfTy);
    m.insert(Symbol::intern("true"), True);
    m.insert(Symbol::intern("let"), Let);
    m.insert(Symbol::intern("while"), While);
    m.insert(Symbol::intern("loop"), Loop);
    m.insert(Symbol::intern("break"), Break);
    m.insert(Symbol::intern("continue"), Continue);
    m.insert(Symbol::intern("print"), Print);
    m.insert(Symbol::intern("impl"), Impl);
    m
}
