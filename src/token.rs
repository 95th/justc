use std::ops::Range;

#[derive(Debug)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
    pub line: usize,
}

impl Token {
    pub fn new(kind: TokenKind, span: Span, line: usize) -> Self {
        Self { kind, span, line }
    }
}

#[derive(Debug)]
pub struct Span {
    pub lo: usize,
    pub hi: usize,
}

impl Span {
    pub fn new(lo: usize, hi: usize) -> Self {
        Self { lo, hi }
    }

    pub fn range(&self) -> Range<usize> {
        self.lo..self.hi
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum TokenKind {
    // Single-character tokens.
    OpenParen,
    CloseParen,
    OpenBrace,
    CloseBrace,
    Comma,
    Dot,
    Minus,
    Plus,
    SemiColon,
    Colon,
    Slash,
    Star,

    // One or two character tokens.
    Not,
    Eq,
    EqEq,
    Gt,
    Lt,
    Ge,
    Le,
    Ne,

    // Literals.
    Ident,
    Str,
    Num,

    // Keywords
    And,
    Struct,
    Else,
    False,
    Fn,
    For,
    In,
    If,
    Or,
    Return,
    This,
    True,
    Let,
    While,
    Loop,
    Eof,
}
