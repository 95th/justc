use crate::symbol::Symbol;

#[derive(Debug, Clone)]
pub struct Token {
    pub kind: TokenKind,
    pub symbol: Symbol,
    pub line: usize,
}

impl Token {
    pub fn new(kind: TokenKind, symbol: Symbol, line: usize) -> Self {
        Self { kind, symbol, line }
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
    Print,
    Eof,
}
