use crate::lex::Span;
use crate::symbol::Symbol;

#[derive(Debug, Clone, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub symbol: Symbol,
    pub span: Span,
}

impl Token {
    pub fn new(kind: TokenKind, symbol: Symbol, span: Span) -> Self {
        Self { kind, symbol, span }
    }

    pub fn dummy() -> Self {
        Self {
            kind: TokenKind::Eof,
            symbol: Symbol::intern(""),
            span: Span::DUMMY,
        }
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
    ColonColon,
    Slash,
    Star,
    Percent,
    Range,
    RangeClosed,
    Arrow,

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
    Literal { kind: LiteralKind },

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
    Break,
    Continue,
    Print,
    Eof,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum LiteralKind {
    Str,
    Int,
    Float,
}
