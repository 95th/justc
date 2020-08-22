use crate::{
    lex::{Span, Token},
    symbol::Symbol,
};
use std::fmt;

#[derive(Debug)]
pub enum BinOp {
    // Math
    Add,
    Sub,
    Mul,
    Div,
    Rem,

    // Comparisons
    Lt,
    Gt,
    Le,
    Ge,
    Ne,
    Eq,

    // Logical
    And,
    Or,
}

impl fmt::Display for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BinOp::Add => f.write_str("+"),
            BinOp::Sub => f.write_str("-"),
            BinOp::Mul => f.write_str("*"),
            BinOp::Div => f.write_str("/"),
            BinOp::Rem => f.write_str("%"),
            BinOp::Lt => f.write_str("<"),
            BinOp::Gt => f.write_str(">"),
            BinOp::Le => f.write_str("<="),
            BinOp::Ge => f.write_str(">="),
            BinOp::Ne => f.write_str("!="),
            BinOp::Eq => f.write_str("=="),
            BinOp::And => f.write_str("&&"),
            BinOp::Or => f.write_str("||"),
        }
    }
}

#[derive(Debug)]
pub enum UnOp {
    Not,
    Neg,
}

impl fmt::Display for UnOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            UnOp::Not => f.write_str("!"),
            UnOp::Neg => f.write_str("-"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Lit {
    pub kind: LitKind,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum LitKind {
    Str(Symbol),
    Integer(i64),
    Float(Symbol),
    Bool(bool),
    Err,
}

#[derive(Debug)]
pub enum Expr {
    Binary {
        op: BinOp,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    Grouping(Box<Expr>),
    Literal(Lit),
    Unary {
        op: UnOp,
        expr: Box<Expr>,
    },
    Variable(Token),
    Block(Block),
}

#[derive(Debug)]
pub enum Stmt {
    Expr(Box<Expr>),
    Let {
        name: Token,
        ty: Option<Ty>,
        init: Option<Box<Expr>>,
    },
    Assign {
        name: Token,
        val: Box<Expr>,
    },
}

#[derive(Default, Debug)]
pub struct Block {
    pub stmts: Vec<Stmt>,
}

impl From<Stmt> for Block {
    fn from(stmt: Stmt) -> Self {
        Self { stmts: vec![stmt] }
    }
}

#[derive(Debug, Clone)]
pub struct Ty {
    pub kind: TyKind,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum TyKind {
    Ident(Token),
    Infer,
    Err,
}
