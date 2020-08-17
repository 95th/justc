use crate::token::Token;
use std::{fmt, rc::Rc};

#[derive(Debug)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Lt,
    Gt,
    Le,
    Ge,
    Ne,
    Eq,
}

impl fmt::Display for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BinOp::Add => f.write_str("+"),
            BinOp::Sub => f.write_str("-"),
            BinOp::Mul => f.write_str("*"),
            BinOp::Div => f.write_str("/"),
            BinOp::Lt => f.write_str("<"),
            BinOp::Gt => f.write_str(">"),
            BinOp::Le => f.write_str("<="),
            BinOp::Ge => f.write_str(">="),
            BinOp::Ne => f.write_str("!="),
            BinOp::Eq => f.write_str("=="),
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
pub enum Lit {
    Str(Rc<String>),
    Number(f64),
    Bool(bool),
}

impl fmt::Display for Lit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Lit::Str(s) => write!(f, "\"{}\"", s),
            Lit::Number(n) => write!(f, "{}", n),
            Lit::Bool(b) => write!(f, "{}", b),
        }
    }
}

#[derive(Debug)]
pub enum Expr {
    Binary(BinOp, Box<Expr>, Box<Expr>),
    Grouping(Box<Expr>),
    Literal(Lit),
    Unary(UnOp, Box<Expr>),
    Variable(Token),
}

#[derive(Debug)]
pub enum Stmt {
    Expr(Box<Expr>),
    Print(Box<Expr>),
    Let(Token, Option<Box<Expr>>),
    Assign(Token, Box<Expr>),
    Block(Vec<Stmt>),
}
