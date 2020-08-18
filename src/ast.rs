use crate::{err::Result, eval::Interpreter, token::Token};
use std::{fmt, rc::Rc};

#[derive(Debug)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Lt,
    Gt,
    Le,
    Ge,
    Ne,
    Eq,
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
pub enum Lit {
    Str(Rc<String>),
    Number(f64),
    Bool(bool),
    Callable(Rc<dyn Callable>),
}

pub trait Callable: std::fmt::Debug {
    fn call(&self, interpreter: &mut Interpreter, args: Vec<Lit>) -> Result<Lit>;

    fn arity(&self) -> usize;
}

impl fmt::Display for Lit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Lit::Str(s) => write!(f, "\"{}\"", s),
            Lit::Number(n) => write!(f, "{}", n),
            Lit::Bool(b) => write!(f, "{}", b),
            Lit::Callable(c) => write!(f, "{:?}", c),
        }
    }
}

#[derive(Debug)]
pub enum Expr {
    Binary(BinOp, Box<Expr>, Box<Expr>),
    Call(Box<Expr>, Token, Vec<Expr>),
    Grouping(Box<Expr>),
    Literal(Lit),
    Unary(UnOp, Box<Expr>),
    Variable(Token),
}

#[derive(Debug)]
pub enum Stmt {
    Expr(Box<Expr>),
    Function(Rc<Function>),
    Print(Box<Expr>),
    Let(Token, Option<Token>, Option<Box<Expr>>),
    Loop(Vec<Stmt>),
    Assign(Token, Box<Expr>),
    Block(Vec<Stmt>),
    If(Box<Expr>, Vec<Stmt>, Vec<Stmt>),
    Break,
    Continue,
}

#[derive(Debug)]
pub struct Function {
    pub name: Token,
    pub params: Vec<Token>,
    pub types: Vec<Token>,
    pub ret_ty: Option<Token>,
    pub body: Vec<Stmt>,
}

impl Callable for Function {
    fn call(&self, interpreter: &mut Interpreter, args: Vec<Lit>) -> Result<Lit> {
        interpreter.execute_block_with(&self.body, |env| {
            for i in 0..self.params.len() {
                env.declare(&self.params[i]);
                env.define(&self.params[i], args[i].clone())?;
            }
            Ok(())
        })?;
        Ok(Lit::Bool(false))
    }

    fn arity(&self) -> usize {
        self.params.len()
    }
}
