use crate::{err::Result, eval::Interpreter, lex::Token};
use std::{fmt, rc::Rc};

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
    Binary {
        op: BinOp,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    Call {
        callee: Box<Expr>,
        paren: Token,
        args: Vec<Expr>,
    },
    Grouping(Box<Expr>),
    Literal(Lit),
    Unary {
        op: UnOp,
        expr: Box<Expr>,
    },
    Variable(Token),
}

#[derive(Debug)]
pub enum Stmt {
    Expr(Box<Expr>),
    Function(Rc<Function>),
    Print(Box<Expr>),
    Let {
        name: Token,
        ty: Option<Ty>,
        init: Option<Box<Expr>>,
    },
    Loop(Vec<Stmt>),
    Assign {
        name: Token,
        val: Box<Expr>,
    },
    Block(Vec<Stmt>),
    If {
        cond: Box<Expr>,
        then_branch: Vec<Stmt>,
        else_branch: Vec<Stmt>,
    },
    Break,
    Continue,
}

#[derive(Debug)]
pub struct Param {
    pub name: Token,
    pub ty: Ty,
}

#[derive(Debug)]
pub struct Function {
    pub name: Token,
    pub params: Vec<Param>,
    pub ret_ty: Ty,
    pub body: Vec<Stmt>,
}

impl Callable for Function {
    fn call(&self, interpreter: &mut Interpreter, args: Vec<Lit>) -> Result<Lit> {
        interpreter.execute_block_with(&self.body, |env| {
            for i in 0..self.params.len() {
                env.declare(&self.params[i].name);
                env.define(&self.params[i].name, args[i].clone())?;
            }
            Ok(())
        })?;
        Ok(Lit::Bool(false))
    }

    fn arity(&self) -> usize {
        self.params.len()
    }
}

#[derive(Debug, Eq, PartialEq, Copy, Clone)]
pub enum Ty {
    Unit,
    Bool,
    Int(IntTy),
    Float(FloatTy),
    String,
}

#[derive(Debug, Eq, PartialEq, Copy, Clone)]
pub enum IntTy {
    I8,
    I16,
    I32,
    I64,
}

#[derive(Debug, Eq, PartialEq, Copy, Clone)]
pub enum FloatTy {
    F32,
    F64,
}
