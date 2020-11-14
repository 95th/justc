use crate::{
    lex::{Span, Spanned, Token},
    symbol::Symbol,
};
use std::fmt;

#[derive(Debug, PartialEq, Clone)]
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

#[derive(Debug, Clone, PartialEq)]
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

#[derive(Debug, Clone, PartialEq)]
pub enum Lit {
    Unit,
    Str(Symbol),
    Integer(i64),
    Float(Symbol),
    Bool(bool),
    Err,
}

#[derive(Debug, PartialEq)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

impl Expr {
    pub fn is_assignable(&self) -> bool {
        match &self.kind {
            ExprKind::Field(..) => true,
            ExprKind::Tuple(exprs) => match &exprs[..] {
                [e] => e.is_assignable(),
                _ => false,
            },
            ExprKind::Variable(v) => !v.is_self_param(),
            _ => false,
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum ExprKind {
    Binary {
        op: Spanned<BinOp>,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    Tuple(Vec<Box<Expr>>),
    Literal(Lit, Span),
    Unary {
        op: Spanned<UnOp>,
        expr: Box<Expr>,
    },
    Variable(Token),
    Block(Block),
    If {
        cond: Box<Expr>,
        then_clause: Block,
        else_clause: Option<Box<Expr>>,
    },
    Closure {
        params: Vec<Param>,
        ret: Ty,
        body: Box<Expr>,
    },
    Call {
        callee: Box<Expr>,
        args: Vec<Box<Expr>>,
    },
    Struct(Token, Vec<Field>, /* tuple: */ bool),
    Field(Box<Expr>, Token),
    MethodCall {
        callee: Box<Expr>,
        name: Token,
        args: Vec<Box<Expr>>,
    },
    AssocMethod {
        ty: Ty,
        name: Token,
    },
    Assign {
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    OpAssign {
        op: Spanned<BinOp>,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    Return(Span, Option<Box<Expr>>),
    Continue(Span),
    Break(Span),
}

#[derive(Debug, PartialEq)]
pub struct Field {
    pub name: Token,
    pub expr: Box<Expr>,
}

#[derive(Debug, PartialEq)]
pub enum Stmt {
    Expr(Box<Expr>, /* semicolon: */ bool),
    Let {
        name: Token,
        ty: Ty,
        init: Option<Box<Expr>>,
    },
    While {
        cond: Box<Expr>,
        body: Block,
    },
}

#[derive(Default, Debug, PartialEq)]
pub struct Block {
    pub stmts: Vec<Stmt>,
    pub span: Span,
    pub functions: Vec<Function>,
    pub structs: Vec<Struct>,
    pub enums: Vec<Enum>,
    pub impls: Vec<Impl>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Ty {
    pub kind: TyKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TyKind {
    Fn(Vec<Ty>, Box<Ty>),
    Ident(Token),
    Tuple(Vec<Ty>),
    Infer,
    Unit,
    SelfTy,
}

impl From<TyKind> for Ty {
    fn from(kind: TyKind) -> Self {
        Self {
            kind,
            span: Span::DUMMY,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Param {
    pub name: Token,
    pub ty: Ty,
}

#[derive(Debug, PartialEq)]
pub struct Function {
    pub name: Token,
    pub params: Vec<Param>,
    pub body: Block,
    pub ret: Ty,
}

#[derive(Debug, PartialEq)]
pub struct Struct {
    pub name: Token,
    pub fields: Vec<StructField>,
}

#[derive(Debug, PartialEq)]
pub struct Impl {
    pub name: Token,
    pub functions: Vec<Function>,
}

#[derive(Debug, PartialEq)]
pub struct StructField {
    pub name: Token,
    pub ty: Ty,
}

#[derive(Debug, PartialEq)]
pub struct Enum {
    pub name: Token,
    pub variants: Vec<EnumVariant>,
}

#[derive(Debug, PartialEq)]
pub struct EnumVariant {
    pub name: Token,
    pub kind: EnumVariantKind,
}

#[derive(Debug, PartialEq)]
pub enum EnumVariantKind {
    Empty,
    Struct(Vec<StructField>),
    Tuple(Vec<StructField>),
}

#[derive(Debug)]
pub struct Ast {
    pub stmts: Vec<Stmt>,
    pub functions: Vec<Function>,
    pub structs: Vec<Struct>,
    pub enums: Vec<Enum>,
    pub impls: Vec<Impl>,
}
