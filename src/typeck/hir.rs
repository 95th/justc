use crate::{
    lex::Span, lex::Spanned, lex::Token, parse::ast::BinOp, parse::ast::Lit, parse::ast::UnOp,
};

use super::ty::Tvar;

#[derive(Debug)]
pub enum Stmt {
    Expr(Box<Expr>, bool),
    Let {
        name: Token,
        ty: Tvar,
        init: Option<Box<Expr>>,
    },
    Assign {
        name: Box<Expr>,
        val: Box<Expr>,
    },
    While {
        cond: Box<Expr>,
        body: Block,
    },
    Return(Span, Option<Box<Expr>>),
    Continue(Span),
    Break(Span),
}

#[derive(Debug)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
    pub ty: Tvar,
}

#[derive(Debug)]
pub enum ExprKind {
    Binary {
        op: Spanned<BinOp>,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    Literal(Lit, Tvar, Span),
    Unary {
        op: Spanned<UnOp>,
        expr: Box<Expr>,
    },
    Variable(Token, Tvar),
    Block(Block),
    If {
        cond: Box<Expr>,
        then_clause: Block,
        else_clause: Option<Box<Expr>>,
    },
    Closure {
        params: Vec<Param>,
        ret: Tvar,
        body: Box<Expr>,
    },
    Call {
        callee: Box<Expr>,
        args: Vec<Box<Expr>>,
    },
    Struct(Token, Vec<Field>, Tvar),
    Field(Box<Expr>, Token),
}

#[derive(Debug)]
pub struct Field {
    pub name: Token,
    pub expr: Box<Expr>,
}

#[derive(Debug)]
pub struct Block {
    pub structs: Vec<Struct>,
    pub functions: Vec<Function>,
    pub stmts: Vec<Stmt>,
    pub ty: Tvar,
    pub span: Span,
}

#[derive(Debug)]
pub struct Param {
    pub name: Token,
    pub ty: Tvar,
}

#[derive(Debug)]
pub struct Function {
    pub name: Token,
    pub params: Vec<Param>,
    pub ret: Tvar,
    pub body: Block,
    pub ty: Tvar,
}

#[derive(Debug)]
pub struct Struct {
    pub name: Token,
    pub fields: Vec<StructField>,
    pub ty: Tvar,
}

#[derive(Debug)]
pub struct StructField {
    pub name: Token,
    pub ty: Tvar,
}

#[derive(Debug)]
pub struct Ast {
    pub structs: Vec<Struct>,
    pub functions: Vec<Function>,
    pub stmts: Vec<Stmt>,
}
