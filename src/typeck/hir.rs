use crate::{
    lex::Span, lex::Spanned, lex::Token, parse::ast::BinOp, parse::ast::Lit, parse::ast::UnOp,
};

use super::ty::Ty;

#[derive(Debug)]
pub enum Stmt {
    Expr(Box<Expr>, bool),
    Let {
        name: Token,
        ty: Ty,
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
    pub ty: Ty,
}

#[derive(Debug)]
pub enum ExprKind {
    Binary {
        op: Spanned<BinOp>,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    Literal(Lit, Ty, Span),
    Unary {
        op: Spanned<UnOp>,
        expr: Box<Expr>,
    },
    Variable(Token, Ty),
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
    Struct(Token, Vec<Field>, Ty),
    Field(Box<Expr>, Token),
    MethodCall {
        callee: Box<Expr>,
        name: Token,
        args: Vec<Box<Expr>>,
    },
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
    pub ty: Ty,
    pub span: Span,
}

#[derive(Debug)]
pub struct Param {
    pub name: Token,
    pub param_ty: SpannedTy,
}

#[derive(Debug)]
pub struct Function {
    pub name: Token,
    pub params: Vec<Param>,
    pub ret: SpannedTy,
    pub body: Block,
    pub ty: Ty,
}

#[derive(Debug)]
pub struct SpannedTy {
    pub ty: Ty,
    pub span: Span,
    pub is_self: bool,
}

#[derive(Debug)]
pub struct Struct {
    pub name: Token,
    pub fields: Vec<StructField>,
    pub methods: Vec<Function>,
    pub ty: Ty,
    pub id: u32,
}

#[derive(Debug)]
pub struct StructField {
    pub name: Token,
    pub ty: Ty,
}

#[derive(Debug)]
pub struct Ast {
    pub structs: Vec<Struct>,
    pub functions: Vec<Function>,
    pub stmts: Vec<Stmt>,
}
