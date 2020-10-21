use crate::{
    lex::Span, lex::Spanned, lex::Token, parse::ast::BinOp, parse::ast::Lit, parse::ast::UnOp,
};

use super::ty::Ty;

#[derive(Debug)]
pub enum TypedStmt {
    Expr(Box<TypedExpr>),
    // Semicolon terminated Expr statement
    SemiExpr(Box<TypedExpr>),
    Let {
        name: Token,
        ty: Ty,
        init: Option<Box<TypedExpr>>,
    },
    Assign {
        name: Box<TypedExpr>,
        val: Box<TypedExpr>,
    },
    While {
        cond: Box<TypedExpr>,
        body: TypedBlock,
    },
}

#[derive(Debug)]
pub struct TypedExpr {
    pub kind: TypedExprKind,
    pub span: Span,
    pub ty: Ty,
}

#[derive(Debug)]
pub enum TypedExprKind {
    Binary {
        op: Spanned<BinOp>,
        left: Box<TypedExpr>,
        right: Box<TypedExpr>,
    },
    Grouping(Box<TypedExpr>),
    Literal(Lit, Ty, Span),
    Unary {
        op: Spanned<UnOp>,
        expr: Box<TypedExpr>,
    },
    Variable(Token, Ty),
    Block(TypedBlock),
    If {
        cond: Box<TypedExpr>,
        then_clause: TypedBlock,
        else_clause: Option<Box<TypedExpr>>,
    },
    Closure {
        params: Vec<TypedParam>,
        ret: Ty,
        body: Box<TypedExpr>,
    },
    Call {
        callee: Box<TypedExpr>,
        args: Vec<Box<TypedExpr>>,
    },
}

#[derive(Debug)]
pub struct TypedBlock {
    pub stmts: Vec<TypedStmt>,
    pub functions: Vec<TypedFunction>,
    pub ty: Ty,
    pub span: Span,
}

#[derive(Debug)]
pub struct TypedParam {
    pub name: Token,
    pub ty: Ty,
}

#[derive(Debug)]
pub struct TypedFunction {
    pub name: Token,
    pub params: Vec<TypedParam>,
    pub ret: Ty,
    pub body: TypedBlock,
    pub ty: Ty,
}
