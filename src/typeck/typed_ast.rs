use crate::{lex::Span, lex::Token, parse::ast::BinOp, parse::ast::Lit, parse::ast::UnOp};

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
        op: BinOp,
        left: Box<TypedExpr>,
        right: Box<TypedExpr>,
    },
    Grouping(Box<TypedExpr>),
    Literal(Lit, Ty, Span),
    Unary {
        op: UnOp,
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
    pub ty: Ty,
    pub span: Span,
}

#[derive(Debug)]
pub struct TypedParam {
    pub name: Token,
    pub ty: Ty,
}
