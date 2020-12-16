use crate::{lex::Span, lex::Spanned, lex::Token, parse::ast::BinOp, parse::ast::Lit, parse::ast::UnOp};

use super::ty::TypeVar;

#[derive(Debug, Clone)]
pub enum Stmt {
    Expr(Expr, bool),
    Let {
        name: Token,
        ty: TypeVar,
        init: Option<Expr>,
    },
}

#[derive(Debug, Clone)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
    pub ty: TypeVar,
}

impl Expr {
    pub fn is_flow_control(&self) -> bool {
        matches!(
            self.kind,
            ExprKind::Return(..) | ExprKind::Break(..) | ExprKind::Continue
        )
    }
}

#[derive(Debug, Clone)]
pub enum ExprKind {
    Binary {
        op: Spanned<BinOp>,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    Tuple(Vec<Expr>),
    Literal(Lit, TypeVar, Span),
    Unary {
        op: Spanned<UnOp>,
        expr: Box<Expr>,
    },
    Variable(Token, TypeVar),
    Block(Block),
    If {
        cond: Box<Expr>,
        then_clause: Block,
        else_clause: Option<Box<Expr>>,
    },
    Closure {
        params: Vec<Param>,
        ret: TypeVar,
        body: Box<Expr>,
    },
    Call {
        callee: Box<Expr>,
        args: Vec<Expr>,
    },
    Struct(Token, Vec<Field>, TypeVar),
    Field(Box<Expr>, Token),
    AssocMethod {
        ty: TypeVar,
        name: Token,
    },
    MethodCall {
        callee: Box<Expr>,
        name: Token,
        args: Vec<Expr>,
    },
    Assign {
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    Return(Option<Box<Expr>>),
    Break(Option<Box<Expr>>),
    Continue,
    Loop(Block),
    Array(Vec<Expr>),
    ArrayAccess(Box<Expr>, Box<Expr>),
}

#[derive(Debug, Clone)]
pub struct Field {
    pub name: Token,
    pub expr: Expr,
}

#[derive(Debug, Clone)]
pub struct Block {
    pub structs: Vec<Struct>,
    pub enums: Vec<Enum>,
    pub impls: Vec<Impl>,
    pub functions: Vec<Function>,
    pub stmts: Vec<Stmt>,
    pub ty: TypeVar,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Param {
    pub name: Token,
    pub param_ty: TypeVar,
}

#[derive(Debug, Clone)]
pub struct Function {
    pub name: Token,
    pub params: Vec<Param>,
    pub ret: TypeVar,
    pub body: Block,
    pub ty: TypeVar,
}

#[derive(Debug, Clone)]
pub struct Struct {
    pub name: Token,
    pub fields: Vec<StructField>,
    pub ty: TypeVar,
}

#[derive(Debug, Clone)]
pub struct StructField {
    pub name: Token,
    pub ty: TypeVar,
}

#[derive(Debug, Clone)]
pub struct Enum {
    pub name: Token,
    pub variants: Vec<EnumVariant>,
    pub ty: TypeVar,
}

#[derive(Debug, Clone)]
pub struct EnumVariant {
    pub name: Token,
    pub kind: EnumVariantKind,
}

#[derive(Debug, Clone)]
pub enum EnumVariantKind {
    Empty,
    Struct(Vec<StructField>),
    Tuple(Vec<StructField>),
}

#[derive(Debug, Clone)]
pub struct Ast {
    pub structs: Vec<Struct>,
    pub enums: Vec<Enum>,
    pub functions: Vec<Function>,
    pub impls: Vec<Impl>,
    pub stmts: Vec<Stmt>,
}

#[derive(Debug, Clone)]
pub struct Impl {
    pub ty: TypeVar,
    pub functions: Vec<Function>,
}
