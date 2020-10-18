use crate::{
    err::Handler,
    parse::ast::{self, Block, Expr, ExprKind, Lit, Stmt},
    symbol::SymbolTable,
};

use super::{
    ty::Ty, ty::TyContext, typed_ast::TypedBlock, typed_ast::TypedExpr, typed_ast::TypedExprKind,
    typed_ast::TypedStmt,
};

pub fn annotate(ast: Vec<Stmt>, handler: &Handler) -> Option<Vec<TypedStmt>> {
    let env = &mut TyContext::new();
    let bindings = &mut SymbolTable::new();
    Annotate::new(env, bindings, &handler).annotate_stmts(ast)
}

struct Annotate<'a> {
    env: &'a mut TyContext,
    bindings: &'a mut SymbolTable<Ty>,
    handler: &'a Handler,
}

impl<'a> Annotate<'a> {
    fn new(
        env: &'a mut TyContext,
        bindings: &'a mut SymbolTable<Ty>,
        handler: &'a Handler,
    ) -> Self {
        Self {
            env,
            bindings,
            handler,
        }
    }

    fn annotate_stmts(&mut self, stmts: Vec<Stmt>) -> Option<Vec<TypedStmt>> {
        stmts.into_iter().map(|s| self.annotate_stmt(s)).collect()
    }

    fn annotate_stmt(&mut self, stmt: Stmt) -> Option<TypedStmt> {
        match stmt {
            Stmt::Expr(e) => Some(TypedStmt::Expr(self.annotate_expr(e)?)),
            Stmt::SemiExpr(e) => Some(TypedStmt::SemiExpr(self.annotate_expr(e)?)),
            Stmt::Let { name, init, ty } => {
                let init = match init {
                    Some(e) => Some(self.annotate_expr(e)?),
                    None => None,
                };

                let let_ty = if let Some(ty) = ty {
                    match ty.kind {
                        ast::TyKind::Ident(t) => t.symbol.as_str_with(|s| {
                            let ty = match s {
                                "bool" => Ty::Bool,
                                "int" => Ty::Int,
                                "str" => Ty::Str,
                                "float" => Ty::Float,
                                _ => {
                                    self.handler.report(t.span, "Unknown type");
                                    return None;
                                }
                            };
                            Some(ty)
                        })?,
                        ast::TyKind::Infer => self.env.new_var(),
                    }
                } else {
                    self.env.new_var()
                };

                self.bindings.insert(name.symbol, let_ty.clone());

                Some(TypedStmt::Let {
                    name,
                    ty: let_ty,
                    init,
                })
            }
            Stmt::Assign { name, val } => Some(TypedStmt::Assign {
                name: self.annotate_expr(name)?,
                val: self.annotate_expr(val)?,
            }),
        }
    }

    fn annotate_expr(&mut self, expr: Box<Expr>) -> Option<Box<TypedExpr>> {
        let (kind, span) = (expr.kind, expr.span);
        let kind = match kind {
            ExprKind::Binary { op, left, right } => TypedExprKind::Binary {
                op,
                left: self.annotate_expr(left)?,
                right: self.annotate_expr(right)?,
            },
            ExprKind::Grouping(e) => TypedExprKind::Grouping(self.annotate_expr(e)?),
            ExprKind::Literal(lit, span) => {
                let ty = match &lit {
                    Lit::Str(_) => Ty::Str,
                    Lit::Integer(_) => Ty::Int,
                    Lit::Float(_) => Ty::Float,
                    Lit::Bool(_) => Ty::Bool,
                    Lit::Err => self.env.new_var(),
                };
                TypedExprKind::Literal(lit, ty, span)
            }
            ExprKind::Unary { op, expr } => TypedExprKind::Unary {
                op,
                expr: self.annotate_expr(expr)?,
            },
            ExprKind::Variable(t) => match self.bindings.get(&t.symbol) {
                Some(ty) => TypedExprKind::Variable(t, ty.clone()),
                None => {
                    self.handler.report(t.span, "Undefined variable");
                    return None;
                }
            },
            ExprKind::Block(block) => TypedExprKind::Block(self.annotate_block(block)?),
            ExprKind::If {
                cond,
                then_clause,
                else_clause,
            } => TypedExprKind::If {
                cond: self.annotate_expr(cond)?,
                then_clause: self.annotate_block(then_clause)?,
                else_clause: match else_clause {
                    Some(e) => Some(self.annotate_block(e)?),
                    None => None,
                },
            },
        };
        Some(Box::new(TypedExpr {
            kind,
            span,
            ty: self.env.new_var(),
        }))
    }

    fn annotate_block(&mut self, block: Block) -> Option<TypedBlock> {
        let env = &mut *self.env;
        let handler = self.handler;
        self.bindings.enter(|bindings| {
            let mut annotate = Annotate::new(env, bindings, handler);
            Some(TypedBlock {
                stmts: annotate.annotate_stmts(block.stmts)?,
                ty: env.new_var(),
                span: block.span,
            })
        })
    }
}
