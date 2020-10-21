use crate::{
    err::Handler,
    lex::Span,
    parse::ast::BinOp,
    parse::ast::{Stmt, UnOp},
};

use self::{
    ty::Ty,
    typed_ast::{TypedBlock, TypedExpr, TypedExprKind, TypedFunction, TypedStmt},
};

mod annotate;
mod constraints;
pub mod ty;
pub mod typed_ast;
mod unify;

pub struct Typeck<'a> {
    handler: &'a Handler,
}

impl<'a> Typeck<'a> {
    pub fn new(handler: &'a Handler) -> Self {
        Self { handler }
    }

    pub fn typeck(&self, ast: Vec<Stmt>) -> Option<Vec<TypedStmt>> {
        let mut stmts = self::annotate::annotate(ast, self.handler)?;
        let constraints = self::constraints::collect(&mut stmts);
        let mut constraints = constraints.into_iter().collect::<Vec<_>>();

        let subst = self::unify::unify(&mut constraints, self.handler)?;
        subst.fill_ast(&mut stmts);

        for stmt in &stmts {
            self.typeck_stmt(stmt)?;
        }

        dbg!(&stmts);
        Some(stmts)
    }

    fn typeck_stmt(&self, stmt: &TypedStmt) -> Option<()> {
        match stmt {
            TypedStmt::Expr(e) | TypedStmt::SemiExpr(e) => self.typeck_expr(e),
            TypedStmt::Let { ty, init, .. } => {
                if let Some(init) = init {
                    self.typeck_expr(init)?;
                    self.typeck_eq(ty, &init.ty, &init.span)?;
                }
                Some(())
            }
            TypedStmt::Assign { name, val } => {
                self.typeck_expr(val)?;
                self.typeck_eq(&name.ty, &val.ty, &val.span)
            }
            TypedStmt::While { cond, body } => {
                self.typeck_expr(cond)?;
                self.typeck_block(body)
            }
        }
    }

    fn typeck_expr(&self, expr: &TypedExpr) -> Option<()> {
        match &expr.kind {
            TypedExprKind::Binary {
                op,
                span,
                left,
                right,
            } => {
                self.typeck_eq(&left.ty, &right.ty, &right.span)?;
                match op {
                    BinOp::Add
                    | BinOp::Sub
                    | BinOp::Mul
                    | BinOp::Div
                    | BinOp::Rem
                    | BinOp::Lt
                    | BinOp::Gt
                    | BinOp::Le
                    | BinOp::Ge => {
                        if [Ty::Int, Ty::Float].contains(&left.ty) {
                            Some(())
                        } else {
                            self.handler.report(*span, "Operation not supported.");
                            None
                        }
                    }

                    BinOp::Ne | BinOp::Eq => {
                        if [Ty::Int, Ty::Float, Ty::Bool].contains(&left.ty) {
                            Some(())
                        } else {
                            self.handler.report(*span, "Operation not supported.");
                            None
                        }
                    }
                    BinOp::And | BinOp::Or => {
                        if left.ty == Ty::Bool {
                            Some(())
                        } else {
                            self.handler.report(*span, "Operation not supported.");
                            None
                        }
                    }
                }
            }
            TypedExprKind::Grouping(e) => self.typeck_expr(e),
            TypedExprKind::Literal(_, _, _) => Some(()),
            TypedExprKind::Unary { op, span, expr } => match op {
                UnOp::Not => {
                    if expr.ty == Ty::Bool {
                        Some(())
                    } else {
                        self.handler.report(*span, "Operation not supported.");
                        None
                    }
                }
                UnOp::Neg => {
                    if [Ty::Int, Ty::Float, Ty::Bool].contains(&expr.ty) {
                        Some(())
                    } else {
                        self.handler.report(expr.span, "Operation not supported.");
                        None
                    }
                }
            },
            TypedExprKind::Variable(_, _) => Some(()),
            TypedExprKind::Block(block) => self.typeck_block(block),
            TypedExprKind::If {
                cond,
                then_clause,
                else_clause,
            } => {
                self.typeck_expr(cond)?;
                self.typeck_block(then_clause)?;
                if let Some(else_clause) = else_clause {
                    self.typeck_expr(else_clause)?;
                }
                Some(())
            }
            TypedExprKind::Closure { ret, body, .. } => {
                self.typeck_expr(body)?;
                self.typeck_eq(ret, &body.ty, &body.span)
            }
            TypedExprKind::Call { callee, args } => {
                self.typeck_expr(callee)?;
                for arg in args {
                    self.typeck_expr(arg)?;
                }
                Some(())
            }
        }
    }

    fn typeck_block(&self, block: &TypedBlock) -> Option<()> {
        for f in &block.functions {
            self.typeck_fn(f)?;
        }
        for s in &block.stmts {
            self.typeck_stmt(s)?;
        }

        if let Some(TypedStmt::Expr(last)) = block.stmts.last() {
            self.typeck_eq(&last.ty, &block.ty, &last.span)?;
        }

        Some(())
    }

    fn typeck_fn(&self, func: &TypedFunction) -> Option<()> {
        self.typeck_eq(&func.ret, &func.body.ty, &func.body.span)?;
        self.typeck_block(&func.body)
    }

    fn typeck_eq(&self, a: &Ty, b: &Ty, span: &Span) -> Option<()> {
        if matches!(a, Ty::Var(_)) || matches!(b, Ty::Var(_)) {
            self.handler.report(
                *span,
                "Type cannot be inferred. Please add type annotations",
            );
            return None;
        }
        if a == b {
            Some(())
        } else {
            self.handler.report(
                *span,
                &format!("Type mismatch: Expected: {:?}, Actual: {:?}", a, b),
            );
            None
        }
    }
}
