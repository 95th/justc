use self::{
    hir::{Ast, Block, Expr, ExprKind, Function, Stmt},
    ty::Ty,
};
use crate::{err::Handler, lex::Span, parse::ast};

mod annotate;
mod constraints;
mod hir;
mod ty;
mod unify;

pub struct Typeck<'a> {
    handler: &'a Handler,
}

impl<'a> Typeck<'a> {
    pub fn new(handler: &'a Handler) -> Self {
        Self { handler }
    }

    pub fn typeck(&self, ast: ast::Ast) -> Option<Ast> {
        let mut ast = self::annotate::annotate(ast, self.handler)?;
        let mut constraints = self::constraints::collect(&mut ast);

        let subst = self::unify::unify(&mut constraints, self.handler)?;
        subst.fill_ast(&mut ast);

        self.typeck_fns(&ast.functions)?;
        self.typeck_stmts(&ast.stmts)?;

        dbg!(&ast);
        Some(ast)
    }

    fn typeck_stmts(&self, stmts: &[Stmt]) -> Option<()> {
        for stmt in stmts {
            self.typeck_stmt(stmt)?;
        }
        Some(())
    }

    fn typeck_stmt(&self, stmt: &Stmt) -> Option<()> {
        use Stmt::*;
        match stmt {
            Expr { expr, .. } => self.typeck_expr(expr),
            Let { ty, init, .. } => {
                if let Some(init) = init {
                    self.typeck_expr(init)?;
                    self.typeck_eq(ty, &init.ty, &init.span)?;
                }
                Some(())
            }
            Assign { name, val } => {
                self.typeck_expr(val)?;
                self.typeck_eq(&name.ty, &val.ty, &val.span)
            }
            While { cond, body } => {
                self.typeck_expr(cond)?;
                self.typeck_block(body)
            }
            Return(_, e) => {
                if let Some(e) = e {
                    self.typeck_expr(e)
                } else {
                    Some(())
                }
            }
            Continue(_) => Some(()),
        }
    }

    fn typeck_expr(&self, expr: &Expr) -> Option<()> {
        use ExprKind::*;
        match &expr.kind {
            Binary { op, left, right } => {
                self.typeck_eq(&left.ty, &right.ty, &right.span)?;

                use ast::BinOp::*;
                match op.val {
                    Add | Sub | Mul | Div | Rem | Lt | Gt | Le | Ge => match &left.ty {
                        Ty::Int | Ty::Float => Some(()),
                        ty => {
                            self.handler
                                .report(op.span, &format!("Not supported for {:?}", ty));
                            None
                        }
                    },

                    Ne | Eq => match &left.ty {
                        Ty::Int | Ty::Float | Ty::Bool => Some(()),
                        ty => {
                            self.handler
                                .report(op.span, &format!("Not supported for {:?}", ty));
                            None
                        }
                    },
                    And | Or => match &left.ty {
                        Ty::Bool => Some(()),
                        ty => {
                            self.handler
                                .report(op.span, &format!("Not supported for {:?}", ty));
                            None
                        }
                    },
                }
            }
            Literal(..) => Some(()),
            Unary { op, expr } => match op.val {
                ast::UnOp::Not => match &expr.ty {
                    Ty::Bool => Some(()),
                    ty => {
                        self.handler
                            .report(op.span, &format!("Not supported for {:?}", ty));
                        None
                    }
                },
                ast::UnOp::Neg => match &expr.ty {
                    Ty::Int | Ty::Float => Some(()),
                    ty => {
                        self.handler
                            .report(op.span, &format!("Not supported for {:?}", ty));
                        None
                    }
                },
            },
            Variable(_, _) => Some(()),
            Block(block) => self.typeck_block(block),
            If {
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
            Closure { ret, body, .. } => {
                self.typeck_expr(body)?;
                self.typeck_eq(ret, &body.ty, &body.span)
            }
            Call { callee, args } => {
                self.typeck_expr(callee)?;
                for arg in args {
                    self.typeck_expr(arg)?;
                }
                Some(())
            }
        }
    }

    fn typeck_block(&self, block: &Block) -> Option<()> {
        self.typeck_fns(&block.functions)?;
        self.typeck_stmts(&block.stmts)?;

        if let Some(Stmt::Expr {
            expr,
            semicolon: false,
        }) = block.stmts.last()
        {
            self.typeck_eq(&expr.ty, &block.ty, &expr.span)?;
        }

        Some(())
    }

    fn typeck_fns(&self, func: &[Function]) -> Option<()> {
        for f in func {
            self.typeck_fn(f)?;
        }
        Some(())
    }

    fn typeck_fn(&self, func: &Function) -> Option<()> {
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
