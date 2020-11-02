use std::rc::Rc;

use self::{
    hir::{Ast, Block, Expr, ExprKind, Function, Stmt, Struct},
    ty::{Ty, TyContext},
};
use crate::{
    err::{Handler, Result},
    lex::Span,
    parse::ast,
};

mod annotate;
mod fill;
mod hir;
mod ty;
mod unification;

pub struct Typeck {
    handler: Rc<Handler>,
}

impl Typeck {
    pub fn new(handler: &Rc<Handler>) -> Self {
        Self {
            handler: handler.clone(),
        }
    }

    pub fn typeck(&self, ast: ast::Ast) -> Result<Ast> {
        let mut env = TyContext::new(&self.handler);
        let mut ast = self::annotate::annotate(ast, &mut env, &self.handler)?;

        self::unification::unify(&ast, &mut env, &self.handler)?;
        env.fill(&mut ast)?;

        dbg!(&ast);

        self.typeck_structs(&ast.structs)?;
        self.typeck_fns(&ast.functions)?;
        self.typeck_stmts(&ast.stmts)?;

        Ok(ast)
    }

    fn typeck_stmts(&self, stmts: &[Stmt]) -> Result<()> {
        for stmt in stmts {
            self.typeck_stmt(stmt)?;
        }
        Ok(())
    }

    fn typeck_stmt(&self, stmt: &Stmt) -> Result<()> {
        match stmt {
            Stmt::Expr(expr, _) => self.typeck_expr(expr),
            Stmt::Let { name, ty, init } => {
                self.typeck_no_var(ty, name.span)?;
                if let Some(init) = init {
                    self.typeck_expr(init)?;
                    self.typeck_eq(ty, &init.ty, init.span)?;
                }
                Ok(())
            }
            Stmt::Assign { lhs, rhs } => {
                self.typeck_expr(lhs)?;
                self.typeck_expr(rhs)?;
                self.typeck_eq(&lhs.ty, &rhs.ty, rhs.span)
            }
            Stmt::While { cond, body } => {
                self.typeck_expr(cond)?;
                self.typeck_eq(&Ty::Bool, &cond.ty, cond.span)?;
                self.typeck_block(body)
            }
            Stmt::Return(_, e) => {
                if let Some(e) = e {
                    self.typeck_expr(e)
                } else {
                    Ok(())
                }
            }
            Stmt::Continue(_) | Stmt::Break(_) => Ok(()),
        }
    }

    fn typeck_expr(&self, expr: &Expr) -> Result<()> {
        match &expr.kind {
            ExprKind::Binary { op, left, right } => {
                self.typeck_eq(&left.ty, &right.ty, right.span)?;

                use ast::BinOp::*;
                match op.val {
                    Add | Sub | Mul | Div | Rem | Lt | Gt | Le | Ge => match &left.ty {
                        Ty::Int | Ty::Float => Ok(()),
                        ty => self
                            .handler
                            .mk_err(op.span, &format!("Not supported for {}", ty)),
                    },

                    Ne | Eq => match &left.ty {
                        Ty::Int | Ty::Float | Ty::Bool => Ok(()),
                        ty => self
                            .handler
                            .mk_err(op.span, &format!("Not supported for {}", ty)),
                    },
                    And | Or => match &left.ty {
                        Ty::Bool => Ok(()),
                        ty => self
                            .handler
                            .mk_err(op.span, &format!("Not supported for {}", ty)),
                    },
                }
            }
            ExprKind::Literal(..) => Ok(()),
            ExprKind::Unary { op, expr } => match op.val {
                ast::UnOp::Not => match &expr.ty {
                    Ty::Bool => Ok(()),
                    ty => self
                        .handler
                        .mk_err(op.span, &format!("Not supported for {}", ty)),
                },
                ast::UnOp::Neg => match &expr.ty {
                    Ty::Int | Ty::Float => Ok(()),
                    ty => self
                        .handler
                        .mk_err(op.span, &format!("Not supported for {}", ty)),
                },
            },
            ExprKind::Variable(_, _) => Ok(()),
            ExprKind::Block(block) => self.typeck_block(block),
            ExprKind::If {
                cond,
                then_clause,
                else_clause,
            } => {
                self.typeck_expr(cond)?;
                self.typeck_block(then_clause)?;
                if let Some(else_clause) = else_clause {
                    self.typeck_expr(else_clause)?;
                }
                Ok(())
            }
            ExprKind::Closure { params, ret, body } => {
                for p in params {
                    self.typeck_no_var(&p.param_ty.ty, p.name.span)?;
                }
                self.typeck_expr(body)?;
                self.typeck_eq(ret, &body.ty, body.span)
            }
            ExprKind::Call { callee, args } => {
                self.typeck_expr(callee)?;
                for arg in args {
                    self.typeck_expr(arg)?;
                }
                Ok(())
            }
            ExprKind::Struct(_, fields, _) => {
                for f in fields {
                    self.typeck_expr(&f.expr)?;
                }

                Ok(())
            }
            ExprKind::Field(expr, _) => {
                self.typeck_expr(expr)?;
                Ok(())
            }
            ExprKind::MethodCall { ty, args, .. } => {
                self.typeck_no_var(&ty.ty, ty.span)?;
                for arg in args {
                    self.typeck_expr(arg)?;
                }
                Ok(())
            }
        }
    }

    fn typeck_block(&self, block: &Block) -> Result<()> {
        self.typeck_structs(&block.structs)?;
        self.typeck_fns(&block.functions)?;
        self.typeck_stmts(&block.stmts)?;

        if let Some(Stmt::Expr(expr, false)) = block.stmts.last() {
            self.typeck_eq(&expr.ty, &block.ty, expr.span)?;
        }

        Ok(())
    }

    fn typeck_structs(&self, structs: &[Struct]) -> Result<()> {
        for s in structs {
            self.typeck_struct(s)?;
        }
        Ok(())
    }

    fn typeck_struct(&self, s: &Struct) -> Result<()> {
        for f in &s.fields {
            self.typeck_no_var(&f.ty, f.name.span)?;
        }
        self.typeck_no_var(&s.ty, s.name.span)?;
        Ok(())
    }

    fn typeck_fns(&self, func: &[Function]) -> Result<()> {
        for f in func {
            self.typeck_fn(f)?;
        }
        Ok(())
    }

    fn typeck_fn(&self, func: &Function) -> Result<()> {
        self.typeck_eq(&func.ret.ty, &func.body.ty, func.body.span)?;
        self.typeck_block(&func.body)
    }

    fn typeck_eq(&self, a: &Ty, b: &Ty, span: Span) -> Result<()> {
        self.typeck_no_var(a, span)?;
        self.typeck_no_var(b, span)?;

        if a == b {
            Ok(())
        } else {
            self.handler.mk_err(
                span,
                &format!("Type mismatch: Expected: {}, Actual: {}", a, b),
            )
        }
    }

    fn typeck_no_var(&self, ty: &Ty, span: Span) -> Result<()> {
        match ty {
            Ty::Infer(_) => self
                .handler
                .mk_err(span, "Type cannot be inferred. Please add type annotations"),
            Ty::Unit | Ty::Bool | Ty::Int | Ty::Float | Ty::Str => Ok(()),
            Ty::Fn(params, ret) => {
                for p in params {
                    self.typeck_no_var(p, span)?;
                }
                self.typeck_no_var(ret, span)
            }
            Ty::Struct(.., fields) => {
                for (_, f) in fields {
                    self.typeck_no_var(f, span)?;
                }
                Ok(())
            }
        }
    }
}
