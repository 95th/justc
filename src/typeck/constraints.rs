use crate::{
    err::Handler,
    parse::ast::{BinOp, UnOp},
};

use super::{
    hir::{Ast, Block, Expr, ExprKind, Function, Stmt},
    ty::{Tvar, TyContext, TyKind},
};

struct Collector<'a> {
    enclosing_fn_ret_ty: Option<Tvar>,
    env: &'a mut TyContext,
    handler: &'a Handler,
}

pub fn collect(ast: &Ast, env: &mut TyContext, handler: &Handler) -> Option<()> {
    let mut collector = Collector::new(env, handler);
    collector.collect_fns(&ast.functions)?;
    collector.collect_stmts(&ast.stmts)
}

impl<'a> Collector<'a> {
    fn new(env: &'a mut TyContext, handler: &'a Handler) -> Self {
        Self {
            enclosing_fn_ret_ty: None,
            env,
            handler,
        }
    }

    fn collect_stmts(&mut self, ast: &[Stmt]) -> Option<()> {
        for stmt in ast {
            self.collect_stmt(stmt)?;
        }
        Some(())
    }

    fn collect_stmt(&mut self, stmt: &Stmt) -> Option<()> {
        match stmt {
            Stmt::Expr(expr, ..) => self.collect_expr(expr),
            Stmt::Let { ty, init, .. } => {
                if let Some(init) = init {
                    self.collect_expr(init)?;
                    self.env.unify(*ty, init.ty, init.span)?;
                }
                Some(())
            }
            Stmt::Assign { name, val } => {
                self.collect_expr(name)?;
                self.collect_expr(val)?;
                self.env.unify(name.ty, val.ty, val.span)
            }
            Stmt::While { cond, body } => {
                self.collect_expr(cond)?;
                self.collect_block(body)?;
                self.env.unify_ty(cond.ty, TyKind::Bool, cond.span)
            }
            Stmt::Return(_, e) => {
                if let Some(e) = e {
                    self.collect_expr(e)?;
                }
                Some(())
            }
            Stmt::Continue(_) | Stmt::Break(_) => Some(()),
        }
    }

    fn collect_expr(&mut self, expr: &Expr) -> Option<()> {
        match &expr.kind {
            ExprKind::Binary {
                op, left, right, ..
            } => {
                self.collect_expr(left)?;
                self.collect_expr(right)?;
                self.env.unify(left.ty, right.ty, right.span)?;
                match op.val {
                    BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem => {
                        self.env.unify(expr.ty, left.ty, left.span)
                    }
                    BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge | BinOp::Ne | BinOp::Eq => {
                        self.env.unify_ty(expr.ty, TyKind::Bool, expr.span)
                    }
                    BinOp::And | BinOp::Or => {
                        self.env.unify_ty(left.ty, TyKind::Bool, left.span)?;
                        self.env.unify_ty(right.ty, TyKind::Bool, right.span)
                    }
                }
            }
            ExprKind::Literal(_, ty, _) => self.env.unify(expr.ty, *ty, expr.span),
            ExprKind::Unary { op, expr: e, .. } => {
                self.collect_expr(e)?;
                match op.val {
                    UnOp::Not => {
                        self.env.unify_ty(expr.ty, TyKind::Bool, expr.span)?;
                        self.env.unify_ty(e.ty, TyKind::Bool, e.span)
                    }
                    UnOp::Neg => self.env.unify(expr.ty, e.ty, e.span),
                }
            }
            ExprKind::Variable(.., ty) => self.env.unify(expr.ty, *ty, expr.span),
            ExprKind::Block(block) => {
                self.collect_block(block)?;
                self.env.unify(expr.ty, block.ty, block.span)
            }
            ExprKind::If {
                cond,
                then_clause,
                else_clause,
            } => {
                self.collect_expr(cond)?;
                self.env.unify_ty(cond.ty, TyKind::Bool, cond.span)?;

                self.collect_block(then_clause)?;
                if let Some(else_clause) = else_clause {
                    self.collect_expr(else_clause)?;
                    self.env
                        .unify(then_clause.ty, else_clause.ty, else_clause.span)?;
                    self.env.unify(expr.ty, then_clause.ty, then_clause.span)
                } else {
                    self.env
                        .unify_ty(then_clause.ty, TyKind::Unit, then_clause.span)?;
                    self.env.unify_ty(expr.ty, TyKind::Unit, expr.span)
                }
            }
            ExprKind::Closure { params, ret, body } => self.enter_fn_scope(*ret, |this| {
                this.collect_expr(body)?;
                this.env.unify(*ret, body.ty.clone(), body.span)
            }),
            ExprKind::Call { callee, args } => {
                self.collect_expr(callee)?;
                for arg in args {
                    self.collect_expr(arg)?;
                }
                Some(())
            }
            ExprKind::Struct(name, fields, ty) => {
                for f in fields {
                    self.collect_expr(&f.expr)?;
                }

                self.env.unify(expr.ty, *ty, expr.span)
            }
            ExprKind::Field(e, name) => {
                self.collect_expr(e)?;
                let ty = self.env.get_ty(e.ty, e.span)?;
                match &*ty.0 {
                    TyKind::Struct(struct_name, fields) => {
                        let fty = match fields.get(&name.symbol) {
                            Some(t) => t,
                            None => {
                                self.handler.report(
                                    name.span,
                                    &format!(
                                        "Field {} not found on type {}",
                                        name.symbol, struct_name
                                    ),
                                );
                                return None;
                            }
                        };
                        self.env.unify(expr.ty, *fty, expr.span)
                    }
                    _ => {
                        self.handler
                            .report(name.span, &format!("Not a struct: {:?}", ty));
                        None
                    }
                }
            }
        }
    }

    fn collect_block(&mut self, block: &Block) -> Option<()> {
        self.collect_fns(&block.functions);

        for stmt in &block.stmts {
            self.collect_stmt(stmt);
            if let Stmt::Return(span, e) = stmt {
                if let Some(e) = e {
                    self.env
                        .unify(self.enclosing_fn_ret_ty.unwrap(), e.ty, e.span)?;
                } else {
                    self.env
                        .unify_ty(self.enclosing_fn_ret_ty.unwrap(), TyKind::Unit, *span)?;
                }
            }
        }

        match block.stmts.last() {
            Some(Stmt::Expr(expr, false)) => self.env.unify(block.ty, expr.ty, expr.span),
            Some(Stmt::Return(_, _)) => Some(()),
            _ => self.env.unify_ty(block.ty, TyKind::Unit, block.span),
        }
    }

    fn collect_fns(&mut self, items: &[Function]) -> Option<()> {
        for item in items {
            self.enter_fn_scope(item.ret, |this| this.collect_fn(item))?;
        }
        Some(())
    }

    fn collect_fn(&mut self, function: &Function) -> Option<()> {
        self.collect_block(&function.body)?;
        self.env
            .unify(function.ret, function.body.ty, function.body.span)
    }

    fn enter_fn_scope<F, R>(&mut self, ty: Tvar, f: F) -> R
    where
        F: FnOnce(&mut Self) -> R,
    {
        let save_ret_ty = self.enclosing_fn_ret_ty.take();
        self.enclosing_fn_ret_ty = Some(ty);
        let result = f(self);
        self.enclosing_fn_ret_ty = save_ret_ty;
        result
    }
}
