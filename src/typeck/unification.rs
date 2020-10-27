use crate::{
    err::Handler,
    parse::ast::{BinOp, UnOp},
};

use super::{
    hir::{Ast, Block, Expr, ExprKind, Function, Stmt, Struct},
    ty::{Tvar, TyContext, TyKind},
};

struct Unifier<'a> {
    enclosing_fn_ret_ty: Option<Tvar>,
    env: &'a mut TyContext,
    handler: &'a Handler,
}

pub fn unify(ast: &Ast, env: &mut TyContext, handler: &Handler) -> Option<()> {
    let mut unifier = Unifier::new(env, handler);
    unifier.unify_structs(&ast.structs)?;
    unifier.unify_fns(&ast.functions)?;
    unifier.unify_stmts(&ast.stmts)
}

impl<'a> Unifier<'a> {
    fn new(env: &'a mut TyContext, handler: &'a Handler) -> Self {
        Self {
            enclosing_fn_ret_ty: None,
            env,
            handler,
        }
    }

    fn unify_stmts(&mut self, ast: &[Stmt]) -> Option<()> {
        for stmt in ast {
            self.unify_stmt(stmt)?;
        }
        Some(())
    }

    fn unify_stmt(&mut self, stmt: &Stmt) -> Option<()> {
        match stmt {
            Stmt::Expr(expr, ..) => self.unify_expr(expr),
            Stmt::Let { ty, init, .. } => {
                if let Some(init) = init {
                    self.unify_expr(init)?;
                    self.env.unify(*ty, init.ty, init.span)?;
                }
                Some(())
            }
            Stmt::Assign { name, val } => {
                self.unify_expr(name)?;
                self.unify_expr(val)?;
                self.env.unify(name.ty, val.ty, val.span)
            }
            Stmt::While { cond, body } => {
                self.unify_expr(cond)?;
                self.unify_block(body)?;
                self.env.unify_ty(cond.ty, TyKind::Bool, cond.span)
            }
            Stmt::Return(_, e) => {
                if let Some(e) = e {
                    self.unify_expr(e)?;
                }
                Some(())
            }
            Stmt::Continue(_) | Stmt::Break(_) => Some(()),
        }
    }

    fn unify_expr(&mut self, expr: &Expr) -> Option<()> {
        match &expr.kind {
            ExprKind::Binary {
                op, left, right, ..
            } => {
                self.unify_expr(left)?;
                self.unify_expr(right)?;
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
                self.unify_expr(e)?;
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
                self.unify_block(block)?;
                self.env.unify(expr.ty, block.ty, block.span)
            }
            ExprKind::If {
                cond,
                then_clause,
                else_clause,
            } => {
                self.unify_expr(cond)?;
                self.env.unify_ty(cond.ty, TyKind::Bool, cond.span)?;

                self.unify_block(then_clause)?;
                if let Some(else_clause) = else_clause {
                    self.unify_expr(else_clause)?;
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
                this.unify_expr(body)?;
                this.env.unify(*ret, body.ty.clone(), body.span)?;
                this.env.unify_ty(
                    expr.ty,
                    TyKind::Fn(params.iter().map(|p| p.ty).collect(), *ret),
                    expr.span,
                )
            }),
            ExprKind::Call { callee, args } => {
                self.unify_expr(callee)?;
                for arg in args {
                    self.unify_expr(arg)?;
                }

                let ty = self.env.get_ty(callee.ty, callee.span)?;
                match &*ty.0 {
                    TyKind::Fn(params, ret) => {
                        for (param, arg) in params.iter().zip(args) {
                            self.env.unify(*param, arg.ty, arg.span)?;
                        }
                        self.env.unify(*ret, expr.ty, expr.span)?;
                    }
                    ty => {
                        self.handler.report(
                            callee.span,
                            &format!("Type error: Expected Function, Actual: {:?}", ty,),
                        );
                        return None;
                    }
                }
                Some(())
            }
            ExprKind::Struct(.., fields, ty) => {
                for f in fields {
                    self.unify_expr(&f.expr)?;
                }

                self.env.unify(expr.ty, *ty, expr.span)
            }
            ExprKind::Field(e, ..) => self.unify_expr(e),
        }
    }

    fn unify_block(&mut self, block: &Block) -> Option<()> {
        self.unify_fns(&block.functions);

        for stmt in &block.stmts {
            self.unify_stmt(stmt);
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

    fn unify_structs(&mut self, structs: &[Struct]) -> Option<()> {
        for s in structs {
            self.unify_struct(s)?;
        }
        Some(())
    }

    fn unify_struct(&mut self, s: &Struct) -> Option<()> {
        self.env.unify_ty(
            s.ty,
            TyKind::Struct(
                s.name.symbol,
                s.fields.iter().map(|f| (f.name.symbol, f.ty)).collect(),
            ),
            s.name.span,
        )
    }

    fn unify_fns(&mut self, items: &[Function]) -> Option<()> {
        for item in items {
            self.enter_fn_scope(item.ret, |this| this.unify_fn(item))?;
        }
        Some(())
    }

    fn unify_fn(&mut self, function: &Function) -> Option<()> {
        self.unify_block(&function.body)?;
        self.env
            .unify(function.ret, function.body.ty, function.body.span)?;
        self.env.unify_ty(
            function.ty,
            TyKind::Fn(function.params.iter().map(|p| p.ty).collect(), function.ret),
            function.name.span,
        )
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
