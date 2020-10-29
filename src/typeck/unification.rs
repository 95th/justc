use crate::{
    err::{Handler, Result},
    lex::TokenKind,
    parse::ast::{BinOp, UnOp},
};

use super::{
    hir::{Ast, Block, Expr, ExprKind, Function, Impl, Stmt, Struct},
    ty::{Ty, TyContext},
};

struct Unifier<'a> {
    enclosing_fn_ret_ty: Option<Ty>,
    enclosing_self_ty: Option<Ty>,
    env: &'a mut TyContext,
    handler: &'a Handler,
}

pub fn unify(ast: &Ast, env: &mut TyContext, handler: &Handler) -> Result<()> {
    let mut unifier = Unifier::new(env, handler);
    unifier.unify_structs(&ast.structs)?;
    unifier.unify_impls(&ast.impls)?;
    unifier.unify_fns(&ast.functions)?;
    unifier.unify_stmts(&ast.stmts)
}

impl<'a> Unifier<'a> {
    fn new(env: &'a mut TyContext, handler: &'a Handler) -> Self {
        Self {
            enclosing_fn_ret_ty: None,
            enclosing_self_ty: None,
            env,
            handler,
        }
    }

    fn unify_stmts(&mut self, ast: &[Stmt]) -> Result<()> {
        for stmt in ast {
            self.unify_stmt(stmt)?;
        }
        Ok(())
    }

    fn unify_stmt(&mut self, stmt: &Stmt) -> Result<()> {
        match stmt {
            Stmt::Expr(expr, ..) => self.unify_expr(expr),
            Stmt::Let { ty, init, .. } => {
                if let Some(init) = init {
                    self.unify_expr(init)?;
                    self.env.unify(ty, &init.ty, init.span)?;
                }
                Ok(())
            }
            Stmt::Assign { name, val } => {
                self.unify_expr(name)?;
                self.unify_expr(val)?;
                self.env.unify(&name.ty, &val.ty, val.span)
            }
            Stmt::While { cond, body } => {
                self.unify_expr(cond)?;
                self.unify_block(body)?;
                self.env.unify(&cond.ty, &Ty::Bool, cond.span)
            }
            Stmt::Return(_, e) => {
                if let Some(e) = e {
                    self.unify_expr(e)?;
                }
                Ok(())
            }
            Stmt::Continue(_) | Stmt::Break(_) => Ok(()),
        }
    }

    fn unify_expr(&mut self, expr: &Expr) -> Result<()> {
        match &expr.kind {
            ExprKind::Binary {
                op, left, right, ..
            } => {
                self.unify_expr(left)?;
                self.unify_expr(right)?;
                self.env.unify(&left.ty, &right.ty, right.span)?;
                match op.val {
                    BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem => {
                        self.env.unify(&expr.ty, &left.ty, left.span)
                    }
                    BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge | BinOp::Ne | BinOp::Eq => {
                        self.env.unify(&expr.ty, &Ty::Bool, expr.span)
                    }
                    BinOp::And | BinOp::Or => {
                        self.env.unify(&left.ty, &Ty::Bool, left.span)?;
                        self.env.unify(&right.ty, &Ty::Bool, right.span)
                    }
                }
            }
            ExprKind::Literal(_, ty, _) => self.env.unify(&expr.ty, ty, expr.span),
            ExprKind::Unary { op, expr: e, .. } => {
                self.unify_expr(e)?;
                match op.val {
                    UnOp::Not => {
                        self.env.unify(&expr.ty, &Ty::Bool, expr.span)?;
                        self.env.unify(&e.ty, &Ty::Bool, e.span)
                    }
                    UnOp::Neg => self.env.unify(&expr.ty, &e.ty, e.span),
                }
            }
            ExprKind::Variable(.., ty) => self.env.unify(&expr.ty, ty, expr.span),
            ExprKind::Block(block) => {
                self.unify_block(block)?;
                self.env.unify(&expr.ty, &block.ty, block.span)
            }
            ExprKind::If {
                cond,
                then_clause,
                else_clause,
            } => {
                self.unify_expr(cond)?;
                self.env.unify(&cond.ty, &Ty::Bool, cond.span)?;

                self.unify_block(then_clause)?;
                if let Some(else_clause) = else_clause {
                    self.unify_expr(else_clause)?;
                    self.env
                        .unify(&then_clause.ty, &else_clause.ty, else_clause.span)?;
                    self.env.unify(&expr.ty, &then_clause.ty, then_clause.span)
                } else {
                    self.env
                        .unify(&then_clause.ty, &Ty::Unit, then_clause.span)?;
                    self.env.unify(&expr.ty, &Ty::Unit, expr.span)
                }
            }
            ExprKind::Closure { params, ret, body } => self.enter_fn_scope(ret.clone(), |this| {
                this.env.unify(
                    &expr.ty,
                    &Ty::Fn(
                        params.iter().map(|p| p.param_ty.ty.clone()).collect(),
                        Box::new(ret.clone()),
                    ),
                    expr.span,
                )?;
                this.unify_expr(body)?;
                this.env.unify(&ret, &body.ty, body.span)
            }),
            ExprKind::Call { callee, args } => {
                self.unify_expr(callee)?;

                let ty = self.env.resolve_ty(&callee.ty);
                match &*ty {
                    Ty::Fn(params, ret) => {
                        for (param, arg) in params.iter().zip(args) {
                            self.env.unify(param, &arg.ty, arg.span)?;
                        }
                        self.env.unify(ret, &expr.ty, expr.span)?;
                    }
                    Ty::Infer(_) => {
                        return self.handler.mk_err(
                            callee.span,
                            "Type cannot be inferred. Please add type annotations",
                        );
                    }
                    ty => {
                        return self.handler.mk_err(
                            callee.span,
                            &format!("Type error: Expected Function, Actual: {:?}", ty),
                        );
                    }
                }
                for arg in args {
                    self.unify_expr(arg)?;
                }
                Ok(())
            }
            ExprKind::Struct(name, fields, ty) => {
                if name.kind == TokenKind::SelfTy {
                    self.env
                        .unify(self.enclosing_self_ty.as_ref().unwrap(), ty, name.span)?;
                }
                let ty = self.env.resolve_ty(ty);
                match &*ty {
                    Ty::Struct(.., fields2) => {
                        if fields.len() != fields2.len() {
                            return self.handler.mk_err(expr.span, "Number of fields mismatch");
                        }

                        for f in fields {
                            match fields2.get(&f.name.symbol) {
                                Some(t) => self.env.unify(t, &f.expr.ty, f.expr.span)?,
                                None => {
                                    return self.handler.mk_err(f.name.span, "Field not found");
                                }
                            }
                        }
                    }
                    Ty::Infer(_) => {
                        return self
                            .handler
                            .mk_err(name.span, "Type not found in this scope");
                    }
                    ty => {
                        return self.handler.mk_err(
                            name.span,
                            &format!("Expected Struct, found on type {:?}", ty),
                        );
                    }
                }

                for f in fields {
                    self.unify_expr(&f.expr)?;
                }

                self.env.unify(&expr.ty, &*ty, expr.span)
            }
            ExprKind::Field(e, field_name) => {
                self.unify_expr(e)?;
                let ty = self.env.resolve_ty(&e.ty);
                match &*ty {
                    Ty::Struct(.., name, fields) => {
                        if let Some(f) = fields.get(&field_name.symbol) {
                            self.env.unify(f, &expr.ty, field_name.span)
                        } else {
                            self.handler.mk_err(
                                field_name.span,
                                &format!("Field {} not found on type {}", field_name.symbol, name),
                            )
                        }
                    }
                    Ty::Infer(_) => self.handler.mk_err(
                        e.span,
                        "Type cannot be inferred. Please add type annotations",
                    ),
                    ty => self.handler.mk_err(
                        field_name.span,
                        &format!("Field {} not found on type {:?}", field_name.symbol, ty),
                    ),
                }
            }
        }
    }

    fn unify_block(&mut self, block: &Block) -> Result<()> {
        self.unify_structs(&block.structs)?;
        self.unify_impls(&block.impls)?;
        self.unify_fns(&block.functions)?;

        for stmt in &block.stmts {
            self.unify_stmt(stmt)?;
            if let Stmt::Return(span, e) = stmt {
                if let Some(e) = e {
                    self.env
                        .unify(self.enclosing_fn_ret_ty.as_ref().unwrap(), &e.ty, e.span)?;
                } else {
                    self.env
                        .unify(self.enclosing_fn_ret_ty.as_ref().unwrap(), &Ty::Unit, *span)?;
                }
            }
        }

        match block.stmts.last() {
            Some(Stmt::Expr(expr, false)) => self.env.unify(&block.ty, &expr.ty, expr.span),
            Some(Stmt::Return(_, _)) => Ok(()),
            _ => self.env.unify(&block.ty, &Ty::Unit, block.span),
        }
    }

    fn unify_structs(&mut self, structs: &[Struct]) -> Result<()> {
        for s in structs {
            self.unify_struct(s)?;
        }
        Ok(())
    }

    fn unify_struct(&mut self, s: &Struct) -> Result<()> {
        self.env.unify(
            &s.ty,
            &Ty::Struct(
                s.id,
                s.name.symbol,
                s.fields
                    .iter()
                    .map(|f| (f.name.symbol, f.ty.clone()))
                    .collect(),
            ),
            s.name.span,
        )
    }

    fn unify_fns(&mut self, items: &[Function]) -> Result<()> {
        for item in items {
            self.unify_fn_header(item)?;
        }

        for item in items {
            self.enter_fn_scope(item.ret.ty.clone(), |this| this.unify_fn_body(item))?;
        }
        Ok(())
    }

    fn unify_fn_header(&mut self, function: &Function) -> Result<()> {
        let mut has_self_param = false;
        for (idx, p) in function.params.iter().enumerate() {
            if p.name.kind == TokenKind::SelfParam {
                if idx != 0 {
                    return self
                        .handler
                        .mk_err(p.name.span, "`self` must be the first parameter");
                }

                if has_self_param {
                    return self
                        .handler
                        .mk_err(p.name.span, "Multiple `self` not allowed");
                }

                self.env.unify(
                    self.enclosing_self_ty.as_ref().unwrap(),
                    &p.param_ty.ty,
                    p.param_ty.span,
                )?;
                has_self_param = true;
            }

            if p.param_ty.is_self {
                self.env.unify(
                    self.enclosing_self_ty.as_ref().unwrap(),
                    &p.param_ty.ty,
                    p.param_ty.span,
                )?;
            }
        }

        self.env.unify(
            &function.ty,
            &Ty::Fn(
                function
                    .params
                    .iter()
                    .map(|p| p.param_ty.ty.clone())
                    .collect(),
                Box::new(function.ret.ty.clone()),
            ),
            function.name.span,
        )?;
        if function.ret.is_self {
            self.env.unify(
                self.enclosing_self_ty.as_ref().unwrap(),
                &function.ret.ty,
                function.ret.span,
            )?;
        }
        Ok(())
    }

    fn unify_fn_body(&mut self, function: &Function) -> Result<()> {
        self.unify_block(&function.body)?;
        self.env
            .unify(&function.ret.ty, &function.body.ty, function.body.span)?;
        Ok(())
    }

    fn unify_impls(&mut self, impls: &[Impl]) -> Result<()> {
        for item in impls {
            self.unify_impl(item)?;
        }
        Ok(())
    }

    fn unify_impl(&mut self, item: &Impl) -> Result<()> {
        self.enter_self_scope(item.ty.clone(), |this| this.unify_fns(&item.functions))
    }

    fn enter_fn_scope<F, R>(&mut self, ty: Ty, f: F) -> R
    where
        F: FnOnce(&mut Self) -> R,
    {
        let save_ret_ty = self.enclosing_fn_ret_ty.take();
        self.enclosing_fn_ret_ty = Some(ty);
        let result = f(self);
        self.enclosing_fn_ret_ty = save_ret_ty;
        result
    }

    fn enter_self_scope<F, R>(&mut self, ty: Ty, f: F) -> R
    where
        F: FnOnce(&mut Self) -> R,
    {
        let save_ty = self.enclosing_self_ty.take();
        self.enclosing_self_ty = Some(ty);
        let result = f(self);
        self.enclosing_self_ty = save_ty;
        result
    }
}
