use std::rc::Rc;

use crate::{
    err::{Handler, Result},
    lex::Span,
    parse::ast::{BinOp, UnOp},
};

use super::{
    hir::*,
    ty::{Ty, TyContext, TypeVar},
};

struct Unifier<'a> {
    enclosing_fn_ret_ty: Option<TypeVar>,
    enclosing_loop_ty: Option<TypeVar>,
    env: &'a mut TyContext,
    handler: &'a Handler,
}

pub fn unify(ast: &Ast, env: &mut TyContext, handler: &Handler) -> Result<()> {
    let mut unifier = Unifier::new(env, handler);
    unifier.unify_structs(&ast.structs)?;
    unifier.unify_fn_headers(&ast.functions)?;
    unifier.unify_impls(&ast.impls)?;
    unifier.unify_fn_bodies(&ast.functions)?;
    unifier.unify_stmts(&ast.stmts)
}

impl<'a> Unifier<'a> {
    fn new(env: &'a mut TyContext, handler: &'a Handler) -> Self {
        Self {
            enclosing_fn_ret_ty: None,
            enclosing_loop_ty: None,
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
            Stmt::Expr(expr, ..) => {
                self.unify_expr(expr)?;
            }
            Stmt::Let { ty, init, .. } => {
                if let Some(init) = init {
                    self.env.unify(*ty, init.ty, init.span)?;
                    self.unify_expr(init)?;
                }
            }
        }
        Ok(())
    }

    fn unify_expr(&mut self, expr: &Expr) -> Result<()> {
        match &expr.kind {
            ExprKind::Binary { op, lhs, rhs } => {
                self.unify_expr(lhs)?;
                self.unify_expr(rhs)?;
                self.env.unify(lhs.ty, rhs.ty, rhs.span)?;
                match op.val {
                    BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem => {
                        self.env.unify(expr.ty, lhs.ty, expr.span)?
                    }
                    BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge | BinOp::Ne | BinOp::Eq => {
                        self.env.unify(expr.ty, self.env.bool(), expr.span)?
                    }
                    BinOp::And | BinOp::Or => {
                        self.env.unify(expr.ty, lhs.ty, lhs.span)?;
                        self.env.unify(expr.ty, self.env.bool(), expr.span)?
                    }
                }
            }
            ExprKind::Tuple(exprs) => {
                for e in exprs {
                    self.unify_expr(e)?;
                }
                let tuple_ty = Ty::Tuple(exprs.iter().map(|e| e.ty).collect());
                let ty = self.env.alloc_ty(tuple_ty);
                self.env.unify(expr.ty, ty, expr.span)?;
            }
            ExprKind::Literal(_, ty, _) => self.env.unify(expr.ty, *ty, expr.span)?,
            ExprKind::Unary { op, expr: e, .. } => {
                self.unify_expr(e)?;
                match op.val {
                    UnOp::Not => {
                        self.env.unify(self.env.bool(), e.ty, e.span)?;
                        self.env.unify(expr.ty, self.env.bool(), expr.span)?;
                    }
                    UnOp::Neg => self.env.unify(expr.ty, e.ty, e.span)?,
                }
            }
            ExprKind::Variable(.., ty) => self.env.unify(expr.ty, *ty, expr.span)?,
            ExprKind::Block(block) => {
                self.env.unify(expr.ty, block.ty, block.span)?;
                self.unify_block(block)?;
            }
            ExprKind::If {
                cond,
                then_clause,
                else_clause,
            } => {
                self.env.unify(self.env.bool(), cond.ty, cond.span)?;
                self.unify_expr(cond)?;

                self.env.unify(expr.ty, then_clause.ty, then_clause.span)?;
                self.unify_block(then_clause)?;

                if let Some(else_clause) = else_clause {
                    self.env.unify(expr.ty, else_clause.ty, else_clause.span)?;
                    self.unify_expr(else_clause)?;
                } else {
                    self.env.unify(expr.ty, self.env.unit(), expr.span)?;
                }

                if let Ty::Infer(_) = self.env.resolve_ty(expr.ty) {
                    self.env.unify(expr.ty, self.env.unit(), expr.span)?;
                }
            }
            ExprKind::Closure { params, ret, body } => self.enter_fn_scope(*ret, |this| {
                this.env.unify(*ret, body.ty, body.span)?;
                let params = params.iter().map(|p| p.param_ty).collect();
                let ty = this.env.alloc_ty(Ty::Fn(params, *ret));
                this.env.unify(expr.ty, ty, expr.span)?;
                this.unify_expr(body)?;
                Ok(())
            })?,
            ExprKind::Call { callee, args } => {
                self.unify_expr(callee)?;
                let ty = self.env.resolve_ty(callee.ty);
                self.unify_fn_call(expr, None, args, &ty, callee.span)?;
                for arg in args {
                    self.unify_expr(arg)?;
                }
            }
            ExprKind::Struct(name, fields, ty_var) => {
                let ty = self.env.resolve_ty(*ty_var);
                match ty {
                    Ty::Struct(_, _, fields2) => {
                        for f in fields {
                            match fields2.get(f.name.symbol) {
                                Some(t) => self.env.unify(t, f.expr.ty, f.expr.span)?,
                                None => {
                                    return self
                                        .handler
                                        .mk_err(f.name.span, &format!("`{}` does not have this field", name.symbol));
                                }
                            }
                        }

                        if fields.len() != fields2.len() {
                            let mut extra = vec![];
                            for f2 in fields2.keys() {
                                if !fields.iter().any(|f| f.name.symbol == f2) {
                                    extra.push(f2.to_string());
                                }
                            }
                            return self
                                .handler
                                .mk_err(name.span, &format!("missing fields: {}", extra.join(", ")));
                        }
                    }
                    Ty::Infer(id) => {
                        log::warn!("Type not found for {:?}", id);
                        return self.handler.mk_err(name.span, "Type not found in this scope");
                    }
                    ty => {
                        return self
                            .handler
                            .mk_err(name.span, &format!("Expected Struct, found on type `{}`", ty));
                    }
                }

                for f in fields {
                    self.unify_expr(&f.expr)?;
                }

                self.env.unify(expr.ty, *ty_var, expr.span)?;
            }
            ExprKind::Field(e, field_name) => {
                self.unify_expr(e)?;
                let ty = self.env.resolve_ty(e.ty);
                match &ty {
                    Ty::Struct(_, name, fields) => {
                        if let Some(f) = fields.get(field_name.symbol) {
                            self.env.unify(expr.ty, f, field_name.span)?;
                        } else {
                            return self.handler.mk_err(
                                field_name.span,
                                &format!("Field `{}` not found on type `{}`", field_name.symbol, name),
                            );
                        }
                    }
                    Ty::Tuple(tys) => {
                        let index = field_name.symbol.as_str_with(|s| {
                            if s == "0" {
                                Some(0)
                            } else if s.starts_with('0') {
                                None
                            } else {
                                s.parse::<usize>().ok()
                            }
                        });
                        let index = match index {
                            Some(i) if i < tys.len() => i,
                            _ => {
                                return self.handler.mk_err(
                                    field_name.span,
                                    &format!("Field `{}` not found on type `{}`", field_name.symbol, ty),
                                );
                            }
                        };
                        self.env.unify(expr.ty, tys[index], field_name.span)?;
                    }
                    Ty::Infer(_) => {
                        return self
                            .handler
                            .mk_err(e.span, "Type cannot be inferred. Please add type annotations");
                    }
                    ty => {
                        return self.handler.mk_err(
                            field_name.span,
                            &format!("Field `{}` not found on type `{}`", field_name.symbol, ty),
                        );
                    }
                }
            }
            ExprKind::AssocMethod { ty, name: method_name } => {
                let ty = self.env.resolve_ty(*ty);
                match ty {
                    Ty::Struct(id, name, ..) => {
                        let method_ty = match self.env.get_method(id, method_name.symbol) {
                            Some(ty) => ty,
                            None => {
                                return self.handler.mk_err(
                                    method_name.span,
                                    &format!("Method `{}` not found on type `{}`", method_name.symbol, name),
                                );
                            }
                        };

                        self.env.unify(expr.ty, method_ty, method_name.span)?;
                    }
                    Ty::Infer(_) => {
                        return self
                            .handler
                            .mk_err(method_name.span, "Type cannot be inferred. Please add type annotations");
                    }
                    ty => {
                        return self.handler.mk_err(
                            method_name.span,
                            &format!("Type error: Expected struct, Actual: `{}`", ty,),
                        )
                    }
                }
            }
            ExprKind::MethodCall {
                callee,
                name: method_name,
                args,
            } => {
                self.unify_expr(callee)?;
                let ty = self.env.resolve_ty(callee.ty);
                match ty {
                    Ty::Struct(id, name, fields) => {
                        match self.env.get_method(id, method_name.symbol) {
                            Some(ty) => {
                                let method_ty = self.env.resolve_ty(ty);
                                self.unify_fn_call(expr, Some(callee), args, &method_ty, method_name.span)?;
                            }
                            None => match fields.get(method_name.symbol) {
                                Some(ty) => {
                                    let method_ty = self.env.resolve_ty(ty);
                                    self.unify_fn_call(expr, None, args, &method_ty, method_name.span)?;
                                }
                                None => {
                                    return self.handler.mk_err(
                                        method_name.span,
                                        &format!(
                                            "Method or Field `{}` not found on type `{}`",
                                            method_name.symbol, name
                                        ),
                                    )
                                }
                            },
                        }
                        for arg in args {
                            self.unify_expr(arg)?;
                        }
                    }
                    Ty::Tuple(fields) => {
                        let index = match method_name.symbol.parse::<usize>() {
                            Ok(i) => i,
                            Err(_) => {
                                return self.handler.mk_err(
                                    method_name.span,
                                    &format!("Method or Field `{}` not found on tuple", method_name.symbol),
                                )
                            }
                        };
                        match fields.get(index) {
                            Some(ty) => {
                                let method_ty = self.env.resolve_ty(*ty);
                                self.unify_fn_call(expr, None, args, &method_ty, method_name.span)?;
                            }
                            None => {
                                return self.handler.mk_err(
                                    method_name.span,
                                    &format!("Method or Field `{}` not found on tuple", method_name.symbol),
                                )
                            }
                        }
                        for arg in args {
                            self.unify_expr(arg)?;
                        }
                    }
                    Ty::Infer(_) => {
                        return self
                            .handler
                            .mk_err(callee.span, "Type cannot be inferred. Please add type annotations");
                    }
                    ty => {
                        return self.handler.mk_err(
                            method_name.span,
                            &format!("Method or Field `{}` not found on type `{}`", method_name.symbol, ty),
                        )
                    }
                }
            }
            ExprKind::Assign { lhs, rhs } => {
                self.env.unify(expr.ty, self.env.unit(), expr.span)?;
                self.unify_expr(lhs)?;
                self.unify_expr(rhs)?;
                self.env.unify(lhs.ty, rhs.ty, rhs.span)?;
            }
            ExprKind::Return(e) => {
                let ret_ty = self.enclosing_fn_ret_ty.unwrap();
                if let Some(e) = e {
                    self.env.unify(ret_ty, e.ty, e.span)?;
                    self.unify_expr(e)?;
                } else {
                    self.env.unify(ret_ty, self.env.unit(), expr.span)?;
                }
            }
            ExprKind::Continue => {}
            ExprKind::Break(e) => {
                let loop_ty = self.enclosing_loop_ty.unwrap();
                if let Some(e) = e {
                    self.env.unify(loop_ty, e.ty, e.span)?;
                    self.unify_expr(e)?;
                } else {
                    self.env.unify(loop_ty, self.env.unit(), expr.span)?;
                }
            }
            ExprKind::Loop(body) => {
                self.env.unify(self.env.unit(), body.ty, body.span)?;
                self.enter_loop_scope(expr.ty, |this| this.unify_block(body))?;
            }
        }
        Ok(())
    }

    fn unify_block(&mut self, block: &Block) -> Result<()> {
        self.unify_structs(&block.structs)?;
        self.unify_fn_headers(&block.functions)?;
        self.unify_impls(&block.impls)?;
        self.unify_fn_bodies(&block.functions)?;

        match block.stmts.last() {
            Some(Stmt::Expr(expr, false)) => {
                if !expr.is_flow_control() {
                    self.env.unify(block.ty, expr.ty, expr.span)?;
                }
            }
            _ => self.env.unify(block.ty, self.env.unit(), block.span)?,
        }

        for stmt in &block.stmts {
            self.unify_stmt(stmt)?;
        }

        Ok(())
    }

    fn unify_structs(&mut self, structs: &[Struct]) -> Result<()> {
        for s in structs {
            self.unify_struct(s)?;
        }
        Ok(())
    }

    fn unify_struct(&mut self, s: &Struct) -> Result<()> {
        let fields = s.fields.iter().map(|f| (f.name.symbol, f.ty)).collect();
        self.env
            .unify_value(s.ty, Ty::Struct(s.ty, s.name.symbol, Rc::new(fields)));
        Ok(())
    }

    fn unify_impls(&mut self, impls: &[Impl]) -> Result<()> {
        for i in impls {
            self.unify_impl(i)?;
        }
        Ok(())
    }

    fn unify_impl(&mut self, i: &Impl) -> Result<()> {
        for f in &i.functions {
            if self.env.add_method(i.ty, f.name.symbol, f.ty) {
                return self
                    .handler
                    .mk_err(f.name.span, "Function with same name already defined for this type");
            }
        }
        self.unify_fns(&i.functions)?;
        Ok(())
    }

    fn unify_fns(&mut self, items: &[Function]) -> Result<()> {
        self.unify_fn_headers(items)?;
        self.unify_fn_bodies(items)?;
        Ok(())
    }

    fn unify_fn_headers(&mut self, items: &[Function]) -> Result<()> {
        for item in items {
            self.unify_fn_header(item)?;
        }
        Ok(())
    }

    fn unify_fn_bodies(&mut self, items: &[Function]) -> Result<()> {
        for item in items {
            self.enter_fn_scope(item.ret, |this| this.unify_fn_body(item))?;
        }
        Ok(())
    }

    fn unify_fn_header(&mut self, function: &Function) -> Result<()> {
        for (idx, p) in function.params.iter().enumerate() {
            if p.name.is_self_param() && idx != 0 {
                return self.handler.mk_err(p.name.span, "`self` must be the first parameter");
            }
        }

        let params = function.params.iter().map(|p| p.param_ty).collect();
        self.env.unify_value(function.ty, Ty::Fn(params, function.ret));

        Ok(())
    }

    fn unify_fn_body(&mut self, function: &Function) -> Result<()> {
        self.env.unify(function.ret, function.body.ty, function.body.span)?;
        self.unify_block(&function.body)?;
        Ok(())
    }

    fn unify_fn_call(
        &mut self,
        expr: &Expr,
        self_param: Option<&Expr>,
        args: &[Expr],
        fn_ty: &Ty,
        span: Span,
    ) -> Result<()> {
        match fn_ty {
            Ty::Fn(params, ret) => {
                let arg_mismatch = |expected: usize, actual: usize| {
                    self.handler.mk_err(
                        expr.span,
                        &format!(
                            "Number of arguments mismatch: Expected: `{}`, actual: `{}`",
                            expected, actual
                        ),
                    )
                };

                let mut params = &params[..];
                match (params, self_param) {
                    ([first, rest_params @ ..], Some(self_param)) => {
                        if rest_params.len() != args.len() {
                            return arg_mismatch(rest_params.len(), args.len());
                        }
                        params = rest_params;
                        self.env.unify(*first, self_param.ty, self_param.span)?;
                    }
                    ([], Some(_)) => {
                        return self
                            .handler
                            .mk_err(span, "this is an associated function, not a method");
                    }
                    _ => {
                        if params.len() != args.len() {
                            return arg_mismatch(params.len(), args.len());
                        }
                    }
                }

                for (param, arg) in params.iter().zip(args) {
                    self.env.unify(*param, arg.ty, arg.span)?;
                }
                self.env.unify(*ret, expr.ty, expr.span)?;
            }
            Ty::Infer(_) => {
                return self
                    .handler
                    .mk_err(span, "Type cannot be inferred. Please add type annotations");
            }
            ty => {
                return self
                    .handler
                    .mk_err(span, &format!("Type error: Expected Function, Actual: `{}`", ty));
            }
        }
        Ok(())
    }

    fn enter_fn_scope<F, R>(&mut self, ty: TypeVar, f: F) -> R
    where
        F: FnOnce(&mut Self) -> R,
    {
        let save_ret_ty = self.enclosing_fn_ret_ty.take();
        self.enclosing_fn_ret_ty = Some(ty);
        let result = f(self);
        self.enclosing_fn_ret_ty = save_ret_ty;
        result
    }

    fn enter_loop_scope<F, R>(&mut self, ty: TypeVar, f: F) -> R
    where
        F: FnOnce(&mut Self) -> R,
    {
        let save_loop_ty = self.enclosing_loop_ty.take();
        self.enclosing_loop_ty = Some(ty);
        let result = f(self);
        self.enclosing_loop_ty = save_loop_ty;
        result
    }
}
