use std::rc::Rc;

use crate::{
    err::{ErrHandler, Result},
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
    tyctx: &'a mut TyContext,
    handler: &'a ErrHandler,
}

pub fn unify(ast: &Ast, env: &mut TyContext, handler: &ErrHandler) -> Result<()> {
    let mut unifier = Unifier::new(env, handler);
    unifier.unify_impls(&ast.impls)?;
    unifier.unify_fn_bodies(&ast.functions)?;
    unifier.unify_stmts(&ast.stmts)
}

impl<'a> Unifier<'a> {
    fn new(tyctx: &'a mut TyContext, handler: &'a ErrHandler) -> Self {
        Self {
            enclosing_fn_ret_ty: None,
            enclosing_loop_ty: None,
            tyctx,
            handler,
        }
    }

    fn unify_stmts(&mut self, mut stmts: &[Stmt]) -> Result<()> {
        while let [stmt, rest @ ..] = stmts {
            self.unify_stmt(stmt, rest.is_empty())?;
            stmts = rest;
        }
        Ok(())
    }

    fn unify_stmt(&mut self, stmt: &Stmt, is_last: bool) -> Result<()> {
        if !is_last {
            match *stmt {
                Stmt::Expr(ref e, semi) if !semi || e.is_flow_control() => {
                    self.tyctx.unify(self.tyctx.unit(), e.ty, e.span)?;
                }
                _ => {}
            }
        }

        match stmt {
            Stmt::Expr(expr, _) => {
                self.unify_expr(expr, expr.ty)?;
            }
            Stmt::Let { ty, init, .. } => {
                if let Some(init) = init {
                    self.unify_expr(init, *ty)?;
                }
            }
        }
        Ok(())
    }

    fn unify_expr(&mut self, expr: &Expr, expected: TypeVar) -> Result<()> {
        self.tyctx.unify(expected, expr.ty, expr.span)?;
        match &expr.kind {
            ExprKind::Binary { op, lhs, rhs } => {
                self.unify_expr(lhs, lhs.ty)?;
                self.unify_expr(rhs, lhs.ty)?;
                match op.val {
                    BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem => {
                        self.tyctx.unify(expected, lhs.ty, expr.span)?
                    }
                    BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge | BinOp::Ne | BinOp::Eq => {
                        self.tyctx.unify(expected, self.tyctx.bool(), expr.span)?
                    }
                    BinOp::And | BinOp::Or => {
                        self.tyctx.unify(expected, lhs.ty, lhs.span)?;
                        self.tyctx.unify(expected, self.tyctx.bool(), expr.span)?
                    }
                }
            }
            ExprKind::Tuple(exprs) => {
                let resolved = self.tyctx.resolve_ty(expected);
                match resolved {
                    Ty::Tuple(tys) => {
                        if tys.len() != exprs.len() {
                            return self.handler.mk_err(
                                expr.span,
                                &format!("Tuple size mismatch: Expected: {}, Actual: {}", tys.len(), exprs.len()),
                            );
                        }
                        for (e, &t) in exprs.iter().zip(tys.iter()) {
                            self.unify_expr(e, t)?;
                        }
                    }
                    Ty::Infer(v) => {
                        for e in exprs {
                            self.unify_expr(e, e.ty)?;
                        }
                        let tuple_ty = Ty::Tuple(exprs.iter().map(|e| e.ty).collect());
                        self.tyctx.unify_value(v, tuple_ty);
                    }
                    _ => {
                        return self.handler.mk_err(
                            expr.span,
                            &format!("Type error: Expected: `{}`, Actual: Tuple", resolved),
                        );
                    }
                }
            }
            ExprKind::Literal(_, ty, _) => self.tyctx.unify(expected, *ty, expr.span)?,
            ExprKind::Unary { op, expr: e, .. } => match op.val {
                UnOp::Not => {
                    self.unify_expr(e, self.tyctx.bool())?;
                    self.tyctx.unify(expected, self.tyctx.bool(), expr.span)?;
                }
                UnOp::Neg => {
                    self.unify_expr(e, expected)?;
                }
            },
            ExprKind::Variable(.., ty) => self.tyctx.unify(expected, *ty, expr.span)?,
            ExprKind::Block(block) => {
                self.tyctx.unify(expected, block.ty, block.span)?;
                self.unify_block(block)?;
            }
            ExprKind::If {
                cond,
                then_clause,
                else_clause,
            } => {
                self.unify_expr(cond, self.tyctx.bool())?;

                self.tyctx.unify(expected, then_clause.ty, then_clause.span)?;
                self.unify_block(then_clause)?;

                if let Some(else_clause) = else_clause {
                    self.unify_expr(else_clause, expected)?;
                } else {
                    self.tyctx.unify(expected, self.tyctx.unit(), expr.span)?;
                }

                if let Ty::Infer(_) = self.tyctx.resolve_ty(expected) {
                    self.tyctx.unify(expected, self.tyctx.unit(), expr.span)?;
                }
            }
            ExprKind::Closure { params, ret, body } => self.enter_fn_scope(*ret, |this| {
                let params = params.iter().map(|p| p.param_ty).collect();
                let ty = this.tyctx.alloc_ty(Ty::Fn(params, *ret, Rc::from([])));
                this.tyctx.unify(expected, ty, expr.span)?;
                this.unify_expr(body, *ret)?;
                Ok(())
            })?,
            ExprKind::Call { callee, args } => {
                self.unify_expr(callee, callee.ty)?;
                let ty = self.tyctx.resolve_ty(callee.ty);
                self.unify_fn_call(expr, None, args, &ty, callee.span)?;
            }
            ExprKind::Struct(name, fields, ty_var) => {
                match self.tyctx.resolve_ty(*ty_var) {
                    Ty::Struct(..) => {}
                    Ty::Infer(_) => {
                        return self
                            .handler
                            .mk_err(expr.span, "Type cannot be inferred. Please add type annotations");
                    }
                    ty => {
                        return self
                            .handler
                            .mk_err(expr.span, &format!("Type error: Expected struct, Actual: `{}`", ty,))
                    }
                };
                log::debug!("struct literal: {ty_var:?}");
                if let Some(struct_fields) = self.tyctx.get_fields(*ty_var) {
                    for f in fields {
                        if let Some(t) = struct_fields.get(f.name.symbol) {
                            self.unify_expr(&f.expr, t)?;
                        } else {
                            return self
                                .handler
                                .mk_err(f.name.span, &format!("`{}` does not have this field", name.symbol));
                        }
                    }

                    if fields.len() != struct_fields.len() {
                        let mut missing = vec![];
                        for field_name in struct_fields.keys() {
                            if !fields.iter().any(|f| f.name.symbol == field_name) {
                                missing.push(field_name.to_string());
                            }
                        }
                        return self
                            .handler
                            .mk_err(name.span, &format!("missing fields: {}", missing.join(", ")));
                    }
                } else {
                    return self
                        .handler
                        .mk_err(name.span, &format!("`{}` has no fields", name.symbol));
                }
                self.tyctx.unify(expected, *ty_var, expr.span)?;
            }
            ExprKind::Field(e, field_name) => {
                self.unify_expr(e, e.ty)?;
                let ty = self.tyctx.resolve_ty(e.ty);
                log::debug!("Field access of {:?} = {:?}", e.ty, ty);
                match &ty {
                    Ty::Struct(_, name, _) => {
                        if let Some(f) = self.tyctx.get_field(e.ty, field_name.symbol) {
                            self.tyctx.unify(expected, f, field_name.span)?;
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
                        self.tyctx.unify(expected, tys[index], field_name.span)?;
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
            ExprKind::AssocMethod { ty, name: method_name } => match self.tyctx.resolve_ty(*ty) {
                Ty::Struct(_, name, ..) => {
                    let method_ty = match self.tyctx.get_method(*ty, method_name.symbol) {
                        Some(ty) => ty,
                        None => {
                            return self.handler.mk_err(
                                method_name.span,
                                &format!("Method `{}` not found on type `{}`", method_name.symbol, name),
                            );
                        }
                    };

                    self.tyctx.unify(expected, method_ty, method_name.span)?;
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
            },
            ExprKind::MethodCall {
                callee,
                name: method_name,
                args,
            } => {
                self.unify_expr(callee, callee.ty)?;
                match self.tyctx.resolve_ty(callee.ty) {
                    Ty::Struct(_, name, _) => match self.tyctx.get_method(callee.ty, method_name.symbol) {
                        Some(ty) => {
                            let method_ty = self.tyctx.resolve_ty(ty);
                            self.unify_fn_call(expr, Some(callee), args, &method_ty, method_name.span)?;
                        }
                        None => match self.tyctx.get_field(callee.ty, method_name.symbol) {
                            Some(ty) => {
                                let method_ty = self.tyctx.resolve_ty(ty);
                                self.unify_fn_call(expr, None, args, &method_ty, method_name.span)?;
                            }
                            None => {
                                return self.handler.mk_err(
                                    method_name.span,
                                    &format!("Method or Field `{}` not found on type `{}`", method_name.symbol, name),
                                )
                            }
                        },
                    },
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
                                let method_ty = self.tyctx.resolve_ty(*ty);
                                self.unify_fn_call(expr, None, args, &method_ty, method_name.span)?;
                            }
                            None => {
                                return self.handler.mk_err(
                                    method_name.span,
                                    &format!("Method or Field `{}` not found on tuple", method_name.symbol),
                                )
                            }
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
                self.tyctx.unify(expected, self.tyctx.unit(), expr.span)?;
                self.unify_expr(lhs, lhs.ty)?;
                self.unify_expr(rhs, lhs.ty)?;
            }
            ExprKind::Return(e) => {
                let ret_ty = self.enclosing_fn_ret_ty.unwrap();
                if let Some(e) = e {
                    self.unify_expr(e, ret_ty)?;
                } else {
                    self.tyctx.unify(ret_ty, self.tyctx.unit(), expr.span)?;
                }
            }
            ExprKind::Continue => {}
            ExprKind::Break(e) => {
                let loop_ty = self.enclosing_loop_ty.unwrap();
                if let Some(e) = e {
                    self.unify_expr(e, loop_ty)?;
                } else {
                    self.tyctx.unify(loop_ty, self.tyctx.unit(), expr.span)?;
                }
            }
            ExprKind::Loop(body) => {
                self.tyctx.unify(self.tyctx.unit(), body.ty, body.span)?;
                self.enter_loop_scope(expected, |this| this.unify_block(body))?;
            }
            ExprKind::Array(values) => {
                let resolved = self.tyctx.resolve_ty(expected);

                let t = match resolved {
                    Ty::Array(t) => t,
                    Ty::Infer(v) => {
                        let t = self.tyctx.new_type_var();
                        self.tyctx.unify_value(v, Ty::Array(t));
                        t
                    }
                    _ => {
                        return self.handler.mk_err(
                            expr.span,
                            &format!("Type error: Expected `{}`, Actual: Array", resolved),
                        );
                    }
                };
                for v in values {
                    self.unify_expr(v, t)?;
                }
            }
            ExprKind::ArrayRepeat(e, times) => {
                let resolved = self.tyctx.resolve_ty(expected);

                let t = match resolved {
                    Ty::Array(t) => t,
                    Ty::Infer(v) => {
                        let t = self.tyctx.new_type_var();
                        self.tyctx.unify_value(v, Ty::Array(t));
                        t
                    }
                    _ => {
                        return self.handler.mk_err(
                            expr.span,
                            &format!("Type error: Expected `{}`, Actual: Array", resolved),
                        );
                    }
                };

                self.unify_expr(e, t)?;
                self.unify_expr(times, self.tyctx.int())?;
            }
            ExprKind::ArrayAccess(receiver, index) => {
                self.unify_expr(receiver, receiver.ty)?;
                let receiver_ty = self.tyctx.resolve_ty(receiver.ty);

                let t = match receiver_ty {
                    Ty::Array(t) => t,
                    Ty::Infer(_) => {
                        return self
                            .handler
                            .mk_err(receiver.span, "Type cannot be inferred. Please add type annotations");
                    }
                    _ => {
                        return self.handler.mk_err(
                            receiver.span,
                            &format!("Type error: Expected Array, Actual: `{}`", receiver_ty),
                        );
                    }
                };
                self.unify_expr(index, self.tyctx.int())?;
                self.tyctx.unify(expected, t, expr.span)?;
            }
        }
        Ok(())
    }

    fn unify_block(&mut self, block: &Block) -> Result<()> {
        self.unify_impls(&block.impls)?;
        self.unify_fn_bodies(&block.functions)?;

        match block.stmts.last() {
            Some(Stmt::Expr(e, semi)) if !*semi || e.is_flow_control() => {
                self.tyctx.unify(block.ty, e.ty, e.span)?;
            }
            _ => self.tyctx.unify(block.ty, self.tyctx.unit(), block.span)?,
        }

        self.unify_stmts(&block.stmts)?;
        Ok(())
    }

    fn unify_impls(&mut self, impls: &[Impl]) -> Result<()> {
        for i in impls {
            self.unify_impl(i)?;
        }
        Ok(())
    }

    fn unify_impl(&mut self, i: &Impl) -> Result<()> {
        self.unify_fns(&i.functions)?;
        Ok(())
    }

    fn unify_fns(&mut self, items: &[Function]) -> Result<()> {
        self.unify_fn_bodies(items)?;
        Ok(())
    }

    fn unify_fn_bodies(&mut self, items: &[Function]) -> Result<()> {
        for item in items {
            self.enter_fn_scope(item.ret, |this| this.unify_fn_body(item))?;
        }
        Ok(())
    }

    fn unify_fn_body(&mut self, function: &Function) -> Result<()> {
        self.tyctx.unify(function.ret, function.body.ty, function.body.span)?;
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
            Ty::Fn(params, ret, _) => {
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
                        self.tyctx.unify(*first, self_param.ty, self_param.span)?;
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
                    self.unify_expr(arg, *param)?;
                }
                self.tyctx.unify(*ret, expr.ty, expr.span)?;
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
