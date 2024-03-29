use std::{collections::HashMap, rc::Rc};

use self::{
    hir::*,
    ty::{Ty, TyContext, TypeVar},
};
use crate::{
    err::{ErrHandler, Result},
    lex::Span,
    parse::ast,
};

mod annotate;
mod hir;
mod ty;
mod unification;

pub struct Typeck {
    env: TyContext,
    handler: Rc<ErrHandler>,
    resolved_types: HashMap<TypeVar, Ty>,
}

impl Typeck {
    pub fn new(handler: &Rc<ErrHandler>) -> Self {
        Self {
            env: TyContext::new(handler),
            handler: handler.clone(),
            resolved_types: HashMap::new(),
        }
    }

    pub fn typeck(&mut self, ast: &ast::Ast) -> Result<Ast> {
        let ast = self::annotate::annotate(ast, &mut self.env, &self.handler)?;
        log::debug!("{:#?}", &ast);

        self::unification::unify(&ast, &mut self.env, &self.handler)?;
        log::info!("hey there");

        self.typeck_structs(&ast.structs)?;
        self.typeck_impls(&ast.impls)?;
        self.typeck_fns(&ast.functions)?;
        self.typeck_stmts(&ast.stmts)?;

        Ok(ast)
    }

    fn typeck_stmts(&mut self, stmts: &[Stmt]) -> Result<()> {
        for stmt in stmts {
            self.typeck_stmt(stmt)?;
        }
        Ok(())
    }

    fn typeck_stmt(&mut self, stmt: &Stmt) -> Result<()> {
        match stmt {
            Stmt::Expr(expr, _) => self.typeck_expr(expr),
            Stmt::Let { name, ty, init } => {
                self.typeck_no_var(*ty, name.span)?;
                if let Some(init) = init {
                    self.typeck_expr(init)?;
                    self.typeck_eq(*ty, init.ty, init.span)?;
                }
                Ok(())
            }
        }
    }

    fn typeck_expr(&mut self, expr: &Expr) -> Result<()> {
        self.typeck_no_var(expr.ty, expr.span)?;
        match &expr.kind {
            ExprKind::Binary { op, lhs, rhs } => {
                self.typeck_eq(lhs.ty, rhs.ty, rhs.span)?;

                use ast::BinOp::*;
                match op.val {
                    Add | Sub | Mul | Div | Rem | Lt | Gt | Le | Ge => match self.env.resolve_ty(lhs.ty) {
                        Ty::Int | Ty::Float => {}
                        ty => return self.handler.mk_err(op.span, &format!("Not supported for `{}`", ty)),
                    },

                    Ne | Eq => match self.env.resolve_ty(lhs.ty) {
                        Ty::Int | Ty::Float | Ty::Bool => {}
                        ty => return self.handler.mk_err(op.span, &format!("Not supported for `{}`", ty)),
                    },
                    And | Or => match self.env.resolve_ty(lhs.ty) {
                        Ty::Bool => {}
                        ty => return self.handler.mk_err(op.span, &format!("Not supported for `{}`", ty)),
                    },
                }
            }
            ExprKind::Literal(..) => {}
            ExprKind::Tuple(exprs) => {
                for e in exprs {
                    self.typeck_no_var(e.ty, e.span)?;
                }
            }
            ExprKind::Unary { op, expr } => match op.val {
                ast::UnOp::Not => match self.env.resolve_ty(expr.ty) {
                    Ty::Bool => {}
                    ty => return self.handler.mk_err(op.span, &format!("Not supported for `{}`", ty)),
                },
                ast::UnOp::Neg => match self.env.resolve_ty(expr.ty) {
                    Ty::Int | Ty::Float => {}
                    ty => return self.handler.mk_err(op.span, &format!("Not supported for `{}`", ty)),
                },
            },
            ExprKind::Variable(_, _) => {}
            ExprKind::Block(block) => self.typeck_block(block)?,
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
            }
            ExprKind::Closure { params, ret, body } => {
                for p in params {
                    self.typeck_no_var(p.param_ty, p.name.span)?;
                }
                self.typeck_expr(body)?;
                self.typeck_eq(*ret, body.ty, body.span)?;
            }
            ExprKind::Call { callee, args } | ExprKind::MethodCall { callee, args, .. } => {
                self.typeck_expr(callee)?;
                for arg in args {
                    self.typeck_expr(arg)?;
                }
            }
            ExprKind::Struct(_, fields, _) => {
                for f in fields {
                    self.typeck_expr(&f.expr)?;
                }
            }
            ExprKind::Field(expr, _) => {
                self.typeck_expr(expr)?;
            }
            ExprKind::AssocMethod { ty, .. } => {
                self.typeck_no_var(*ty, expr.span)?;
            }
            ExprKind::Assign { lhs, rhs } => {
                self.typeck_expr(lhs)?;
                self.typeck_expr(rhs)?;
                self.typeck_eq(lhs.ty, rhs.ty, rhs.span)?;
            }
            ExprKind::Return(e) | ExprKind::Break(e) => {
                if let Some(e) = e {
                    self.typeck_expr(e)?;
                }
            }
            ExprKind::Continue => {}
            ExprKind::Loop(body) => self.typeck_block(body)?,
            ExprKind::Array(values) => {
                for v in values {
                    self.typeck_expr(v)?;
                }
            }
            ExprKind::ArrayRepeat(e, times) => {
                self.typeck_expr(e)?;
                self.typeck_expr(times)?;
            }
            ExprKind::ArrayAccess(receiver, index) => {
                self.typeck_expr(receiver)?;
                self.typeck_expr(index)?;
            }
        }
        Ok(())
    }

    fn typeck_block(&mut self, block: &Block) -> Result<()> {
        self.typeck_structs(&block.structs)?;
        self.typeck_fns(&block.functions)?;
        self.typeck_stmts(&block.stmts)?;

        if let Some(Stmt::Expr(expr, false)) = block.stmts.last() {
            self.typeck_eq(expr.ty, block.ty, expr.span)?;
        }

        Ok(())
    }

    fn typeck_structs(&mut self, structs: &[Struct]) -> Result<()> {
        for s in structs {
            self.typeck_struct(s)?;
        }
        Ok(())
    }

    fn typeck_struct(&mut self, s: &Struct) -> Result<()> {
        for f in &s.fields {
            self.typeck_no_var(f.ty, f.name.span)?;
        }
        self.typeck_no_var(s.ty, s.name.span)?;
        Ok(())
    }

    fn typeck_impls(&mut self, impls: &[Impl]) -> Result<()> {
        for i in impls {
            self.typeck_impl(i)?;
        }
        Ok(())
    }

    fn typeck_impl(&mut self, i: &Impl) -> Result<()> {
        self.typeck_fns(&i.functions)?;
        Ok(())
    }

    fn typeck_fns(&mut self, func: &[Function]) -> Result<()> {
        for f in func {
            self.typeck_fn(f)?;
        }
        Ok(())
    }

    fn typeck_fn(&mut self, func: &Function) -> Result<()> {
        for p in &func.params {
            self.typeck_no_var(p.param_ty, p.name.span)?;
        }
        self.typeck_eq(func.ret, func.body.ty, func.body.span)?;
        self.typeck_block(&func.body)
    }

    fn typeck_eq(&mut self, a: TypeVar, b: TypeVar, span: Span) -> Result<()> {
        self.typeck_no_var(a, span)?;
        self.typeck_no_var(b, span)?;

        let a = self.env.resolve_ty(a);
        let b = self.env.resolve_ty(b);

        match (&a, &b) {
            (a, b) if a == b => {}
            (Ty::Struct(id, ..), Ty::Struct(id2, ..)) => {
                if id != id2 {
                    return self
                        .handler
                        .mk_err(span, &format!("Type mismatch: Expected: `{}`, Actual: `{}`", a, b));
                }
            }
            (Ty::Fn(args, ret, _), Ty::Fn(arg2, ret2, _)) => {
                for (&a, &b) in args.iter().zip(arg2.iter()) {
                    self.typeck_eq(a, b, span)?;
                }
                self.typeck_eq(*ret, *ret2, span)?;
            }
            (Ty::Tuple(tys), Ty::Tuple(tys2)) => {
                for (&a, &b) in tys.iter().zip(tys2.iter()) {
                    self.typeck_eq(a, b, span)?;
                }
            }
            (a, b) => {
                return self
                    .handler
                    .mk_err(span, &format!("Type mismatch: Expected: `{}`, Actual: `{}`", a, b));
            }
        }
        Ok(())
    }

    fn typeck_no_var(&mut self, var: TypeVar, span: Span) -> Result<()> {
        if self.resolved_types.contains_key(&var) {
            return Ok(());
        }

        let ty = self.env.resolve_ty(var);
        log::trace!("{:?} = {:?}", var, ty);
        self.resolved_types.insert(var, ty.clone());
        match ty {
            Ty::Infer(_) => self
                .handler
                .mk_err(span, "Type cannot be inferred. Please add type annotations"),
            Ty::Generic(..) => Ok(()),
            Ty::Unit | Ty::Bool | Ty::Int | Ty::Float | Ty::Str => Ok(()),
            Ty::Fn(args, ret, _) => {
                for arg in args.iter() {
                    self.typeck_no_var(*arg, span)?;
                }
                self.typeck_no_var(ret, span)
            }
            Ty::Struct(..) => {
                if let Some(fields) = self.env.get_fields(var) {
                    for (_, ty) in fields.iter() {
                        self.typeck_no_var(ty, span)?;
                    }
                }
                Ok(())
            }
            Ty::Tuple(tys) => {
                for ty in tys.iter() {
                    self.typeck_no_var(*ty, span)?;
                }
                Ok(())
            }
            Ty::Array(t) => self.typeck_no_var(t, span),
        }
    }
}
