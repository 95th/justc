use std::rc::Rc;

use crate::{
    err::{Handler, Result},
    lex::Token,
    parse::ast,
    symbol::SymbolTable,
};

use super::{
    hir::{self, SpannedTy},
    ty::{Ty, TyContext, TypeVar},
};

pub fn annotate(ast: ast::Ast, env: &mut TyContext, handler: &Handler) -> Result<hir::Ast> {
    let bindings = &mut SymbolTable::new();
    let functions = &mut SymbolTable::new();
    let structs = &mut SymbolTable::new();
    Annotate::new(env, bindings, functions, structs, handler).annotate_ast(ast)
}

struct Annotate<'a> {
    env: &'a mut TyContext,
    bindings: &'a mut SymbolTable<TypeVar>,
    functions: &'a mut SymbolTable<TypeVar>,
    structs: &'a mut SymbolTable<TypeVar>,
    handler: &'a Handler,
    has_enclosing_fn: bool,
    has_enclosing_loop: bool,
}

impl<'a> Annotate<'a> {
    fn new(
        env: &'a mut TyContext,
        bindings: &'a mut SymbolTable<TypeVar>,
        functions: &'a mut SymbolTable<TypeVar>,
        structs: &'a mut SymbolTable<TypeVar>,
        handler: &'a Handler,
    ) -> Self {
        Self {
            env,
            bindings,
            functions,
            structs,
            handler,
            has_enclosing_fn: false,
            has_enclosing_loop: false,
        }
    }

    fn annotate_ast(&mut self, ast: ast::Ast) -> Result<hir::Ast> {
        let structs = self.annotate_structs(ast.structs)?;
        let impls = self.annotate_impls(ast.impls)?;
        let functions = self.annotate_fns(ast.functions)?;
        let stmts = self.annotate_stmts(ast.stmts)?;
        Ok(hir::Ast {
            structs,
            impls,
            functions,
            stmts,
        })
    }

    fn annotate_stmts(&mut self, stmts: Vec<ast::Stmt>) -> Result<Vec<hir::Stmt>> {
        stmts.into_iter().map(|s| self.annotate_stmt(s)).collect()
    }

    fn annotate_stmt(&mut self, stmt: ast::Stmt) -> Result<hir::Stmt> {
        match stmt {
            ast::Stmt::Expr(expr, semicolon) => {
                Ok(hir::Stmt::Expr(self.annotate_expr(expr)?, semicolon))
            }
            ast::Stmt::Let { name, init, ty } => {
                let init = match init {
                    Some(e) => Some(self.annotate_expr(e)?),
                    None => None,
                };

                let let_ty = self.ast_ty_to_ty(ty)?;
                self.bindings.insert(name.symbol, let_ty);

                Ok(hir::Stmt::Let {
                    name,
                    ty: let_ty,
                    init,
                })
            }
            ast::Stmt::Assign { lhs, rhs } => Ok(hir::Stmt::Assign {
                lhs: self.annotate_expr(lhs)?,
                rhs: self.annotate_expr(rhs)?,
            }),
            ast::Stmt::OpAssign { lhs, rhs, op } => {
                let lhs = self.annotate_expr(lhs)?;
                let rhs = self.annotate_expr(rhs)?;
                let rhs = Box::new(hir::Expr {
                    span: lhs.span.to(rhs.span),
                    kind: hir::ExprKind::Binary {
                        left: lhs.clone(),
                        right: rhs,
                        op,
                    },
                    ty: self.env.new_type_var(),
                });
                Ok(hir::Stmt::Assign { lhs, rhs })
            }
            ast::Stmt::While { cond, body } => {
                let cond = self.annotate_expr(cond)?;
                let body = self.enter_loop_scope(|this| this.annotate_block(body))?;
                Ok(hir::Stmt::While { cond, body })
            }
            ast::Stmt::Return(span, Some(e)) => {
                if self.has_enclosing_fn {
                    Ok(hir::Stmt::Return(span, Some(self.annotate_expr(e)?)))
                } else {
                    self.handler
                        .mk_err(span, "Cannot return without enclosing function")
                }
            }
            ast::Stmt::Return(span, None) => {
                if self.has_enclosing_fn {
                    Ok(hir::Stmt::Return(span, None))
                } else {
                    self.handler
                        .mk_err(span, "Cannot return without enclosing function")
                }
            }
            ast::Stmt::Continue(span) => {
                if self.has_enclosing_loop {
                    Ok(hir::Stmt::Continue(span))
                } else {
                    self.handler
                        .mk_err(span, "Cannot continue without an enclosing loop")
                }
            }
            ast::Stmt::Break(span) => {
                if self.has_enclosing_loop {
                    Ok(hir::Stmt::Break(span))
                } else {
                    self.handler
                        .mk_err(span, "Cannot break without an enclosing loop")
                }
            }
        }
    }

    fn annotate_expr(&mut self, expr: Box<ast::Expr>) -> Result<Box<hir::Expr>> {
        let ty = self.env.new_type_var();
        let (kind, span) = (expr.kind, expr.span);
        let kind = match kind {
            ast::ExprKind::Binary { op, left, right } => hir::ExprKind::Binary {
                op,
                left: self.annotate_expr(left)?,
                right: self.annotate_expr(right)?,
            },
            ast::ExprKind::Grouping(e) => return self.annotate_expr(e),
            ast::ExprKind::Literal(lit, span) => {
                let ty = match &lit {
                    ast::Lit::Str(_) => self.env.str(),
                    ast::Lit::Integer(_) => self.env.int(),
                    ast::Lit::Float(_) => self.env.float(),
                    ast::Lit::Bool(_) => self.env.bool(),
                    ast::Lit::Err => self.env.new_type_var(),
                };
                hir::ExprKind::Literal(lit, ty, span)
            }
            ast::ExprKind::Unary { op, expr } => hir::ExprKind::Unary {
                op,
                expr: self.annotate_expr(expr)?,
            },
            ast::ExprKind::Variable(t) => match self
                .bindings
                .get(t.symbol)
                .or_else(|| self.functions.get(t.symbol))
            {
                Some(ty) => hir::ExprKind::Variable(t, *ty),
                None => return self.handler.mk_err(t.span, "Not found in this scope"),
            },
            ast::ExprKind::Block(block) => hir::ExprKind::Block(self.annotate_block(block)?),
            ast::ExprKind::If {
                cond,
                then_clause,
                else_clause,
            } => hir::ExprKind::If {
                cond: self.annotate_expr(cond)?,
                then_clause: self.annotate_block(then_clause)?,
                else_clause: match else_clause {
                    Some(e) => Some(self.annotate_expr(e)?),
                    None => None,
                },
            },
            ast::ExprKind::Closure { params, ret, body } => self.enter_block_scope(|this| {
                let params = this.annotate_params(params)?;
                let ret = this.ast_ty_to_ty(ret)?;
                this.has_enclosing_fn = true;
                let body = this.annotate_expr(body)?;
                this.has_enclosing_fn = false;
                Ok(hir::ExprKind::Closure { params, ret, body })
            })?,
            ast::ExprKind::Call { callee, args } => hir::ExprKind::Call {
                callee: self.annotate_expr(callee)?,
                args: args
                    .into_iter()
                    .map(|arg| self.annotate_expr(arg))
                    .collect::<Result<Vec<_>>>()?,
            },
            ast::ExprKind::Struct(name, fields) => {
                let ty = if name.is_self_ty() {
                    self.env.new_type_var()
                } else {
                    match self.structs.get(name.symbol) {
                        Some(ty) => *ty,
                        None => {
                            return self.handler.mk_err(name.span, "Not found in this scope");
                        }
                    }
                };
                hir::ExprKind::Struct(name, self.annotate_fields(fields)?, ty)
            }
            ast::ExprKind::Field(expr, name) => {
                hir::ExprKind::Field(self.annotate_expr(expr)?, name)
            }
            ast::ExprKind::MethodCall { callee, name, args } => {
                let callee = self.annotate_expr(callee)?;
                let ty = SpannedTy {
                    ty: callee.ty,
                    span: callee.span,
                    is_self: false,
                };
                let mut annotated_args = vec![callee];
                for arg in args {
                    annotated_args.push(self.annotate_expr(arg)?);
                }
                hir::ExprKind::Call {
                    callee: Box::new(hir::Expr {
                        span: name.span,
                        kind: hir::ExprKind::AssocMethod { ty, name },
                        ty: self.env.new_type_var(),
                    }),
                    args: annotated_args,
                }
            }
            ast::ExprKind::AssocMethod { ty, name } => {
                let ty = self.ast_ty_to_spanned_ty(ty)?;
                hir::ExprKind::AssocMethod { ty, name }
            }
        };
        Ok(Box::new(hir::Expr { kind, span, ty }))
    }

    fn annotate_block(&mut self, block: ast::Block) -> Result<hir::Block> {
        self.enter_block_scope(|this| {
            let structs = this.annotate_structs(block.structs)?;
            let impls = this.annotate_impls(block.impls)?;
            let functions = this.annotate_fns(block.functions)?;
            let stmts = this.annotate_stmts(block.stmts)?;
            Ok(hir::Block {
                stmts,
                impls,
                functions,
                structs,
                ty: this.env.new_type_var(),
                span: block.span,
            })
        })
    }

    fn annotate_fns(&mut self, functions: Vec<ast::Function>) -> Result<Vec<hir::Function>> {
        for func in &functions {
            self.functions
                .insert(func.name.symbol, self.env.new_type_var());
        }
        functions
            .into_iter()
            .map(|func| self.annotate_fn(func))
            .collect::<Result<Vec<_>>>()
    }

    fn annotate_fn(&mut self, func: ast::Function) -> Result<hir::Function> {
        self.enter_fn_scope(|this| {
            let ty = *this.functions.get(func.name.symbol).unwrap();
            let params = this.annotate_params(func.params)?;
            let ret = this.ast_ty_to_spanned_ty(func.ret)?;
            this.has_enclosing_fn = true;
            let body = this.annotate_block(func.body)?;
            this.has_enclosing_fn = false;
            Ok(hir::Function {
                name: func.name,
                params,
                ret,
                body,
                ty,
            })
        })
    }

    fn annotate_params(&mut self, params: Vec<ast::Param>) -> Result<Vec<hir::Param>> {
        params
            .into_iter()
            .map(|p| {
                let param_ty = self.ast_ty_to_spanned_ty(p.ty)?;
                self.bindings.insert(p.name.symbol, param_ty.ty);
                Ok(hir::Param {
                    name: p.name,
                    param_ty,
                })
            })
            .collect()
    }

    fn ast_ty_to_ty(&mut self, ty: ast::Ty) -> Result<TypeVar> {
        let ty = match ty.kind {
            ast::TyKind::Fn(params, ret) => {
                let params = params
                    .into_iter()
                    .map(|p| self.ast_ty_to_ty(p))
                    .collect::<Result<_>>()?;
                let ret = self.ast_ty_to_ty(*ret)?;
                self.env.alloc_ty(Ty::Fn(Rc::new(params), ret))
            }
            ast::TyKind::Ident(t) => self.token_to_ty(&t)?,
            ast::TyKind::Infer => self.env.new_type_var(),
            ast::TyKind::Unit => self.env.unit(),
            ast::TyKind::SelfTy => self.env.new_type_var(),
        };

        Ok(ty)
    }

    fn ast_ty_to_spanned_ty(&mut self, ast_ty: ast::Ty) -> Result<hir::SpannedTy> {
        let mut is_self = false;
        let ty = match ast_ty.kind {
            ast::TyKind::Fn(params, ret) => {
                let params = params
                    .into_iter()
                    .map(|p| self.ast_ty_to_ty(p))
                    .collect::<Result<_>>()?;
                let ret = self.ast_ty_to_ty(*ret)?;
                self.env.alloc_ty(Ty::Fn(Rc::new(params), ret))
            }
            ast::TyKind::Ident(t) => self.token_to_ty(&t)?,
            ast::TyKind::Infer => self.env.new_type_var(),
            ast::TyKind::Unit => self.env.unit(),
            ast::TyKind::SelfTy => {
                is_self = true;
                self.env.new_type_var()
            }
        };
        Ok(hir::SpannedTy {
            is_self,
            span: ast_ty.span,
            ty,
        })
    }

    fn annotate_impls(&mut self, impls: Vec<ast::Impl>) -> Result<Vec<hir::Impl>> {
        impls.into_iter().map(|i| self.annotate_impl(i)).collect()
    }

    fn annotate_impl(&mut self, i: ast::Impl) -> Result<hir::Impl> {
        let ty = match self.structs.get(i.name.symbol) {
            Some(ty) => *ty,
            None => {
                return self.handler.mk_err(i.name.span, "Not found in this scope");
            }
        };
        let functions = self.annotate_fns(i.functions)?;
        Ok(hir::Impl { ty, functions })
    }

    fn annotate_structs(&mut self, structs: Vec<ast::Struct>) -> Result<Vec<hir::Struct>> {
        for s in &structs {
            self.structs.insert(s.name.symbol, self.env.new_type_var());
        }

        structs
            .into_iter()
            .map(|s| self.annotate_struct(s))
            .collect()
    }

    fn annotate_struct(&mut self, s: ast::Struct) -> Result<hir::Struct> {
        let ty = *self.structs.get(s.name.symbol).unwrap();
        let fields = self.annotate_struct_fields(s.fields)?;
        Ok(hir::Struct {
            name: s.name,
            fields,
            id: ty,
            ty,
        })
    }

    fn annotate_struct_fields(
        &mut self,
        fields: Vec<ast::StructField>,
    ) -> Result<Vec<hir::StructField>> {
        fields
            .into_iter()
            .map(|f| self.annotate_struct_field(f))
            .collect()
    }

    fn annotate_struct_field(&mut self, field: ast::StructField) -> Result<hir::StructField> {
        Ok(hir::StructField {
            name: field.name,
            ty: self.ast_ty_to_ty(field.ty)?,
        })
    }

    fn annotate_fields(&mut self, fields: Vec<ast::Field>) -> Result<Vec<hir::Field>> {
        fields.into_iter().map(|f| self.annotate_field(f)).collect()
    }

    fn annotate_field(&mut self, field: ast::Field) -> Result<hir::Field> {
        Ok(hir::Field {
            name: field.name,
            expr: self.annotate_expr(field.expr)?,
        })
    }

    fn token_to_ty(&mut self, token: &Token) -> Result<TypeVar> {
        token.symbol.as_str_with(|s| {
            let ty = match s {
                "bool" => self.env.bool(),
                "int" => self.env.int(),
                "str" => self.env.str(),
                "float" => self.env.float(),
                _ => {
                    if let Some(ty) = self.structs.get(token.symbol) {
                        *ty
                    } else {
                        return self.handler.mk_err(token.span, "Unknown type");
                    }
                }
            };
            Ok(ty)
        })
    }

    fn enter_block_scope<F, R>(&mut self, f: F) -> R
    where
        F: FnOnce(&mut Annotate<'_>) -> R,
    {
        let Annotate {
            env,
            functions,
            bindings,
            structs,
            handler,
            has_enclosing_fn,
            has_enclosing_loop,
        } = self;

        structs.enter_scope(|structs| {
            functions.enter_scope(|functions| {
                bindings.enter_scope(|bindings| {
                    let mut this = Annotate::new(env, bindings, functions, structs, handler);
                    this.has_enclosing_fn = *has_enclosing_fn;
                    this.has_enclosing_loop = *has_enclosing_loop;
                    f(&mut this)
                })
            })
        })
    }

    fn enter_loop_scope<F, R>(&mut self, f: F) -> R
    where
        F: FnOnce(&mut Annotate<'_>) -> R,
    {
        let has_enclosing_loop = self.has_enclosing_loop;
        self.has_enclosing_loop = true;
        let result = f(self);
        self.has_enclosing_loop = has_enclosing_loop;
        result
    }

    fn enter_fn_scope<F, R>(&mut self, f: F) -> R
    where
        F: FnOnce(&mut Annotate<'_>) -> R,
    {
        let has_enclosing_fn = self.has_enclosing_fn;
        let has_enclosing_loop = self.has_enclosing_loop;

        let bindings = std::mem::take(self.bindings);
        self.has_enclosing_fn = true;
        self.has_enclosing_loop = false;

        let result = self.enter_block_scope(|this| f(this));

        self.has_enclosing_loop = has_enclosing_loop;
        self.has_enclosing_fn = has_enclosing_fn;
        *self.bindings = bindings;

        result
    }
}
