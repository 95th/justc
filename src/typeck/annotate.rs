use std::collections::HashMap;

use crate::{
    err::{Handler, Result},
    lex::Token,
    parse::ast,
    symbol::SymbolTable,
};

use super::{
    hir,
    ty::{Ty, TyContext},
};

pub fn annotate(ast: ast::Ast, env: &mut TyContext, handler: &Handler) -> Result<hir::Ast> {
    let bindings = &mut SymbolTable::new();
    let functions = &mut SymbolTable::new();
    let structs = &mut SymbolTable::new();
    Annotate::new(env, bindings, functions, structs, handler).annotate_ast(ast)
}

struct Annotate<'a> {
    env: &'a mut TyContext,
    bindings: &'a mut SymbolTable<Ty>,
    functions: &'a mut SymbolTable<Ty>,
    structs: &'a mut SymbolTable<Ty>,
    handler: &'a Handler,
    has_enclosing_fn: bool,
    has_enclosing_loop: bool,
}

impl<'a> Annotate<'a> {
    fn new(
        env: &'a mut TyContext,
        bindings: &'a mut SymbolTable<Ty>,
        functions: &'a mut SymbolTable<Ty>,
        structs: &'a mut SymbolTable<Ty>,
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
        let mut structs = self.annotate_structs(ast.structs)?;
        self.annotate_impls(ast.impls, &mut structs)?;
        Ok(hir::Ast {
            structs,
            functions: self.annotate_fns(ast.functions)?,
            stmts: self.annotate_stmts(ast.stmts)?,
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
                self.bindings.insert(name.symbol, let_ty.clone());

                Ok(hir::Stmt::Let {
                    name,
                    ty: let_ty,
                    init,
                })
            }
            ast::Stmt::Assign { name, val } => Ok(hir::Stmt::Assign {
                name: self.annotate_expr(name)?,
                val: self.annotate_expr(val)?,
            }),
            ast::Stmt::While { cond, body } => {
                let cond = self.annotate_expr(cond)?;
                self.has_enclosing_loop = true;
                let body = self.annotate_block(body)?;
                self.has_enclosing_loop = false;
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
                    ast::Lit::Str(_) => Ty::Str,
                    ast::Lit::Integer(_) => Ty::Int,
                    ast::Lit::Float(_) => Ty::Float,
                    ast::Lit::Bool(_) => Ty::Bool,
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
                Some(ty) => hir::ExprKind::Variable(t, ty.clone()),
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
            ast::ExprKind::Closure { params, ret, body } => self.enter_scope(|this| {
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
                        Some(ty) => ty.clone(),
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
            ast::ExprKind::MethodCall { callee, name, args } => hir::ExprKind::MethodCall {
                callee: self.annotate_expr(callee)?,
                name,
                args: args
                    .into_iter()
                    .map(|arg| self.annotate_expr(arg))
                    .collect::<Result<Vec<_>>>()?,
            },
        };
        Ok(Box::new(hir::Expr { kind, span, ty }))
    }

    fn annotate_block(&mut self, block: ast::Block) -> Result<hir::Block> {
        self.enter_scope(|this| {
            let mut structs = this.annotate_structs(block.structs)?;
            this.annotate_impls(block.impls, &mut structs)?;
            let functions = this.annotate_fns(block.functions)?;
            let stmts = this.annotate_stmts(block.stmts)?;
            Ok(hir::Block {
                stmts,
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
        let env = &mut *self.env;
        let structs = &mut *self.structs;
        let handler = self.handler;
        self.functions.enter_scope(|functions| {
            structs.enter_scope(|structs| {
                let bindings = &mut SymbolTable::new();
                let mut this = Annotate::new(env, bindings, functions, structs, handler);

                let ty = this.functions.get(func.name.symbol).unwrap().clone();
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
        })
    }

    fn annotate_params(&mut self, params: Vec<ast::Param>) -> Result<Vec<hir::Param>> {
        params
            .into_iter()
            .map(|p| {
                let param_ty = self.ast_ty_to_spanned_ty(p.ty)?;
                self.bindings.insert(p.name.symbol, param_ty.ty.clone());
                Ok(hir::Param {
                    name: p.name,
                    param_ty: param_ty,
                })
            })
            .collect()
    }

    fn enter_scope<F, R>(&mut self, f: F) -> R
    where
        F: FnOnce(&mut Annotate<'_>) -> R,
    {
        let env = &mut *self.env;
        let functions = &mut *self.functions;
        let structs = &mut *self.structs;
        let handler = self.handler;
        let has_enclosing_fn = self.has_enclosing_fn;
        let has_enclosing_loop = self.has_enclosing_loop;

        self.bindings.enter_scope(|bindings| {
            functions.enter_scope(|functions| {
                structs.enter_scope(|structs| {
                    let mut this = Annotate::new(env, bindings, functions, structs, handler);
                    this.has_enclosing_fn = has_enclosing_fn;
                    this.has_enclosing_loop = has_enclosing_loop;
                    f(&mut this)
                })
            })
        })
    }

    fn ast_ty_to_ty(&mut self, ty: ast::Ty) -> Result<Ty> {
        let ty = match ty.kind {
            ast::TyKind::Fn(params, ret) => {
                let params = params
                    .into_iter()
                    .map(|p| self.ast_ty_to_ty(p))
                    .collect::<Result<_>>()?;
                let ret = self.ast_ty_to_ty(*ret)?;
                Ty::Fn(params, Box::new(ret))
            }
            ast::TyKind::Ident(t) => self.token_to_ty(&t)?,
            ast::TyKind::Infer => self.env.new_type_var(),
            ast::TyKind::Unit => Ty::Unit,
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
                Ty::Fn(params, Box::new(ret))
            }
            ast::TyKind::Ident(t) => self.token_to_ty(&t)?,
            ast::TyKind::Infer => self.env.new_type_var(),
            ast::TyKind::Unit => Ty::Unit,
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

    fn annotate_impls(
        &mut self,
        mut impls: Vec<ast::Impl>,
        structs: &mut [hir::Struct],
    ) -> Result<()> {
        let mut map = HashMap::new();
        for i in &mut impls {
            map.entry(i.name.symbol)
                .or_insert_with(|| vec![])
                .append(&mut i.functions);
        }

        for s in structs {
            if let Some(methods) = map.remove(&s.name.symbol) {
                let methods = self.annotate_fns(methods)?;
                s.methods = methods;
            }
        }

        Ok(())
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
        let ty = self.structs.get(s.name.symbol).unwrap().clone();
        let fields = self.annotate_struct_fields(s.fields)?;
        Ok(hir::Struct {
            name: s.name,
            fields,
            id: ty.type_var_id().unwrap_or_default(),
            ty,
            methods: vec![],
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

    fn token_to_ty(&mut self, token: &Token) -> Result<Ty> {
        token.symbol.as_str_with(|s| {
            let ty = match s {
                "bool" => Ty::Bool,
                "int" => Ty::Int,
                "str" => Ty::Str,
                "float" => Ty::Float,
                _ => {
                    if let Some(ty) = self.structs.get(token.symbol) {
                        ty.clone()
                    } else {
                        return self.handler.mk_err(token.span, "Unknown type");
                    }
                }
            };
            Ok(ty)
        })
    }
}
