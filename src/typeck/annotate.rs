use crate::{err::Handler, lex::Token, parse::ast, symbol::SymbolTable};

use super::{
    hir,
    ty::{Ty, TyContext},
};

pub fn annotate(ast: ast::Ast, env: &mut TyContext, handler: &Handler) -> Option<hir::Ast> {
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

    fn annotate_ast(&mut self, ast: ast::Ast) -> Option<hir::Ast> {
        Some(hir::Ast {
            structs: self.annotate_structs(ast.structs)?,
            functions: self.annotate_fns(ast.functions)?,
            stmts: self.annotate_stmts(ast.stmts)?,
        })
    }

    fn annotate_stmts(&mut self, stmts: Vec<ast::Stmt>) -> Option<Vec<hir::Stmt>> {
        stmts.into_iter().map(|s| self.annotate_stmt(s)).collect()
    }

    fn annotate_stmt(&mut self, stmt: ast::Stmt) -> Option<hir::Stmt> {
        match stmt {
            ast::Stmt::Expr(expr, semicolon) => {
                Some(hir::Stmt::Expr(self.annotate_expr(expr)?, semicolon))
            }
            ast::Stmt::Let { name, init, ty } => {
                let init = match init {
                    Some(e) => Some(self.annotate_expr(e)?),
                    None => None,
                };

                let let_ty = self.ast_ty_to_ty(ty)?;
                self.bindings.insert(name.symbol, let_ty.clone());

                Some(hir::Stmt::Let {
                    name,
                    ty: let_ty,
                    init,
                })
            }
            ast::Stmt::Assign { name, val } => Some(hir::Stmt::Assign {
                name: self.annotate_expr(name)?,
                val: self.annotate_expr(val)?,
            }),
            ast::Stmt::While { cond, body } => {
                let cond = self.annotate_expr(cond)?;
                self.has_enclosing_loop = true;
                let body = self.annotate_block(body)?;
                self.has_enclosing_loop = false;
                Some(hir::Stmt::While { cond, body })
            }
            ast::Stmt::Return(span, Some(e)) => {
                if self.has_enclosing_fn {
                    Some(hir::Stmt::Return(span, Some(self.annotate_expr(e)?)))
                } else {
                    self.handler
                        .report(span, "Cannot return without enclosing function");
                    None
                }
            }
            ast::Stmt::Return(span, None) => {
                if self.has_enclosing_fn {
                    Some(hir::Stmt::Return(span, None))
                } else {
                    self.handler
                        .report(span, "Cannot return without enclosing function");
                    None
                }
            }
            ast::Stmt::Continue(span) => {
                if self.has_enclosing_loop {
                    Some(hir::Stmt::Continue(span))
                } else {
                    self.handler
                        .report(span, "Cannot continue without an enclosing loop");
                    None
                }
            }
            ast::Stmt::Break(span) => {
                if self.has_enclosing_loop {
                    Some(hir::Stmt::Break(span))
                } else {
                    self.handler
                        .report(span, "Cannot break without an enclosing loop");
                    None
                }
            }
        }
    }

    fn annotate_expr(&mut self, expr: Box<ast::Expr>) -> Option<Box<hir::Expr>> {
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
                .get(&t.symbol)
                .or_else(|| self.functions.get(&t.symbol))
            {
                Some(ty) => hir::ExprKind::Variable(t, ty.clone()),
                None => {
                    self.handler.report(t.span, "Not found in this scope");
                    return None;
                }
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
                Some(hir::ExprKind::Closure { params, ret, body })
            })?,
            ast::ExprKind::Call { callee, args } => hir::ExprKind::Call {
                callee: self.annotate_expr(callee)?,
                args: args
                    .into_iter()
                    .map(|arg| self.annotate_expr(arg))
                    .collect::<Option<Vec<_>>>()?,
            },
            ast::ExprKind::Struct(name, fields) => {
                let ty = match self.structs.get(&name.symbol) {
                    Some(ty) => ty.clone(),
                    None => {
                        self.handler.report(name.span, "not found in this scope");
                        return None;
                    }
                };
                hir::ExprKind::Struct(name, self.annotate_fields(fields)?, ty)
            }
            ast::ExprKind::Field(expr, name) => {
                hir::ExprKind::Field(self.annotate_expr(expr)?, name)
            }
        };
        Some(Box::new(hir::Expr { kind, span, ty }))
    }

    fn annotate_block(&mut self, block: ast::Block) -> Option<hir::Block> {
        self.enter_scope(|this| {
            let structs = this.annotate_structs(block.structs)?;
            let functions = this.annotate_fns(block.functions)?;
            let stmts = this.annotate_stmts(block.stmts)?;
            Some(hir::Block {
                stmts,
                functions,
                structs,
                ty: this.env.new_type_var(),
                span: block.span,
            })
        })
    }

    fn annotate_fns(&mut self, functions: Vec<ast::Function>) -> Option<Vec<hir::Function>> {
        for func in &functions {
            self.functions
                .insert(func.name.symbol, self.env.new_type_var());
        }
        functions
            .into_iter()
            .map(|func| self.annotate_fn(func))
            .collect::<Option<Vec<_>>>()
    }

    fn annotate_fn(&mut self, func: ast::Function) -> Option<hir::Function> {
        let env = &mut *self.env;
        let structs = &mut *self.structs;
        let handler = self.handler;
        self.functions.enter_scope(|functions| {
            structs.enter_scope(|structs| {
                let bindings = &mut SymbolTable::new();
                let mut this = Annotate::new(env, bindings, functions, structs, handler);

                let ty = this.functions.get(&func.name.symbol).unwrap().clone();
                let params = this.annotate_params(func.params)?;
                let ret = this.ast_ty_to_ty(func.ret)?;
                this.has_enclosing_fn = true;
                let body = this.annotate_block(func.body)?;
                this.has_enclosing_fn = false;
                Some(hir::Function {
                    name: func.name,
                    params,
                    ret,
                    body,
                    ty,
                })
            })
        })
    }

    fn annotate_params(&mut self, params: Vec<ast::Param>) -> Option<Vec<hir::Param>> {
        params
            .into_iter()
            .map(|p| {
                let param_ty = self.ast_ty_to_ty(p.ty)?;
                self.bindings.insert(p.name.symbol, param_ty.clone());
                Some(hir::Param {
                    name: p.name,
                    ty: param_ty,
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

    fn ast_ty_to_ty(&mut self, ty: ast::Ty) -> Option<Ty> {
        let ty = match ty.kind {
            ast::TyKind::Fn(params, ret) => {
                let params = params
                    .into_iter()
                    .map(|p| self.ast_ty_to_ty(p))
                    .collect::<Option<_>>()?;
                let ret = self.ast_ty_to_ty(*ret)?;
                Ty::Fn(params, Box::new(ret))
            }
            ast::TyKind::Ident(t) => self.token_to_ty(&t)?,
            ast::TyKind::Infer => self.env.new_type_var(),
            ast::TyKind::Unit => Ty::Unit,
        };

        Some(ty)
    }

    fn annotate_structs(&mut self, structs: Vec<ast::Struct>) -> Option<Vec<hir::Struct>> {
        for s in &structs {
            self.structs.insert(s.name.symbol, self.env.new_type_var());
        }

        structs
            .into_iter()
            .map(|s| self.annotate_struct(s))
            .collect()
    }

    fn annotate_struct(&mut self, s: ast::Struct) -> Option<hir::Struct> {
        let ty = self.structs.get(&s.name.symbol).unwrap().clone();
        let fields = self.annotate_struct_fields(s.fields)?;
        Some(hir::Struct {
            name: s.name,
            fields,
            id: ty.type_var_id().unwrap_or_default(),
            ty,
        })
    }

    fn annotate_struct_fields(
        &mut self,
        fields: Vec<ast::StructField>,
    ) -> Option<Vec<hir::StructField>> {
        fields
            .into_iter()
            .map(|f| self.annotate_struct_field(f))
            .collect()
    }

    fn annotate_struct_field(&mut self, field: ast::StructField) -> Option<hir::StructField> {
        Some(hir::StructField {
            name: field.name,
            ty: self.ast_ty_to_ty(field.ty)?,
        })
    }

    fn annotate_fields(&mut self, fields: Vec<ast::Field>) -> Option<Vec<hir::Field>> {
        fields.into_iter().map(|f| self.annotate_field(f)).collect()
    }

    fn annotate_field(&mut self, field: ast::Field) -> Option<hir::Field> {
        Some(hir::Field {
            name: field.name,
            expr: self.annotate_expr(field.expr)?,
        })
    }

    fn token_to_ty(&mut self, token: &Token) -> Option<Ty> {
        token.symbol.as_str_with(|s| {
            let ty = match s {
                "bool" => Ty::Bool,
                "int" => Ty::Int,
                "str" => Ty::Str,
                "float" => Ty::Float,
                _ => {
                    if let Some(ty) = self.structs.get(&token.symbol) {
                        ty.clone()
                    } else {
                        self.handler.report(token.span, "Unknown type");
                        return None;
                    }
                }
            };
            Some(ty)
        })
    }
}
