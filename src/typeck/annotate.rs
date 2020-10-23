use crate::{err::Handler, lex::Token, parse::ast, symbol::SymbolTable};

use super::{hir, ty::Ty, ty::TyContext};

pub fn annotate(ast: ast::Ast, handler: &Handler) -> Option<hir::Ast> {
    let env = &mut TyContext::new();
    let bindings = &mut SymbolTable::new();
    let functions = &mut SymbolTable::new();
    Annotate::new(env, bindings, functions, handler).annotate_ast(ast)
}

struct Annotate<'a> {
    env: &'a mut TyContext,
    bindings: &'a mut SymbolTable<Ty>,
    functions: &'a mut SymbolTable<Ty>,
    handler: &'a Handler,
    has_enclosing_fn: bool,
}

impl<'a> Annotate<'a> {
    fn new(
        env: &'a mut TyContext,
        bindings: &'a mut SymbolTable<Ty>,
        functions: &'a mut SymbolTable<Ty>,
        handler: &'a Handler,
    ) -> Self {
        Self {
            env,
            bindings,
            functions,
            handler,
            has_enclosing_fn: false,
        }
    }

    fn annotate_ast(&mut self, ast: ast::Ast) -> Option<hir::Ast> {
        Some(hir::Ast {
            functions: self.annotate_fns(ast.functions)?,
            stmts: self.annotate_stmts(ast.stmts)?,
        })
    }

    fn annotate_stmts(&mut self, stmts: Vec<ast::Stmt>) -> Option<Vec<hir::Stmt>> {
        stmts.into_iter().map(|s| self.annotate_stmt(s)).collect()
    }

    fn annotate_stmt(&mut self, stmt: ast::Stmt) -> Option<hir::Stmt> {
        match stmt {
            ast::Stmt::Expr(e) => Some(hir::Stmt::Expr(self.annotate_expr(e)?)),
            ast::Stmt::SemiExpr(e) => Some(hir::Stmt::SemiExpr(self.annotate_expr(e)?)),
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
            ast::Stmt::While { cond, body } => Some(hir::Stmt::While {
                cond: self.annotate_expr(cond)?,
                body: self.annotate_block(body)?,
            }),
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
        }
    }

    fn annotate_expr(&mut self, expr: Box<ast::Expr>) -> Option<Box<hir::Expr>> {
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
                    ast::Lit::Err => self.env.new_var(),
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
                this.has_enclosing_fn = true;
                let params = this.annotate_params(params)?;
                let ret = this.ast_ty_to_ty(ret)?;
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
        };
        Some(Box::new(hir::Expr {
            kind,
            span,
            ty: self.env.new_var(),
        }))
    }

    fn annotate_block(&mut self, block: ast::Block) -> Option<hir::Block> {
        self.enter_scope(|this| {
            let functions = this.annotate_fns(block.functions)?;
            let stmts = this.annotate_stmts(block.stmts)?;
            Some(hir::Block {
                stmts,
                functions,
                ty: this.env.new_var(),
                span: block.span,
            })
        })
    }

    fn annotate_fns(&mut self, functions: Vec<ast::Function>) -> Option<Vec<hir::Function>> {
        functions
            .into_iter()
            .map(|func| self.annotate_fn(func))
            .collect::<Option<Vec<_>>>()
    }

    fn annotate_fn(&mut self, func: ast::Function) -> Option<hir::Function> {
        let ty = self.env.new_var();
        self.functions.insert(func.name.symbol, ty.clone());

        let env = &mut *self.env;
        let handler = self.handler;
        self.functions.enter_scope(|functions| {
            let bindings = &mut SymbolTable::new();
            let mut this = Annotate::new(env, bindings, functions, handler);

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
        let handler = self.handler;
        let has_enclosing_fn = self.has_enclosing_fn;
        self.bindings.enter_scope(|bindings| {
            functions.enter_scope(|functions| {
                let mut this = Annotate::new(env, bindings, functions, handler);
                this.has_enclosing_fn = has_enclosing_fn;
                f(&mut this)
            })
        })
    }

    fn ast_ty_to_ty(&mut self, ty: ast::Ty) -> Option<Ty> {
        let ty = match ty.kind {
            ast::TyKind::Ident(t) => self.token_to_ty(&t)?,
            ast::TyKind::Infer => self.env.new_var(),
            ast::TyKind::Unit => Ty::Unit,
        };

        Some(ty)
    }

    fn token_to_ty(&self, token: &Token) -> Option<Ty> {
        token.symbol.as_str_with(|s| {
            let ty = match s {
                "bool" => Ty::Bool,
                "int" => Ty::Int,
                "str" => Ty::Str,
                "float" => Ty::Float,
                _ => {
                    self.handler.report(token.span, "Unknown type");
                    return None;
                }
            };
            Some(ty)
        })
    }
}
