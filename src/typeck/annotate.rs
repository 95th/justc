use crate::{
    err::Handler,
    lex::Token,
    parse::ast::{self, Block, Expr, ExprKind, Function, Lit, Param, Stmt},
    symbol::SymbolTable,
};

use super::{
    ty::Ty,
    ty::TyContext,
    typed_ast::TypedBlock,
    typed_ast::TypedExpr,
    typed_ast::TypedExprKind,
    typed_ast::TypedParam,
    typed_ast::{TypedFunction, TypedStmt},
};

pub fn annotate(ast: Vec<Stmt>, handler: &Handler) -> Option<Vec<TypedStmt>> {
    let env = &mut TyContext::new();
    let bindings = &mut SymbolTable::new();
    Annotate::new(env, bindings, &handler).annotate_stmts(ast)
}

struct Annotate<'a> {
    env: &'a mut TyContext,
    bindings: &'a mut SymbolTable<Ty>,
    handler: &'a Handler,
}

impl<'a> Annotate<'a> {
    fn new(
        env: &'a mut TyContext,
        bindings: &'a mut SymbolTable<Ty>,
        handler: &'a Handler,
    ) -> Self {
        Self {
            env,
            bindings,
            handler,
        }
    }

    fn annotate_stmts(&mut self, stmts: Vec<Stmt>) -> Option<Vec<TypedStmt>> {
        stmts.into_iter().map(|s| self.annotate_stmt(s)).collect()
    }

    fn annotate_stmt(&mut self, stmt: Stmt) -> Option<TypedStmt> {
        match stmt {
            Stmt::Expr(e) => Some(TypedStmt::Expr(self.annotate_expr(e)?)),
            Stmt::SemiExpr(e) => Some(TypedStmt::SemiExpr(self.annotate_expr(e)?)),
            Stmt::Let { name, init, ty } => {
                let init = match init {
                    Some(e) => Some(self.annotate_expr(e)?),
                    None => None,
                };

                let let_ty = self.ast_ty_to_ty(ty, false)?;
                self.bindings.insert(name.symbol, let_ty.clone());

                Some(TypedStmt::Let {
                    name,
                    ty: let_ty,
                    init,
                })
            }
            Stmt::Assign { name, val } => Some(TypedStmt::Assign {
                name: self.annotate_expr(name)?,
                val: self.annotate_expr(val)?,
            }),
            Stmt::While { cond, body } => Some(TypedStmt::While {
                cond: self.annotate_expr(cond)?,
                body: self.annotate_block(body)?,
            }),
        }
    }

    fn annotate_expr(&mut self, expr: Box<Expr>) -> Option<Box<TypedExpr>> {
        let (kind, span) = (expr.kind, expr.span);
        let kind = match kind {
            ExprKind::Binary { op, left, right } => TypedExprKind::Binary {
                op,
                left: self.annotate_expr(left)?,
                right: self.annotate_expr(right)?,
            },
            ExprKind::Grouping(e) => TypedExprKind::Grouping(self.annotate_expr(e)?),
            ExprKind::Literal(lit, span) => {
                let ty = match &lit {
                    Lit::Str(_) => Ty::Str,
                    Lit::Integer(_) => Ty::Int,
                    Lit::Float(_) => Ty::Float,
                    Lit::Bool(_) => Ty::Bool,
                    Lit::Err => self.env.new_var(),
                };
                TypedExprKind::Literal(lit, ty, span)
            }
            ExprKind::Unary { op, expr } => TypedExprKind::Unary {
                op,
                expr: self.annotate_expr(expr)?,
            },
            ExprKind::Variable(t) => match self.bindings.get(&t.symbol) {
                Some(ty) => TypedExprKind::Variable(t, ty.clone()),
                None => {
                    self.handler.report(t.span, "Undefined variable");
                    return None;
                }
            },
            ExprKind::Block(block) => TypedExprKind::Block(self.annotate_block(block)?),
            ExprKind::If {
                cond,
                then_clause,
                else_clause,
            } => TypedExprKind::If {
                cond: self.annotate_expr(cond)?,
                then_clause: self.annotate_block(then_clause)?,
                else_clause: match else_clause {
                    Some(e) => Some(self.annotate_expr(e)?),
                    None => None,
                },
            },
            ExprKind::Closure { params, ret, body } => self.enter_scope(|this| {
                let params = this.annotate_params(params)?;
                let ret = this.ast_ty_to_ty(ret, false)?;
                let body = this.annotate_expr(body)?;
                Some(TypedExprKind::Closure { params, ret, body })
            })?,
            ExprKind::Call { callee, args } => TypedExprKind::Call {
                callee: self.annotate_expr(callee)?,
                args: args
                    .into_iter()
                    .map(|arg| self.annotate_expr(arg))
                    .collect::<Option<Vec<_>>>()?,
            },
        };
        Some(Box::new(TypedExpr {
            kind,
            span,
            ty: self.env.new_var(),
        }))
    }

    fn annotate_block(&mut self, block: Block) -> Option<TypedBlock> {
        self.enter_scope(|this| {
            Some(TypedBlock {
                stmts: this.annotate_stmts(block.stmts)?,
                functions: this.annotate_fns(block.functions)?,
                ty: this.env.new_var(),
                span: block.span,
            })
        })
    }

    fn annotate_fns(&mut self, functions: Vec<Function>) -> Option<Vec<TypedFunction>> {
        functions
            .into_iter()
            .map(|func| self.annotate_fn(func))
            .collect::<Option<Vec<_>>>()
    }

    fn annotate_fn(&mut self, func: Function) -> Option<TypedFunction> {
        let bindings = &mut SymbolTable::new();
        let mut this = Annotate::new(&mut self.env, bindings, &self.handler);

        let params = this.annotate_params(func.params)?;
        for p in &params {
            this.bindings.insert(p.name.symbol, p.ty.clone());
        }

        let ret = this.ast_ty_to_ty(func.ret, true)?;
        let body = this.annotate_block(func.body)?;
        let ty = this.env.new_var();
        Some(TypedFunction {
            name: func.name,
            params,
            ret,
            body,
            ty,
        })
    }

    fn annotate_params(&mut self, params: Vec<Param>) -> Option<Vec<TypedParam>> {
        params
            .into_iter()
            .map(|p| {
                let param_ty = self.ast_ty_to_ty(p.ty, false)?;
                self.bindings.insert(p.name.symbol, param_ty.clone());
                Some(TypedParam {
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
        let handler = self.handler;
        self.bindings.enter_scope(|bindings| {
            let mut annotate = Annotate::new(env, bindings, handler);
            f(&mut annotate)
        })
    }

    fn ast_ty_to_ty(&mut self, ty: Option<ast::Ty>, none_is_unit: bool) -> Option<Ty> {
        let ty = if let Some(ty) = ty {
            match ty.kind {
                ast::TyKind::Ident(t) => self.token_to_ty(&t)?,
                ast::TyKind::Infer => self.env.new_var(),
            }
        } else if none_is_unit {
            Ty::Unit
        } else {
            self.env.new_var()
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
