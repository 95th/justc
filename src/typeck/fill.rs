use super::{hir::*, ty::TyContext};
use crate::{err::Result, lex::Span};

impl TyContext {
    pub fn fill(&mut self, ast: &mut Ast) -> Result<()> {
        self.fill_structs(&mut ast.structs)?;
        self.fill_impls(&mut ast.impls)?;
        self.fill_fns(&mut ast.functions)?;
        self.fill_stmts(&mut ast.stmts)
    }

    fn fill_structs(&mut self, structs: &mut [Struct]) -> Result<()> {
        for s in structs {
            for f in &mut s.fields {
                self.fill_ty(&mut f.ty, s.name.span)?;
            }
            self.fill_ty(&mut s.ty, s.name.span)?;
        }
        Ok(())
    }

    fn fill_impls(&mut self, impls: &mut [Impl]) -> Result<()> {
        for i in impls {
            self.fill_ty(&mut i.ty, Span::DUMMY)?;
            self.fill_fns(&mut i.functions)?;
        }
        Ok(())
    }

    fn fill_fns(&mut self, functions: &mut [Function]) -> Result<()> {
        for f in functions {
            self.fill_fn(f)?;
        }
        Ok(())
    }

    fn fill_fn(&mut self, f: &mut Function) -> Result<()> {
        self.fill_ty(&mut f.ty, f.name.span)?;
        for p in &mut f.params {
            self.fill_ty(&mut p.param_ty.ty, p.param_ty.span)?;
        }
        self.fill_ty(&mut f.ret.ty, f.ret.span)?;
        self.fill_block(&mut f.body)
    }

    fn fill_stmts(&mut self, stmts: &mut [Stmt]) -> Result<()> {
        for s in stmts {
            self.fill_stmt(s)?;
        }
        Ok(())
    }

    fn fill_stmt(&mut self, s: &mut Stmt) -> Result<()> {
        match s {
            Stmt::Expr(e, _) => self.fill_expr(e),
            Stmt::Let { name, ty, init } => {
                self.fill_ty(ty, name.span)?;
                if let Some(init) = init {
                    self.fill_expr(init)?;
                }
                Ok(())
            }
            Stmt::Assign { name, val } => {
                self.fill_expr(name)?;
                self.fill_expr(val)
            }
            Stmt::While { cond, body } => {
                self.fill_expr(cond)?;
                self.fill_block(body)
            }
            Stmt::Return(_, e) => {
                if let Some(e) = e {
                    self.fill_expr(e)?;
                }
                Ok(())
            }
            Stmt::Continue(_) | Stmt::Break(_) => Ok(()),
        }
    }

    fn fill_expr(&mut self, e: &mut Expr) -> Result<()> {
        self.fill_ty(&mut e.ty, e.span)?;
        match &mut e.kind {
            ExprKind::Binary { left, right, .. } => {
                self.fill_expr(left)?;
                self.fill_expr(right)
            }
            ExprKind::Literal(_, ty, span) => self.fill_ty(ty, *span),
            ExprKind::Unary { expr, .. } => self.fill_expr(expr),
            ExprKind::Variable(name, ty) => self.fill_ty(ty, name.span),
            ExprKind::Block(block) => self.fill_block(block),
            ExprKind::If {
                cond,
                then_clause,
                else_clause,
            } => {
                self.fill_expr(cond)?;
                self.fill_block(then_clause)?;
                if let Some(else_clause) = else_clause {
                    self.fill_expr(else_clause)?;
                }
                Ok(())
            }
            ExprKind::Closure { params, ret, body } => {
                for p in params {
                    self.fill_ty(&mut p.param_ty.ty, p.param_ty.span)?;
                }
                self.fill_ty(ret, body.span)?;
                self.fill_expr(body)
            }
            ExprKind::Call { callee, args } => {
                self.fill_expr(callee)?;
                for arg in args {
                    self.fill_expr(arg)?;
                }
                Ok(())
            }
            ExprKind::Struct(name, fields, ty) => {
                for f in fields {
                    self.fill_expr(&mut f.expr)?;
                }
                self.fill_ty(ty, name.span)
            }
            ExprKind::Field(e, _) => self.fill_expr(e),
        }
    }

    fn fill_block(&mut self, block: &mut Block) -> Result<()> {
        self.fill_ty(&mut block.ty, block.span)?;
        self.fill_structs(&mut block.structs)?;
        self.fill_impls(&mut block.impls)?;
        self.fill_fns(&mut block.functions)?;
        self.fill_stmts(&mut block.stmts)
    }
}
