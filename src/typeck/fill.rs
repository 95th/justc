use super::{hir::*, ty::TyContext};
use crate::err::Result;

impl TyContext {
    pub fn fill(&mut self, ast: &mut Ast) -> Result<()> {
        self.fill_structs(&mut ast.structs)?;
        self.fill_fns(&mut ast.functions)?;
        self.fill_stmts(&mut ast.stmts)
    }

    fn fill_structs(&mut self, structs: &mut [Struct]) -> Result<()> {
        for s in structs.iter_mut() {
            if self.fill_ty(&mut s.ty).is_err() {
                return self
                    .handler
                    .mk_err(s.name.span, "Recursive type not allowed");
            }
        }

        for s in structs.iter_mut() {
            for f in &mut s.fields {
                self.fill_ty(&mut f.ty)?;
            }
        }

        for s in structs.iter_mut() {
            self.fill_fns(&mut s.methods)?;
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
        self.fill_ty(&mut f.ty)?;
        for p in &mut f.params {
            self.fill_ty(&mut p.param_ty.ty)?;
        }
        self.fill_ty(&mut f.ret.ty)?;
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
            Stmt::Let { ty, init, .. } => {
                self.fill_ty(ty)?;
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
        self.fill_ty(&mut e.ty)?;
        match &mut e.kind {
            ExprKind::Binary { left, right, .. } => {
                self.fill_expr(left)?;
                self.fill_expr(right)
            }
            ExprKind::Literal(_, ty, _) => self.fill_ty(ty),
            ExprKind::Unary { expr, .. } => self.fill_expr(expr),
            ExprKind::Variable(_, ty) => self.fill_ty(ty),
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
                    self.fill_ty(&mut p.param_ty.ty)?;
                }
                self.fill_ty(ret)?;
                self.fill_expr(body)
            }
            ExprKind::Call { callee, args } => {
                self.fill_expr(callee)?;
                for arg in args {
                    self.fill_expr(arg)?;
                }
                Ok(())
            }
            ExprKind::Struct(_, fields, ty) => {
                for f in fields {
                    self.fill_expr(&mut f.expr)?;
                }
                self.fill_ty(ty)
            }
            ExprKind::Field(e, _) => self.fill_expr(e),
            ExprKind::MethodCall { ty, args, .. } => {
                self.fill_ty(&mut ty.val)?;
                for arg in args {
                    self.fill_expr(arg)?;
                }
                Ok(())
            }
        }
    }

    fn fill_block(&mut self, block: &mut Block) -> Result<()> {
        self.fill_ty(&mut block.ty)?;
        self.fill_structs(&mut block.structs)?;
        self.fill_fns(&mut block.functions)?;
        self.fill_stmts(&mut block.stmts)
    }
}
