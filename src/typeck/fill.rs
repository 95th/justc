use super::{hir::*, ty::TyContext};

impl TyContext {
    pub fn fill(&mut self, ast: &mut Ast) {
        self.fill_structs(&mut ast.structs);
        self.fill_impls(&mut ast.impls);
        self.fill_fns(&mut ast.functions);
        self.fill_stmts(&mut ast.stmts);
    }

    fn fill_structs(&mut self, structs: &mut [Struct]) {
        for s in structs {
            for f in &mut s.fields {
                self.fill_ty(&mut f.ty);
            }
            self.fill_ty(&mut s.ty);
        }
    }

    fn fill_impls(&mut self, impls: &mut [Impl]) {
        for i in impls {
            self.fill_ty(&mut i.ty);
            self.fill_fns(&mut i.functions);
        }
    }

    fn fill_fns(&mut self, functions: &mut [Function]) {
        for f in functions {
            self.fill_fn(f);
        }
    }

    fn fill_fn(&mut self, f: &mut Function) {
        self.fill_ty(&mut f.ty);
        for p in &mut f.params {
            dbg!(&p);
            self.fill_ty(&mut p.param_ty.ty);
        }
        self.fill_ty(&mut f.ret.ty);
        self.fill_block(&mut f.body);
    }

    fn fill_stmts(&mut self, stmts: &mut [Stmt]) {
        for s in stmts {
            self.fill_stmt(s);
        }
    }

    fn fill_stmt(&mut self, s: &mut Stmt) {
        match s {
            Stmt::Expr(e, _) => self.fill_expr(e),
            Stmt::Let { ty, init, .. } => {
                self.fill_ty(ty);
                if let Some(init) = init {
                    self.fill_expr(init);
                }
            }
            Stmt::Assign { name, val } => {
                self.fill_expr(name);
                self.fill_expr(val);
            }
            Stmt::While { cond, body } => {
                self.fill_expr(cond);
                self.fill_block(body);
            }
            Stmt::Return(_, e) => {
                if let Some(e) = e {
                    self.fill_expr(e);
                }
            }
            Stmt::Continue(_) => {}
            Stmt::Break(_) => {}
        }
    }

    fn fill_expr(&mut self, e: &mut Expr) {
        self.fill_ty(&mut e.ty);
        match &mut e.kind {
            ExprKind::Binary { left, right, .. } => {
                self.fill_expr(left);
                self.fill_expr(right);
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
                self.fill_expr(cond);
                self.fill_block(then_clause);
                if let Some(else_clause) = else_clause {
                    self.fill_expr(else_clause);
                }
            }
            ExprKind::Closure { params, ret, body } => {
                for p in params {
                    self.fill_ty(&mut p.param_ty.ty);
                }
                self.fill_ty(ret);
                self.fill_expr(body);
            }
            ExprKind::Call { callee, args } => {
                self.fill_expr(callee);
                for arg in args {
                    self.fill_expr(arg);
                }
            }
            ExprKind::Struct(_, fields, ty) => {
                for f in fields {
                    self.fill_expr(&mut f.expr);
                }
                self.fill_ty(ty);
            }
            ExprKind::Field(e, _) => self.fill_expr(e),
        }
    }

    fn fill_block(&mut self, block: &mut Block) {
        self.fill_ty(&mut block.ty);
        self.fill_structs(&mut block.structs);
        self.fill_impls(&mut block.impls);
        self.fill_fns(&mut block.functions);
        self.fill_stmts(&mut block.stmts);
    }
}
