use super::{hir::*, ty::TyContext};

pub fn fill_tys(ast: &mut Ast, env: &mut TyContext) {
    fill_structs(&mut ast.structs, env);
    fill_impls(&mut ast.impls, env);
    fill_fns(&mut ast.functions, env);
    fill_stmts(&mut ast.stmts, env);
}

fn fill_structs(structs: &mut [Struct], env: &mut TyContext) {
    for s in structs {
        for f in &mut s.fields {
            env.fill_ty(&mut f.ty);
        }
        env.fill_ty(&mut s.ty);
    }
}

fn fill_impls(impls: &mut [Impl], env: &mut TyContext) {
    for i in impls {
        env.fill_ty(&mut i.ty);
        fill_fns(&mut i.functions, env);
    }
}

fn fill_fns(functions: &mut [Function], env: &mut TyContext) {
    for f in functions {
        fill_fn(f, env);
    }
}

fn fill_fn(f: &mut Function, env: &mut TyContext) {
    env.fill_ty(&mut f.ty);
    for p in &mut f.params {
        env.fill_ty(&mut p.ty);
    }
    env.fill_ty(&mut f.ret);
    fill_block(&mut f.body, env);
}

fn fill_stmts(stmts: &mut [Stmt], env: &mut TyContext) {
    for s in stmts {
        fill_stmt(s, env);
    }
}

fn fill_stmt(s: &mut Stmt, env: &mut TyContext) {
    match s {
        Stmt::Expr(e, _) => fill_expr(e, env),
        Stmt::Let { ty, init, .. } => {
            env.fill_ty(ty);
            if let Some(init) = init {
                fill_expr(init, env);
            }
        }
        Stmt::Assign { name, val } => {
            fill_expr(name, env);
            fill_expr(val, env);
        }
        Stmt::While { cond, body } => {
            fill_expr(cond, env);
            fill_block(body, env);
        }
        Stmt::Return(_, e) => {
            if let Some(e) = e {
                fill_expr(e, env);
            }
        }
        Stmt::Continue(_) => {}
        Stmt::Break(_) => {}
    }
}

fn fill_expr(e: &mut Expr, env: &mut TyContext) {
    env.fill_ty(&mut e.ty);
    match &mut e.kind {
        ExprKind::Binary { left, right, .. } => {
            fill_expr(left, env);
            fill_expr(right, env);
        }
        ExprKind::Literal(_, ty, _) => env.fill_ty(ty),
        ExprKind::Unary { expr, .. } => fill_expr(expr, env),
        ExprKind::Variable(_, ty) => env.fill_ty(ty),
        ExprKind::Block(block) => fill_block(block, env),
        ExprKind::If {
            cond,
            then_clause,
            else_clause,
        } => {
            fill_expr(cond, env);
            fill_block(then_clause, env);
            if let Some(else_clause) = else_clause {
                fill_expr(else_clause, env);
            }
        }
        ExprKind::Closure { params, ret, body } => {
            for p in params {
                env.fill_ty(&mut p.ty);
            }
            env.fill_ty(ret);
            fill_expr(body, env);
        }
        ExprKind::Call { callee, args } => {
            fill_expr(callee, env);
            for arg in args {
                fill_expr(arg, env);
            }
        }
        ExprKind::Struct(_, fields, ty) => {
            for f in fields {
                fill_expr(&mut f.expr, env);
            }
            env.fill_ty(ty);
        }
        ExprKind::Field(e, _) => fill_expr(e, env),
    }
}

fn fill_block(block: &mut Block, env: &mut TyContext) {
    env.fill_ty(&mut block.ty);
    fill_structs(&mut block.structs, env);
    fill_impls(&mut block.impls, env);
    fill_fns(&mut block.functions, env);
    fill_stmts(&mut block.stmts, env);
}
