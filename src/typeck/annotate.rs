use crate::parse::ast::{Block, Expr, ExprKind, Lit, Stmt};

use super::{
    ty::Ty, ty::TyEnv, typed_ast::TypedBlock, typed_ast::TypedExpr, typed_ast::TypedExprKind,
    typed_ast::TypedStmt,
};

pub fn annotate(ast: Vec<Stmt>) -> Vec<TypedStmt> {
    let mut env = TyEnv::new();
    annotate_stmts(ast, &mut env)
}

fn annotate_stmts(stmts: Vec<Stmt>, env: &mut TyEnv) -> Vec<TypedStmt> {
    stmts.into_iter().map(|s| annotate_stmt(s, env)).collect()
}

fn annotate_stmt(stmt: Stmt, env: &mut TyEnv) -> TypedStmt {
    match stmt {
        Stmt::Expr(e) => TypedStmt::Expr(annotate_expr(e, env)),
        Stmt::SemiExpr(e) => TypedStmt::SemiExpr(annotate_expr(e, env)),
        Stmt::Let { name, init, .. } => {
            let init = init.map(|e| annotate_expr(e, env));
            let new_ty = env.new_var();
            env.define(name.symbol, new_ty.clone());
            TypedStmt::Let {
                name,
                ty: new_ty,
                init,
            }
        }
        Stmt::Assign { name, val } => TypedStmt::Assign {
            name: annotate_expr(name, env),
            val: annotate_expr(val, env),
        },
    }
}

fn annotate_expr(expr: Box<Expr>, env: &mut TyEnv) -> Box<TypedExpr> {
    let (kind, span) = (expr.kind, expr.span);
    let kind = match kind {
        ExprKind::Binary { op, left, right } => TypedExprKind::Binary {
            op,
            left: annotate_expr(left, env),
            right: annotate_expr(right, env),
        },
        ExprKind::Grouping(e) => TypedExprKind::Grouping(annotate_expr(e, env)),
        ExprKind::Literal(lit) => {
            let ty = match &lit {
                Lit::Str(_) => Ty::Str,
                Lit::Integer(_) => Ty::Int,
                Lit::Float(_) => Ty::Float,
                Lit::Bool(_) => Ty::Bool,
                Lit::Err => env.new_var(),
            };
            TypedExprKind::Literal(lit, ty)
        }
        ExprKind::Unary { op, expr } => TypedExprKind::Unary {
            op,
            expr: annotate_expr(expr, env),
        },
        ExprKind::Variable(t) => match env.lookup(t.symbol) {
            Some(ty) => TypedExprKind::Variable(t, ty.clone()),
            None => panic!("Undefined variable: {}", t.symbol),
        },
        ExprKind::Block(block) => TypedExprKind::Block(annotate_block(block, env)),
        ExprKind::If {
            cond,
            then_clause,
            else_clause,
        } => TypedExprKind::If {
            cond: annotate_expr(cond, env),
            then_clause: annotate_block(then_clause, env),
            else_clause: else_clause.map(|e| annotate_block(e, env)),
        },
    };
    Box::new(TypedExpr {
        kind,
        span,
        ty: env.new_var(),
    })
}

fn annotate_block(block: Block, env: &mut TyEnv) -> TypedBlock {
    env.in_scope(|env| TypedBlock {
        stmts: annotate_stmts(block.stmts, env),
        ty: env.new_var(),
    })
}
