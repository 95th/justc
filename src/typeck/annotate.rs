use crate::{
    parse::ast::{self, Block, Expr, ExprKind, Lit, Stmt},
    symbol::SymbolTable,
};

use super::{
    ty::Ty, ty::TyContext, typed_ast::TypedBlock, typed_ast::TypedExpr, typed_ast::TypedExprKind,
    typed_ast::TypedStmt,
};

pub fn annotate(ast: Vec<Stmt>) -> Vec<TypedStmt> {
    let mut env = TyContext::new();
    let mut bindings = SymbolTable::new();
    annotate_stmts(ast, &mut env, &mut bindings)
}

fn annotate_stmts(
    stmts: Vec<Stmt>,
    env: &mut TyContext,
    bindings: &mut SymbolTable<Ty>,
) -> Vec<TypedStmt> {
    stmts
        .into_iter()
        .map(|s| annotate_stmt(s, env, bindings))
        .collect()
}

fn annotate_stmt(stmt: Stmt, env: &mut TyContext, bindings: &mut SymbolTable<Ty>) -> TypedStmt {
    match stmt {
        Stmt::Expr(e) => TypedStmt::Expr(annotate_expr(e, env, bindings)),
        Stmt::SemiExpr(e) => TypedStmt::SemiExpr(annotate_expr(e, env, bindings)),
        Stmt::Let { name, init, ty } => {
            let init = init.map(|e| annotate_expr(e, env, bindings));

            let let_ty = if let Some(ty) = ty {
                match ty.kind {
                    ast::TyKind::Ident(t) => t.symbol.as_str_with(|s| match s {
                        "bool" => Ty::Bool,
                        "int" => Ty::Int,
                        "str" => Ty::Str,
                        "float" => Ty::Float,
                        _ => panic!("Unknown type: {}", s),
                    }),
                    ast::TyKind::Infer => env.new_var(),
                }
            } else {
                env.new_var()
            };

            bindings.insert(name.symbol, let_ty.clone());

            TypedStmt::Let {
                name,
                ty: let_ty,
                init,
            }
        }
        Stmt::Assign { name, val } => TypedStmt::Assign {
            name: annotate_expr(name, env, bindings),
            val: annotate_expr(val, env, bindings),
        },
    }
}

fn annotate_expr(
    expr: Box<Expr>,
    env: &mut TyContext,
    bindings: &mut SymbolTable<Ty>,
) -> Box<TypedExpr> {
    let (kind, span) = (expr.kind, expr.span);
    let kind = match kind {
        ExprKind::Binary { op, left, right } => TypedExprKind::Binary {
            op,
            left: annotate_expr(left, env, bindings),
            right: annotate_expr(right, env, bindings),
        },
        ExprKind::Grouping(e) => TypedExprKind::Grouping(annotate_expr(e, env, bindings)),
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
            expr: annotate_expr(expr, env, bindings),
        },
        ExprKind::Variable(t) => match bindings.get(&t.symbol) {
            Some(ty) => TypedExprKind::Variable(t, ty.clone()),
            None => panic!("Undefined variable: {}", t.symbol),
        },
        ExprKind::Block(block) => TypedExprKind::Block(annotate_block(block, env, bindings)),
        ExprKind::If {
            cond,
            then_clause,
            else_clause,
        } => TypedExprKind::If {
            cond: annotate_expr(cond, env, bindings),
            then_clause: annotate_block(then_clause, env, bindings),
            else_clause: else_clause.map(|e| annotate_block(e, env, bindings)),
        },
    };
    Box::new(TypedExpr {
        kind,
        span,
        ty: env.new_var(),
    })
}

fn annotate_block(block: Block, env: &mut TyContext, bindings: &mut SymbolTable<Ty>) -> TypedBlock {
    bindings.enter(|bindings| TypedBlock {
        stmts: annotate_stmts(block.stmts, env, bindings),
        ty: env.new_var(),
    })
}
