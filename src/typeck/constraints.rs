use std::collections::HashSet;

use crate::parse::ast::{BinOp, UnOp};

use super::{
    ty::Ty,
    typed_ast::{TypedBlock, TypedExpr, TypedExprKind, TypedStmt},
};

#[derive(Debug, Hash, Eq, PartialEq)]
pub struct Constraint(pub Ty, pub Ty);

pub fn collect(ast: &mut [TypedStmt]) -> HashSet<Constraint> {
    let mut set = HashSet::new();
    collect_stmts(ast, &mut set);
    set
}

pub fn collect_stmts(ast: &mut [TypedStmt], set: &mut HashSet<Constraint>) {
    for stmt in ast {
        collect_stmt(stmt, set);
    }
}

fn collect_stmt(stmt: &mut TypedStmt, set: &mut HashSet<Constraint>) {
    match stmt {
        TypedStmt::Expr(e) | TypedStmt::SemiExpr(e) => collect_expr(e, set),
        TypedStmt::Let { ty, init, .. } => {
            if let Some(init) = init {
                collect_expr(init, set);
                set.insert(Constraint(ty.clone(), init.ty.clone()));
            }
        }
        TypedStmt::Assign { name, val } => {
            collect_expr(name, set);
            collect_expr(val, set);
            set.insert(Constraint(name.ty.clone(), val.ty.clone()));
        }
    }
}

fn collect_expr(expr: &mut TypedExpr, set: &mut HashSet<Constraint>) {
    match &mut expr.kind {
        TypedExprKind::Binary { op, left, right } => {
            collect_expr(left, set);
            collect_expr(right, set);
            set.insert(Constraint(left.ty.clone(), right.ty.clone()));
            match op {
                BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem => {
                    set.insert(Constraint(expr.ty.clone(), left.ty.clone()));
                }
                BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge => {
                    set.insert(Constraint(expr.ty.clone(), Ty::Bool));
                }
                BinOp::Ne | BinOp::Eq => {
                    set.insert(Constraint(expr.ty.clone(), Ty::Bool));
                }
                BinOp::And | BinOp::Or => {
                    set.insert(Constraint(left.ty.clone(), Ty::Bool));
                    set.insert(Constraint(expr.ty.clone(), Ty::Bool));
                }
            }
        }
        TypedExprKind::Grouping(e) => collect_expr(e, set),
        TypedExprKind::Literal(_, ty) => {
            set.insert(Constraint(expr.ty.clone(), ty.clone()));
        }
        TypedExprKind::Unary { op, expr: e } => {
            collect_expr(e, set);
            match op {
                UnOp::Not => {
                    set.insert(Constraint(expr.ty.clone(), Ty::Bool));
                    set.insert(Constraint(e.ty.clone(), Ty::Bool));
                }
                UnOp::Neg => {
                    set.insert(Constraint(expr.ty.clone(), e.ty.clone()));
                }
            }
        }
        TypedExprKind::Variable(_, ty) => {
            set.insert(Constraint(expr.ty.clone(), ty.clone()));
        }
        TypedExprKind::Block(block) => {
            collect_block(block, set);
            set.insert(Constraint(expr.ty.clone(), block.ty.clone()));
        }
        TypedExprKind::If {
            cond,
            then_clause,
            else_clause,
        } => {
            collect_expr(cond, set);
            collect_block(then_clause, set);
            if let Some(else_clause) = else_clause {
                collect_block(else_clause, set);
                set.insert(Constraint(then_clause.ty.clone(), else_clause.ty.clone()));
                set.insert(Constraint(expr.ty.clone(), then_clause.ty.clone()));
            } else {
                set.insert(Constraint(then_clause.ty.clone(), Ty::Unit));
                set.insert(Constraint(expr.ty.clone(), Ty::Unit));
            }
        }
    }
}

fn collect_block(block: &mut TypedBlock, set: &mut HashSet<Constraint>) {
    collect_stmts(&mut block.stmts, set);
    if let Some(TypedStmt::Expr(e)) = block.stmts.last_mut() {
        set.insert(Constraint(block.ty.clone(), e.ty.clone()));
    } else {
        set.insert(Constraint(block.ty.clone(), Ty::Unit));
    }
}
