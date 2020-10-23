use std::collections::BTreeSet;

use crate::{
    lex::{Span, Spanned},
    parse::ast::{BinOp, UnOp},
};

use super::{
    hir::{Ast, Block, Expr, ExprKind, Function, Stmt},
    ty::Ty,
};

#[derive(Debug, PartialOrd, Ord)]
pub struct Constraint {
    pub a: Ty,
    pub b: Ty,
    pub span_a: Span,
    pub span_b: Span,
}

impl PartialEq for Constraint {
    fn eq(&self, other: &Self) -> bool {
        self.a == other.a && self.b == other.b
    }
}

impl Eq for Constraint {}

pub fn collect(ast: &mut Ast) -> BTreeSet<Constraint> {
    let mut set = BTreeSet::new();
    collect_fns(&mut ast.functions, &mut set);
    collect_stmts(&mut ast.stmts, &mut set);
    set
}

fn collect_stmts(ast: &mut [Stmt], set: &mut BTreeSet<Constraint>) {
    for stmt in ast {
        collect_stmt(stmt, set);
    }
}

fn collect_stmt(stmt: &mut Stmt, set: &mut BTreeSet<Constraint>) {
    match stmt {
        Stmt::Expr(e) | Stmt::SemiExpr(e) => collect_expr(e, set),
        Stmt::Let { name, ty, init } => {
            if let Some(init) = init {
                collect_expr(init, set);
                set.insert(Constraint {
                    a: ty.clone(),
                    b: init.ty.clone(),
                    span_a: name.span,
                    span_b: init.span,
                });
            }
        }
        Stmt::Assign { name, val } => {
            collect_expr(name, set);
            collect_expr(val, set);
            set.insert(Constraint {
                a: name.ty.clone(),
                b: val.ty.clone(),
                span_a: name.span,
                span_b: val.span,
            });
        }
        Stmt::While { cond, body } => {
            collect_expr(cond, set);
            collect_block(body, set);
            set.insert(Constraint {
                a: body.ty.clone(),
                b: Ty::Unit,
                span_a: body.span,
                span_b: body.span,
            });
        }
    }
}

fn collect_expr(expr: &mut Expr, set: &mut BTreeSet<Constraint>) {
    match &mut expr.kind {
        ExprKind::Binary {
            op, left, right, ..
        } => {
            collect_expr(left, set);
            collect_expr(right, set);
            set.insert(Constraint {
                a: left.ty.clone(),
                b: right.ty.clone(),
                span_a: left.span,
                span_b: right.span,
            });
            match op.val {
                BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem => {
                    set.insert(Constraint {
                        a: expr.ty.clone(),
                        b: left.ty.clone(),
                        span_a: expr.span,
                        span_b: left.span,
                    });
                }
                BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge => {
                    set.insert(Constraint {
                        a: expr.ty.clone(),
                        b: Ty::Bool,
                        span_a: expr.span,
                        span_b: expr.span,
                    });
                }
                BinOp::Ne | BinOp::Eq => {
                    set.insert(Constraint {
                        a: expr.ty.clone(),
                        b: Ty::Bool,
                        span_a: expr.span,
                        span_b: expr.span,
                    });
                }
                BinOp::And | BinOp::Or => {
                    set.insert(Constraint {
                        a: left.ty.clone(),
                        b: Ty::Bool,
                        span_a: left.span,
                        span_b: left.span,
                    });
                    set.insert(Constraint {
                        a: expr.ty.clone(),
                        b: Ty::Bool,
                        span_a: expr.span,
                        span_b: expr.span,
                    });
                }
            }
        }
        ExprKind::Grouping(e) => collect_expr(e, set),
        ExprKind::Literal(_, ty, span) => {
            set.insert(Constraint {
                a: expr.ty.clone(),
                b: ty.clone(),
                span_a: expr.span,
                span_b: *span,
            });
        }
        ExprKind::Unary { op, expr: e, .. } => {
            collect_expr(e, set);
            match op.val {
                UnOp::Not => {
                    set.insert(Constraint {
                        a: expr.ty.clone(),
                        b: Ty::Bool,
                        span_a: expr.span,
                        span_b: expr.span,
                    });
                    set.insert(Constraint {
                        a: e.ty.clone(),
                        b: Ty::Bool,
                        span_a: e.span,
                        span_b: e.span,
                    });
                }
                UnOp::Neg => {
                    set.insert(Constraint {
                        a: expr.ty.clone(),
                        b: e.ty.clone(),
                        span_a: expr.span,
                        span_b: e.span,
                    });
                }
            }
        }
        ExprKind::Variable(name, ty) => {
            set.insert(Constraint {
                a: expr.ty.clone(),
                b: ty.clone(),
                span_a: expr.span,
                span_b: name.span,
            });
        }
        ExprKind::Block(block) => {
            collect_block(block, set);
            set.insert(Constraint {
                a: expr.ty.clone(),
                b: block.ty.clone(),
                span_a: expr.span,
                span_b: block.span,
            });
        }
        ExprKind::If {
            cond,
            then_clause,
            else_clause,
        } => {
            collect_expr(cond, set);
            set.insert(Constraint {
                a: cond.ty.clone(),
                b: Ty::Bool,
                span_a: cond.span,
                span_b: cond.span,
            });

            collect_block(then_clause, set);
            if let Some(else_clause) = else_clause {
                collect_expr(else_clause, set);
                set.insert(Constraint {
                    a: then_clause.ty.clone(),
                    b: else_clause.ty.clone(),
                    span_a: then_clause.span,
                    span_b: else_clause.span,
                });
                set.insert(Constraint {
                    a: expr.ty.clone(),
                    b: then_clause.ty.clone(),
                    span_a: expr.span,
                    span_b: then_clause.span,
                });
            } else {
                set.insert(Constraint {
                    a: then_clause.ty.clone(),
                    b: Ty::Unit,
                    span_a: then_clause.span,
                    span_b: then_clause.span,
                });
                set.insert(Constraint {
                    a: expr.ty.clone(),
                    b: Ty::Unit,
                    span_a: expr.span,
                    span_b: expr.span,
                });
            }
        }
        ExprKind::Closure { params, ret, body } => {
            collect_expr(body, set);
            set.insert(Constraint {
                a: expr.ty.clone(),
                b: Ty::Fn(
                    params
                        .iter()
                        .map(|p| Spanned::new(p.ty.clone(), p.name.span))
                        .collect(),
                    Box::new(Spanned::new(body.ty.clone(), body.span)),
                ),
                span_a: expr.span,
                span_b: expr.span,
            });
            set.insert(Constraint {
                a: ret.clone(),
                b: body.ty.clone(),
                span_a: body.span,
                span_b: body.span,
            });
        }
        ExprKind::Call { callee, args } => {
            collect_expr(callee, set);
            set.insert(Constraint {
                a: callee.ty.clone(),
                b: Ty::Fn(
                    args.iter()
                        .map(|arg| Spanned::new(arg.ty.clone(), arg.span))
                        .collect(),
                    Box::new(Spanned::new(expr.ty.clone(), expr.span)),
                ),
                span_a: expr.span,
                span_b: expr.span,
            });

            for arg in args {
                collect_expr(arg, set);
            }
        }
    }
}

fn collect_block(block: &mut Block, set: &mut BTreeSet<Constraint>) {
    collect_stmts(&mut block.stmts, set);
    collect_fns(&mut block.functions, set);
    if let Some(Stmt::Expr(e)) = block.stmts.last_mut() {
        set.insert(Constraint {
            a: block.ty.clone(),
            b: e.ty.clone(),
            span_a: block.span,
            span_b: e.span,
        });
    } else {
        set.insert(Constraint {
            a: block.ty.clone(),
            b: Ty::Unit,
            span_a: block.span,
            span_b: block.span,
        });
    }
}

fn collect_fns(items: &mut [Function], set: &mut BTreeSet<Constraint>) {
    for item in items {
        collect_item(item, set);
    }
}

fn collect_item(function: &mut Function, set: &mut BTreeSet<Constraint>) {
    collect_block(&mut function.body, set);
    set.insert(Constraint {
        a: function.ty.clone(),
        b: Ty::Fn(
            function
                .params
                .iter()
                .map(|p| Spanned::new(p.ty.clone(), p.name.span))
                .collect(),
            Box::new(Spanned::new(function.body.ty.clone(), function.body.span)),
        ),
        span_a: function.name.span,
        span_b: function.name.span,
    });
    set.insert(Constraint {
        a: function.ret.clone(),
        b: function.body.ty.clone(),
        span_a: function.body.span,
        span_b: function.body.span,
    });
}
