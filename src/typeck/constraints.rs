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

struct Collector {
    enclosing_fn_ret_ty: Option<Ty>,
    constraints: BTreeSet<Constraint>,
}

pub fn collect(ast: &Ast) -> Vec<Constraint> {
    let mut collector = Collector::new();
    collector.collect_fns(&ast.functions);
    collector.collect_stmts(&ast.stmts);
    collector.constraints.into_iter().collect()
}

impl Collector {
    fn new() -> Self {
        Self {
            enclosing_fn_ret_ty: None,
            constraints: BTreeSet::new(),
        }
    }

    fn collect_stmts(&mut self, ast: &[Stmt]) {
        for stmt in ast {
            self.collect_stmt(stmt);
        }
    }

    fn collect_stmt(&mut self, stmt: &Stmt) {
        match stmt {
            Stmt::Expr { expr, .. } => self.collect_expr(expr),
            Stmt::Let { name, ty, init } => {
                if let Some(init) = init {
                    self.collect_expr(init);
                    self.constraints.insert(Constraint {
                        a: ty.clone(),
                        b: init.ty.clone(),
                        span_a: name.span,
                        span_b: init.span,
                    });
                }
            }
            Stmt::Assign { name, val } => {
                self.collect_expr(name);
                self.collect_expr(val);
                self.constraints.insert(Constraint {
                    a: name.ty.clone(),
                    b: val.ty.clone(),
                    span_a: name.span,
                    span_b: val.span,
                });
            }
            Stmt::While { cond, body } => {
                self.collect_expr(cond);
                self.collect_block(body);
                self.constraints.insert(Constraint {
                    a: body.ty.clone(),
                    b: Ty::Unit,
                    span_a: body.span,
                    span_b: body.span,
                });
            }
            Stmt::Return(_, e) => {
                if let Some(e) = e {
                    self.collect_expr(e);
                }
            }
            Stmt::Continue(_) => {}
        }
    }

    fn collect_expr(&mut self, expr: &Expr) {
        match &expr.kind {
            ExprKind::Binary {
                op, left, right, ..
            } => {
                self.collect_expr(left);
                self.collect_expr(right);
                self.constraints.insert(Constraint {
                    a: left.ty.clone(),
                    b: right.ty.clone(),
                    span_a: left.span,
                    span_b: right.span,
                });
                match op.val {
                    BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem => {
                        self.constraints.insert(Constraint {
                            a: expr.ty.clone(),
                            b: left.ty.clone(),
                            span_a: expr.span,
                            span_b: left.span,
                        });
                    }
                    BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge => {
                        self.constraints.insert(Constraint {
                            a: expr.ty.clone(),
                            b: Ty::Bool,
                            span_a: expr.span,
                            span_b: expr.span,
                        });
                    }
                    BinOp::Ne | BinOp::Eq => {
                        self.constraints.insert(Constraint {
                            a: expr.ty.clone(),
                            b: Ty::Bool,
                            span_a: expr.span,
                            span_b: expr.span,
                        });
                    }
                    BinOp::And | BinOp::Or => {
                        self.constraints.insert(Constraint {
                            a: left.ty.clone(),
                            b: Ty::Bool,
                            span_a: left.span,
                            span_b: left.span,
                        });
                        self.constraints.insert(Constraint {
                            a: expr.ty.clone(),
                            b: Ty::Bool,
                            span_a: expr.span,
                            span_b: expr.span,
                        });
                    }
                }
            }
            ExprKind::Literal(_, ty, span) => {
                self.constraints.insert(Constraint {
                    a: expr.ty.clone(),
                    b: ty.clone(),
                    span_a: expr.span,
                    span_b: *span,
                });
            }
            ExprKind::Unary { op, expr: e, .. } => {
                self.collect_expr(e);
                match op.val {
                    UnOp::Not => {
                        self.constraints.insert(Constraint {
                            a: expr.ty.clone(),
                            b: Ty::Bool,
                            span_a: expr.span,
                            span_b: expr.span,
                        });
                        self.constraints.insert(Constraint {
                            a: e.ty.clone(),
                            b: Ty::Bool,
                            span_a: e.span,
                            span_b: e.span,
                        });
                    }
                    UnOp::Neg => {
                        self.constraints.insert(Constraint {
                            a: expr.ty.clone(),
                            b: e.ty.clone(),
                            span_a: expr.span,
                            span_b: e.span,
                        });
                    }
                }
            }
            ExprKind::Variable(name, ty) => {
                self.constraints.insert(Constraint {
                    a: expr.ty.clone(),
                    b: ty.clone(),
                    span_a: expr.span,
                    span_b: name.span,
                });
            }
            ExprKind::Block(block) => {
                self.collect_block(block);
                self.constraints.insert(Constraint {
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
                self.collect_expr(cond);
                self.constraints.insert(Constraint {
                    a: cond.ty.clone(),
                    b: Ty::Bool,
                    span_a: cond.span,
                    span_b: cond.span,
                });

                self.collect_block(then_clause);
                if let Some(else_clause) = else_clause {
                    self.collect_expr(else_clause);
                    self.constraints.insert(Constraint {
                        a: then_clause.ty.clone(),
                        b: else_clause.ty.clone(),
                        span_a: then_clause.span,
                        span_b: else_clause.span,
                    });
                    self.constraints.insert(Constraint {
                        a: expr.ty.clone(),
                        b: then_clause.ty.clone(),
                        span_a: expr.span,
                        span_b: then_clause.span,
                    });
                } else {
                    self.constraints.insert(Constraint {
                        a: then_clause.ty.clone(),
                        b: Ty::Unit,
                        span_a: then_clause.span,
                        span_b: then_clause.span,
                    });
                    self.constraints.insert(Constraint {
                        a: expr.ty.clone(),
                        b: Ty::Unit,
                        span_a: expr.span,
                        span_b: expr.span,
                    });
                }
            }
            ExprKind::Closure { params, ret, body } => {
                self.enter_fn_scope(ret.clone(), |this| {
                    this.collect_expr(body);
                    this.constraints.insert(Constraint {
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
                    this.constraints.insert(Constraint {
                        a: ret.clone(),
                        b: body.ty.clone(),
                        span_a: body.span,
                        span_b: body.span,
                    });
                });
            }
            ExprKind::Call { callee, args } => {
                self.collect_expr(callee);
                self.constraints.insert(Constraint {
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
                    self.collect_expr(arg);
                }
            }
        }
    }

    fn collect_block(&mut self, block: &Block) {
        self.collect_fns(&block.functions);

        for stmt in &block.stmts {
            self.collect_stmt(stmt);
            if let Stmt::Return(span, e) = stmt {
                if let Some(e) = e {
                    self.constraints.insert(Constraint {
                        a: self.enclosing_fn_ret_ty.clone().unwrap(),
                        b: e.ty.clone(),
                        span_a: e.span,
                        span_b: e.span,
                    });
                } else {
                    self.constraints.insert(Constraint {
                        a: self.enclosing_fn_ret_ty.clone().unwrap(),
                        b: Ty::Unit,
                        span_a: *span,
                        span_b: *span,
                    });
                }
            }
        }

        match block.stmts.last() {
            Some(Stmt::Expr {
                expr,
                semicolon: false,
            }) => {
                self.constraints.insert(Constraint {
                    a: block.ty.clone(),
                    b: expr.ty.clone(),
                    span_a: block.span,
                    span_b: expr.span,
                });
            }
            Some(Stmt::Return(_, _)) => {}
            _ => {
                self.constraints.insert(Constraint {
                    a: block.ty.clone(),
                    b: Ty::Unit,
                    span_a: block.span,
                    span_b: block.span,
                });
            }
        }
    }

    fn collect_fns(&mut self, items: &[Function]) {
        for item in items {
            self.enter_fn_scope(item.ret.clone(), |this| this.collect_fn(item))
        }
    }

    fn collect_fn(&mut self, function: &Function) {
        self.collect_block(&function.body);
        self.constraints.insert(Constraint {
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
        self.constraints.insert(Constraint {
            a: function.ret.clone(),
            b: function.body.ty.clone(),
            span_a: function.body.span,
            span_b: function.body.span,
        });
    }

    fn enter_fn_scope<F, R>(&mut self, ty: Ty, f: F) -> R
    where
        F: FnOnce(&mut Self) -> R,
    {
        let save_ret_ty = self.enclosing_fn_ret_ty.take();
        self.enclosing_fn_ret_ty = Some(ty);
        let result = f(self);
        self.enclosing_fn_ret_ty = save_ret_ty;
        result
    }
}
