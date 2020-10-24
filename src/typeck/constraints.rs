use std::{collections::HashMap, fmt};

use crate::{
    lex::{Span, Spanned},
    parse::ast::{BinOp, UnOp},
};

use super::{
    hir::{Ast, Block, Expr, ExprKind, Function, Stmt, Struct},
    ty::Ty,
};

pub struct Constraint {
    pub a: Ty,
    pub b: Ty,
    pub span_a: Span,
    pub span_b: Span,
}

impl fmt::Debug for Constraint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?} == {:?}", self.a, self.b)
    }
}

struct Collector {
    enclosing_fn_ret_ty: Option<Ty>,
    constraints: Vec<Constraint>,
}

pub fn collect(ast: &Ast) -> Vec<Constraint> {
    let mut collector = Collector::new();
    collector.collect_structs(&ast.structs);
    collector.collect_fns(&ast.functions);
    collector.collect_stmts(&ast.stmts);
    collector.constraints
}

impl Collector {
    fn new() -> Self {
        Self {
            enclosing_fn_ret_ty: None,
            constraints: vec![],
        }
    }

    fn collect_stmts(&mut self, ast: &[Stmt]) {
        for stmt in ast {
            self.collect_stmt(stmt);
        }
    }

    fn collect_stmt(&mut self, stmt: &Stmt) {
        match stmt {
            Stmt::Expr(expr, _) => self.collect_expr(expr),
            Stmt::Let { name, ty, init } => {
                if let Some(init) = init {
                    self.collect_expr(init);
                    self.constraints.push(Constraint {
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
                self.constraints.push(Constraint {
                    a: name.ty.clone(),
                    b: val.ty.clone(),
                    span_a: name.span,
                    span_b: val.span,
                });
            }
            Stmt::While { cond, body } => {
                self.collect_expr(cond);
                self.collect_block(body);
                self.constraints.push(Constraint {
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
            Stmt::Continue(_) | Stmt::Break(_) => {}
        }
    }

    fn collect_expr(&mut self, expr: &Expr) {
        match &expr.kind {
            ExprKind::Binary {
                op, left, right, ..
            } => {
                self.collect_expr(left);
                self.collect_expr(right);
                self.constraints.push(Constraint {
                    a: left.ty.clone(),
                    b: right.ty.clone(),
                    span_a: left.span,
                    span_b: right.span,
                });
                match op.val {
                    BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem => {
                        self.constraints.push(Constraint {
                            a: expr.ty.clone(),
                            b: left.ty.clone(),
                            span_a: expr.span,
                            span_b: left.span,
                        });
                    }
                    BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge => {
                        self.constraints.push(Constraint {
                            a: expr.ty.clone(),
                            b: Ty::Bool,
                            span_a: expr.span,
                            span_b: expr.span,
                        });
                    }
                    BinOp::Ne | BinOp::Eq => {
                        self.constraints.push(Constraint {
                            a: expr.ty.clone(),
                            b: Ty::Bool,
                            span_a: expr.span,
                            span_b: expr.span,
                        });
                    }
                    BinOp::And | BinOp::Or => {
                        self.constraints.push(Constraint {
                            a: left.ty.clone(),
                            b: Ty::Bool,
                            span_a: left.span,
                            span_b: left.span,
                        });
                        self.constraints.push(Constraint {
                            a: expr.ty.clone(),
                            b: Ty::Bool,
                            span_a: expr.span,
                            span_b: expr.span,
                        });
                    }
                }
            }
            ExprKind::Literal(_, ty, span) => {
                self.constraints.push(Constraint {
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
                        self.constraints.push(Constraint {
                            a: expr.ty.clone(),
                            b: Ty::Bool,
                            span_a: expr.span,
                            span_b: expr.span,
                        });
                        self.constraints.push(Constraint {
                            a: e.ty.clone(),
                            b: Ty::Bool,
                            span_a: e.span,
                            span_b: e.span,
                        });
                    }
                    UnOp::Neg => {
                        self.constraints.push(Constraint {
                            a: expr.ty.clone(),
                            b: e.ty.clone(),
                            span_a: expr.span,
                            span_b: e.span,
                        });
                    }
                }
            }
            ExprKind::Variable(name, ty) => {
                self.constraints.push(Constraint {
                    a: expr.ty.clone(),
                    b: ty.clone(),
                    span_a: expr.span,
                    span_b: name.span,
                });
            }
            ExprKind::Block(block) => {
                self.collect_block(block);
                self.constraints.push(Constraint {
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
                self.constraints.push(Constraint {
                    a: cond.ty.clone(),
                    b: Ty::Bool,
                    span_a: cond.span,
                    span_b: cond.span,
                });

                self.collect_block(then_clause);
                if let Some(else_clause) = else_clause {
                    self.collect_expr(else_clause);
                    self.constraints.push(Constraint {
                        a: then_clause.ty.clone(),
                        b: else_clause.ty.clone(),
                        span_a: then_clause.span,
                        span_b: else_clause.span,
                    });
                    self.constraints.push(Constraint {
                        a: expr.ty.clone(),
                        b: then_clause.ty.clone(),
                        span_a: expr.span,
                        span_b: then_clause.span,
                    });
                } else {
                    self.constraints.push(Constraint {
                        a: then_clause.ty.clone(),
                        b: Ty::Unit,
                        span_a: then_clause.span,
                        span_b: then_clause.span,
                    });
                    self.constraints.push(Constraint {
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
                    this.constraints.push(Constraint {
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
                    this.constraints.push(Constraint {
                        a: ret.clone(),
                        b: body.ty.clone(),
                        span_a: body.span,
                        span_b: body.span,
                    });
                });
            }
            ExprKind::Call { callee, args } => {
                self.collect_expr(callee);
                self.constraints.push(Constraint {
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
            ExprKind::Struct(name, fields, ty) => {
                let mut field_map = HashMap::new();
                for f in fields {
                    self.collect_expr(&f.expr);
                    field_map.insert(f.name.symbol, Spanned::new(f.expr.ty.clone(), f.expr.span));
                }

                self.constraints.push(Constraint {
                    a: ty.clone(),
                    b: Ty::Struct(name.symbol, field_map),
                    span_a: name.span,
                    span_b: name.span,
                });

                self.constraints.push(Constraint {
                    a: expr.ty.clone(),
                    b: ty.clone(),
                    span_a: expr.span,
                    span_b: name.span,
                });
            }
        }
    }

    fn collect_block(&mut self, block: &Block) {
        self.collect_structs(&block.structs);
        self.collect_fns(&block.functions);

        for stmt in &block.stmts {
            self.collect_stmt(stmt);
            if let Stmt::Return(span, e) = stmt {
                if let Some(e) = e {
                    self.constraints.push(Constraint {
                        a: self.enclosing_fn_ret_ty.clone().unwrap(),
                        b: e.ty.clone(),
                        span_a: e.span,
                        span_b: e.span,
                    });
                } else {
                    self.constraints.push(Constraint {
                        a: self.enclosing_fn_ret_ty.clone().unwrap(),
                        b: Ty::Unit,
                        span_a: *span,
                        span_b: *span,
                    });
                }
            }
        }

        match block.stmts.last() {
            Some(Stmt::Expr(expr, false)) => {
                self.constraints.push(Constraint {
                    a: block.ty.clone(),
                    b: expr.ty.clone(),
                    span_a: block.span,
                    span_b: expr.span,
                });
            }
            Some(Stmt::Return(_, _)) => {}
            _ => {
                self.constraints.push(Constraint {
                    a: block.ty.clone(),
                    b: Ty::Unit,
                    span_a: block.span,
                    span_b: block.span,
                });
            }
        }
    }

    fn collect_structs(&mut self, structs: &[Struct]) {
        for s in structs {
            self.collect_struct(s);
        }
    }

    fn collect_struct(&mut self, s: &Struct) {
        self.constraints.push(Constraint {
            a: s.ty.clone(),
            b: Ty::Struct(
                s.name.symbol,
                s.fields
                    .iter()
                    .map(|f| (f.name.symbol, Spanned::new(f.ty.clone(), f.name.span)))
                    .collect(),
            ),
            span_a: s.name.span,
            span_b: s.name.span,
        })
    }

    fn collect_fns(&mut self, items: &[Function]) {
        for item in items {
            self.enter_fn_scope(item.ret.clone(), |this| this.collect_fn(item))
        }
    }

    fn collect_fn(&mut self, function: &Function) {
        self.collect_block(&function.body);
        self.constraints.push(Constraint {
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
        self.constraints.push(Constraint {
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
