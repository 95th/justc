use std::collections::HashMap;

use crate::{err::Handler, lex::Span};

use super::{
    constraints::Constraint,
    hir::Block,
    hir::Expr,
    hir::ExprKind,
    hir::{Ast, Function, Stmt},
    ty::Ty,
};

pub fn unify(constraints: &mut [Constraint], handler: &Handler) -> Option<Subst> {
    Unify::new(handler).unify(constraints)
}

struct Unify<'a> {
    handler: &'a Handler,
}

impl<'a> Unify<'a> {
    fn new(handler: &'a Handler) -> Self {
        Self { handler }
    }

    fn unify(&self, constraints: &mut [Constraint]) -> Option<Subst> {
        match constraints {
            [] => Some(Subst::empty()),
            [head, tail @ ..] => {
                let mut subst = self.unify_one(head)?;
                subst.apply(tail);
                let subst_tail = self.unify(tail)?;
                subst.compose(subst_tail);
                Some(subst)
            }
        }
    }

    fn unify_one(&self, constraint: &mut Constraint) -> Option<Subst> {
        let Constraint { a, b, .. } = constraint;
        match (a, b) {
            (Ty::Int, Ty::Int)
            | (Ty::Bool, Ty::Bool)
            | (Ty::Float, Ty::Float)
            | (Ty::Unit, Ty::Unit)
            | (Ty::Str, Ty::Str) => Some(Subst::empty()),
            (Ty::Var(tvar), ref mut ty) => self.unify_var(*tvar, ty, constraint.span_b),
            (ref mut ty, Ty::Var(tvar)) => self.unify_var(*tvar, ty, constraint.span_a),
            (Ty::Fn(params_1, ret_1), Ty::Fn(params_2, ret_2)) => {
                if params_1.len() != params_2.len() {
                    self.handler.report(
                        constraint.span_b,
                        &format!(
                            "Number of arguments mismatch: Expected: {}, Actual: {}",
                            params_1.len(),
                            params_2.len()
                        ),
                    );
                    return None;
                }

                let mut constraints = vec![];
                for (a, b) in params_1.iter_mut().zip(params_2.iter_mut()) {
                    constraints.push(Constraint {
                        a: a.val.clone(),
                        b: b.val.clone(),
                        span_a: a.span,
                        span_b: b.span,
                    });
                }
                constraints.push(Constraint {
                    a: ret_1.val.clone(),
                    b: ret_2.val.clone(),
                    span_a: ret_1.span,
                    span_b: ret_2.span,
                });
                self.unify(&mut constraints)
            }
            (a, b) => {
                self.handler.report(
                    constraint.span_b,
                    &format!("Type mismatch: Expected: {:?}, Actual: {:?}", a, b),
                );
                None
            }
        }
    }

    fn unify_var(&self, tvar: u64, ty: &Ty, span: Span) -> Option<Subst> {
        match ty {
            Ty::Var(tvar2) => {
                if tvar == *tvar2 {
                    Some(Subst::empty())
                } else {
                    Some(Subst::new(tvar, ty))
                }
            }
            ty if occurs(tvar, ty) => {
                self.handler
                    .report(span, &format!("Type is of infinite size: {:?}", ty));
                None
            }
            ty => Some(Subst::new(tvar, ty)),
        }
    }
}

fn occurs(tvar: u64, ty: &Ty) -> bool {
    match ty {
        Ty::Fn(params, ret) => {
            params.iter().any(|ty| occurs(tvar, &ty.val)) || occurs(tvar, &ret.val)
        }
        Ty::Var(tvar2) => tvar == *tvar2,
        _ => false,
    }
}

#[derive(Debug)]
pub struct Subst {
    solutions: HashMap<u64, Ty>,
}

impl Subst {
    pub fn empty() -> Self {
        Self {
            solutions: HashMap::new(),
        }
    }

    pub fn new(tvar: u64, ty: &Ty) -> Self {
        let mut solutions = HashMap::new();
        solutions.insert(tvar, ty.clone());
        Self { solutions }
    }

    pub fn compose(&mut self, other: Self) {
        self.solutions.values_mut().for_each(|t| other.apply_ty(t));
        self.solutions.extend(other.solutions);
    }

    pub fn apply(&self, constraints: &mut [Constraint]) {
        for constraint in constraints {
            self.apply_one(constraint);
        }
    }

    fn apply_one(&self, constraint: &mut Constraint) {
        self.apply_ty(&mut constraint.a);
        self.apply_ty(&mut constraint.b);
    }

    fn apply_ty(&self, ty: &mut Ty) {
        for (&tvar, solution_ty) in &self.solutions {
            substitute(ty, tvar, solution_ty);
        }
    }

    pub fn fill_ast(&self, ast: &mut Ast) {
        self.fill_fns(&mut ast.functions);
        self.fill_stmts(&mut ast.stmts);
    }

    fn fill_stmts(&self, stmts: &mut [Stmt]) {
        for s in stmts {
            self.fill_stmt(s);
        }
    }

    fn fill_stmt(&self, stmt: &mut Stmt) {
        match stmt {
            Stmt::Expr(e) | Stmt::SemiExpr(e) => self.fill_expr(e),
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
        }
    }

    fn fill_expr(&self, expr: &mut Expr) {
        match &mut expr.kind {
            ExprKind::Binary { left, right, .. } => {
                self.fill_expr(left);
                self.fill_expr(right);
            }
            ExprKind::Grouping(expr) | ExprKind::Unary { expr, .. } => self.fill_expr(expr),
            ExprKind::Literal(_, ty, _) | ExprKind::Variable(_, ty) => self.fill_ty(ty),
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
                    self.fill_ty(&mut p.ty);
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
        }
        self.fill_ty(&mut expr.ty);
    }

    fn fill_block(&self, block: &mut Block) {
        self.fill_stmts(&mut block.stmts);
        self.fill_fns(&mut block.functions);
        self.fill_ty(&mut block.ty);
    }

    fn fill_fns(&self, functions: &mut [Function]) {
        for f in functions {
            self.fill_fn(f);
        }
    }

    fn fill_fn(&self, function: &mut Function) {
        for p in &mut function.params {
            self.fill_ty(&mut p.ty);
        }
        self.fill_ty(&mut function.ret);
        self.fill_ty(&mut function.ty);
        self.fill_block(&mut function.body);
    }

    fn fill_ty(&self, ty: &mut Ty) {
        if let Ty::Var(tvar) = ty {
            if let Some(replacement) = self.solutions.get(tvar) {
                *ty = replacement.clone();
            }
        }
    }
}

fn substitute(ty: &mut Ty, tvar: u64, replacement: &Ty) {
    match ty {
        Ty::Var(tvar2) => {
            if tvar == *tvar2 {
                *ty = replacement.clone();
            }
        }
        Ty::Fn(params, ret) => {
            params
                .iter_mut()
                .for_each(|p| substitute(&mut p.val, tvar, replacement));
            substitute(&mut ret.val, tvar, replacement);
        }
        Ty::Unit | Ty::Bool | Ty::Int | Ty::Float | Ty::Str => {}
    }
}
