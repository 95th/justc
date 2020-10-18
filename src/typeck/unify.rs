use std::collections::HashMap;

use crate::{err::Handler, lex::Span};

use super::{
    constraints::Constraint, ty::Ty, typed_ast::TypedBlock, typed_ast::TypedExpr,
    typed_ast::TypedExprKind, typed_ast::TypedStmt,
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
        Ty::Fn(params, ret) => params.iter().any(|ty| occurs(tvar, ty)) || occurs(tvar, ret),
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

    pub fn fill_ast(&self, stmts: &mut [TypedStmt]) {
        for s in stmts {
            self.fill_stmt(s);
        }
    }

    fn fill_stmt(&self, stmt: &mut TypedStmt) {
        match stmt {
            TypedStmt::Expr(e) | TypedStmt::SemiExpr(e) => self.fill_expr(e),
            TypedStmt::Let { ty, init, .. } => {
                self.fill_ty(ty);
                if let Some(init) = init {
                    self.fill_expr(init);
                }
            }
            TypedStmt::Assign { name, val } => {
                self.fill_expr(name);
                self.fill_expr(val);
            }
        }
    }

    fn fill_expr(&self, expr: &mut TypedExpr) {
        match &mut expr.kind {
            TypedExprKind::Binary { left, right, .. } => {
                self.fill_expr(left);
                self.fill_expr(right);
            }
            TypedExprKind::Grouping(expr) | TypedExprKind::Unary { expr, .. } => {
                self.fill_expr(expr)
            }
            TypedExprKind::Literal(_, ty, _) | TypedExprKind::Variable(_, ty) => self.fill_ty(ty),
            TypedExprKind::Block(block) => self.fill_block(block),
            TypedExprKind::If {
                cond,
                then_clause,
                else_clause,
            } => {
                self.fill_expr(cond);
                self.fill_block(then_clause);
                if let Some(else_clause) = else_clause {
                    self.fill_block(else_clause);
                }
            }
        }
        self.fill_ty(&mut expr.ty);
    }

    fn fill_block(&self, block: &mut TypedBlock) {
        self.fill_ast(&mut block.stmts);
        self.fill_ty(&mut block.ty);
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
                .for_each(|p| substitute(p, tvar, replacement));
            substitute(ret, tvar, replacement);
        }
        Ty::Unit | Ty::Bool | Ty::Int | Ty::Float | Ty::Str => {}
    }
}
