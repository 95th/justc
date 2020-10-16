use std::collections::HashMap;

use super::{
    constraints::Constraint, ty::Ty, typed_ast::TypedBlock, typed_ast::TypedExpr,
    typed_ast::TypedExprKind, typed_ast::TypedStmt,
};

pub fn unify(constraints: &mut [Constraint]) -> Substitution {
    match constraints {
        [] => Substitution::new(),
        [head, tail @ ..] => {
            let mut subst = unify_one(head);
            subst.apply(tail);
            let subst_tail = unify(tail);
            subst.compose(subst_tail);
            subst
        }
    }
}

fn unify_one(constraint: &mut Constraint) -> Substitution {
    match constraint {
        Constraint(Ty::Int, Ty::Int)
        | Constraint(Ty::Bool, Ty::Bool)
        | Constraint(Ty::Float, Ty::Float)
        | Constraint(Ty::Unit, Ty::Unit)
        | Constraint(Ty::Str, Ty::Str) => Substitution::new(),
        Constraint(Ty::Var(tvar), ty) | Constraint(ty, Ty::Var(tvar)) => unify_var(*tvar, ty),
        Constraint(a, b) => panic!("Cannot unify type {:?} with {:?}", a, b),
    }
}

fn unify_var(tvar: u64, ty: &Ty) -> Substitution {
    match ty {
        Ty::Var(tvar2) => {
            if tvar == *tvar2 {
                Substitution::new()
            } else {
                Substitution::from_pair(tvar, ty)
            }
        }
        ty if occurs(tvar, ty) => panic!("Circular use: {} occurs in {:?}", tvar, ty),
        ty => Substitution::from_pair(tvar, ty),
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
pub struct Substitution {
    solutions: HashMap<u64, Ty>,
}

impl Substitution {
    pub fn new() -> Self {
        Self {
            solutions: HashMap::new(),
        }
    }

    pub fn from_pair(tvar: u64, ty: &Ty) -> Self {
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
        let Constraint(a, b) = constraint;
        self.apply_ty(a);
        self.apply_ty(b);
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
            TypedExprKind::Literal(_, ty) | TypedExprKind::Variable(_, ty) => self.fill_ty(ty),
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
