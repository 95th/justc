use std::collections::HashMap;

use crate::{
    err::Handler,
    lex::{Span, Spanned},
};

use super::{
    constraints::Constraint,
    hir::Block,
    hir::Expr,
    hir::ExprKind,
    hir::{Ast, Function, Stmt, Struct},
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
        match constraint {
            Constraint::Eq { expected, actual } => match (&mut expected.val, &mut actual.val) {
                (Ty::Int, Ty::Int)
                | (Ty::Bool, Ty::Bool)
                | (Ty::Float, Ty::Float)
                | (Ty::Unit, Ty::Unit)
                | (Ty::Str, Ty::Str) => Some(Subst::empty()),
                (Ty::Var(tvar), ref mut ty) => self.unify_var(*tvar, ty, actual.span),
                (ref mut ty, Ty::Var(tvar)) => self.unify_var(*tvar, ty, expected.span),
                (Ty::Fn(params_1, ret_1), Ty::Fn(params_2, ret_2)) => {
                    if params_1.len() != params_2.len() {
                        self.handler.report(
                            actual.span,
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
                        constraints.push(Constraint::Eq {
                            expected: Spanned::new(a.val.clone(), expected.span),
                            actual: Spanned::new(b.val.clone(), actual.span),
                        });
                    }
                    constraints.push(Constraint::Eq {
                        expected: Spanned::new(ret_1.val.clone(), ret_1.span),
                        actual: Spanned::new(ret_2.val.clone(), ret_2.span),
                    });
                    self.unify(&mut constraints)
                }
                (Ty::Struct(id_1, name_1, fields_1), Ty::Struct(id_2, name_2, fields_2)) => {
                    if name_1 != name_2 {
                        self.handler.report(
                            actual.span,
                            &format!("Type mismatch: Expected: {}, Actual: {}", name_1, name_2),
                        );
                        return None;
                    }

                    if fields_1.len() != fields_2.len() {
                        self.handler.report(
                            actual.span,
                            &format!(
                                "Number of fields mismatch: Expected: `{}`, Actual: `{}`",
                                fields_1.len(),
                                fields_2.len()
                            ),
                        );
                        return None;
                    }

                    *id_1 = *id_2;

                    let mut constraints = vec![];
                    for (name, a) in fields_1 {
                        let b = match fields_2.get_mut(name) {
                            Some(e) => e,
                            None => {
                                self.handler
                                    .report(actual.span, &format!("Field `{}` missing", name));
                                return None;
                            }
                        };

                        constraints.push(Constraint::Eq {
                            expected: Spanned::new(a.val.clone(), a.span),
                            actual: Spanned::new(b.val.clone(), b.span),
                        });
                    }
                    self.unify(&mut constraints)
                }
                (a, b) => {
                    self.handler.report(
                        actual.span,
                        &format!("Type mismatch: Expected: {:?}, Actual: {:?}", a, b),
                    );
                    None
                }
            },
            Constraint::FieldAccess {
                expr_ty,
                field,
                field_ty,
            } => {
                if let Ty::Struct(.., fields) = &mut expr_ty.val {
                    let a = match fields.get_mut(field) {
                        Some(e) => e,
                        None => {
                            self.handler.report(
                                field_ty.span,
                                &format!("Field or Method `{}` not found", field),
                            );
                            return None;
                        }
                    };

                    let constraint = Constraint::Eq {
                        expected: a.clone(),
                        actual: field_ty.clone(),
                    };
                    self.unify(&mut [constraint])
                } else {
                    self.handler.report(
                        field_ty.span,
                        &format!("Field or Method `{}` not found", field),
                    );
                    None
                }
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
        match constraint {
            Constraint::Eq { expected, actual } => {
                self.apply_ty(&mut expected.val);
                self.apply_ty(&mut actual.val);
            }
            Constraint::FieldAccess {
                expr_ty, field_ty, ..
            } => {
                self.apply_ty(&mut expr_ty.val);
                self.apply_ty(&mut field_ty.val);
            }
        }
    }

    fn apply_ty(&self, ty: &mut Ty) {
        for (&tvar, solution_ty) in &self.solutions {
            substitute(ty, tvar, solution_ty);
        }
    }

    pub fn fill_ast(&self, ast: &mut Ast) {
        self.fill_structs(&mut ast.structs);
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
            Stmt::Expr(expr, _) => self.fill_expr(expr),
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
            Stmt::Continue(_) | Stmt::Break(_) => {}
        }
    }

    fn fill_expr(&self, expr: &mut Expr) {
        match &mut expr.kind {
            ExprKind::Binary { left, right, .. } => {
                self.fill_expr(left);
                self.fill_expr(right);
            }
            ExprKind::Unary { expr, .. } => self.fill_expr(expr),
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
            ExprKind::Struct(_, fields, ty) => {
                for f in fields {
                    self.fill_expr(&mut f.expr);
                }
                self.fill_ty(ty);
            }
            ExprKind::Field(expr, _) => {
                self.fill_expr(expr);
            }
        }
        self.fill_ty(&mut expr.ty);
    }

    fn fill_block(&self, block: &mut Block) {
        self.fill_structs(&mut block.structs);
        self.fill_stmts(&mut block.stmts);
        self.fill_fns(&mut block.functions);
        self.fill_ty(&mut block.ty);
    }

    fn fill_structs(&self, structs: &mut [Struct]) {
        for s in structs {
            self.fill_struct(s);
        }
    }

    fn fill_struct(&self, s: &mut Struct) {
        self.fill_ty(&mut s.ty);
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
        match ty {
            Ty::Var(tvar) => {
                if let Some(replacement) = self.solutions.get(tvar) {
                    *ty = replacement.clone();
                }
            }
            Ty::Unit | Ty::Bool | Ty::Int | Ty::Float | Ty::Str => {}
            Ty::Fn(params, ret) => {
                for p in params {
                    self.fill_ty(&mut p.val);
                }
                self.fill_ty(&mut ret.val);
            }
            Ty::Struct(.., fields) => {
                for f in fields.values_mut() {
                    self.fill_ty(&mut f.val);
                }
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
            for p in params {
                substitute(&mut p.val, tvar, replacement);
            }
            substitute(&mut ret.val, tvar, replacement);
        }
        Ty::Struct(.., fields) => {
            for (_, ty) in fields {
                substitute(&mut ty.val, tvar, replacement);
            }
        }
        Ty::Unit | Ty::Bool | Ty::Int | Ty::Float | Ty::Str => {}
    }
}
