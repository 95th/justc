use crate::{
    err::Handler,
    parse::ast::{self, BinOp, Block, Expr, ExprKind, Lit, Stmt},
    scope::Bindings,
};
use std::rc::Rc;

pub type Ty = usize;

pub enum TyKind {
    Unit,
    Bool,
    Int,
    Float,
    Str,
}

pub struct TyCtxt {
    types: Vec<TyKind>,
    pub common: CommonTypes,
    handler: Rc<Handler>,
}

pub struct CommonTypes {
    unit: Ty,
    boolean: Ty,
    int: Ty,
    float: Ty,
    str: Ty,
}

impl TyCtxt {
    pub fn new(handler: &Rc<Handler>) -> Self {
        let types = vec![
            TyKind::Unit,
            TyKind::Bool,
            TyKind::Int,
            TyKind::Float,
            TyKind::Str,
        ];
        let common = CommonTypes {
            unit: 0,
            boolean: 1,
            int: 2,
            float: 3,
            str: 4,
        };
        Self {
            types,
            common,
            handler: handler.clone(),
        }
    }

    #[allow(unused)]
    pub fn new_ty(&mut self, kind: TyKind) -> Ty {
        let idx = self.types.len();
        self.types.push(kind);
        idx
    }

    pub fn get(&self, t: Ty) -> &TyKind {
        &self.types[t]
    }

    pub fn check_stmts(&mut self, stmts: &[Stmt], bindings: &mut Bindings) -> Option<()> {
        for stmt in stmts {
            self.check_stmt(stmt, bindings)?;
        }
        Some(())
    }

    fn check_stmt(&mut self, stmt: &Stmt, bindings: &mut Bindings) -> Option<()> {
        match stmt {
            Stmt::Expr(e) | Stmt::SemiExpr(e) => {
                self.check_expr(e, bindings)?;
            }
            Stmt::Let { name, ty, init } => {
                let init_ty = init.as_ref().map(|init| self.check_expr(init, bindings))?;

                let ty = match ty.as_ref() {
                    Some(ast::Ty {
                        kind: ast::TyKind::Ident(token),
                        ..
                    }) => {
                        let ty = token.symbol.as_str_with(|s| match s {
                            "bool" => Some(self.common.boolean),
                            "int" => Some(self.common.int),
                            "str" => Some(self.common.str),
                            "float" => Some(self.common.float),
                            _ => {
                                self.handler.report(token.span, "Unknown type");
                                None
                            }
                        })?;

                        if let Some(init_ty) = init_ty {
                            if ty != init_ty {
                                self.handler.report(name.span, "Type mismatch in let");
                                return None;
                            }
                        }

                        Some(ty)
                    }
                    _ => init_ty,
                };

                if let Some(ty) = ty {
                    bindings.insert(name.symbol, ty);
                } else {
                    self.handler.report(name.span, "Cannot infer type");
                    return None;
                }
            }
            Stmt::Assign { name, val } => {
                let val_ty = self.check_expr(val, bindings)?;
                let name_ty = match bindings.get(&name.symbol) {
                    Some(t) => t,
                    None => {
                        self.handler.report(name.span, "Undefined variable");
                        return None;
                    }
                };
                if name_ty != val_ty {
                    self.handler.report(val.span, "Type mismatch in assignment");
                    return None;
                }
            }
        }

        Some(())
    }

    fn check_expr(&mut self, expr: &Expr, bindings: &mut Bindings) -> Option<Ty> {
        match &expr.kind {
            ExprKind::Binary { op, left, right } => match op {
                BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem => {
                    let left_ty = self.check_expr(left, bindings)?;
                    let right_ty = self.check_expr(right, bindings)?;
                    if left_ty != right_ty {
                        self.handler
                            .report(expr.span, "Expression in binary op must be of same type");
                        return None;
                    }
                    let a = self.get(left_ty);
                    let b = self.get(right_ty);
                    match (a, b) {
                        (TyKind::Int, TyKind::Int) | (TyKind::Float, TyKind::Float) => {
                            Some(left_ty)
                        }
                        _ => {
                            self.handler
                                .report(expr.span, "Expressions must be numeric");
                            return None;
                        }
                    }
                }
                BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge => {
                    let left_ty = self.check_expr(left, bindings)?;
                    let right_ty = self.check_expr(right, bindings)?;
                    if left_ty != right_ty {
                        self.handler
                            .report(expr.span, "Expression in binary op must be of same type");
                        return None;
                    }
                    let a = self.get(left_ty);
                    let b = self.get(right_ty);
                    match (a, b) {
                        (TyKind::Int, TyKind::Int) | (TyKind::Float, TyKind::Float) => {
                            Some(self.common.boolean)
                        }
                        _ => {
                            self.handler
                                .report(expr.span, "Expressions must be numeric");
                            return None;
                        }
                    }
                }
                BinOp::Ne | BinOp::Eq => {
                    let left_ty = self.check_expr(left, bindings)?;
                    let right_ty = self.check_expr(right, bindings)?;
                    if left_ty != right_ty {
                        self.handler
                            .report(expr.span, "Expression in binary op must be of same type");
                        return None;
                    }
                    let a = self.get(left_ty);
                    let b = self.get(right_ty);
                    match (a, b) {
                        (TyKind::Int, TyKind::Int)
                        | (TyKind::Float, TyKind::Float)
                        | (TyKind::Bool, TyKind::Bool) => Some(self.common.boolean),
                        _ => {
                            self.handler
                                .report(expr.span, "Expressions must be numeric or boolean");
                            return None;
                        }
                    }
                }
                BinOp::And | BinOp::Or => {
                    let left_ty = self.check_expr(left, bindings)?;
                    let right_ty = self.check_expr(right, bindings)?;
                    if left_ty != right_ty {
                        self.handler
                            .report(expr.span, "Expression in binary op must be of same type");
                        return None;
                    }
                    let a = self.get(left_ty);
                    let b = self.get(right_ty);
                    match (a, b) {
                        (TyKind::Bool, TyKind::Bool) => Some(self.common.boolean),
                        _ => {
                            self.handler
                                .report(expr.span, "Expressions must be boolean");
                            return None;
                        }
                    }
                }
            },
            ExprKind::Grouping(e) => self.check_expr(e, bindings),
            ExprKind::Literal(lit) => match lit {
                Lit::Str(_) => Some(self.common.str),
                Lit::Integer(_) => Some(self.common.int),
                Lit::Float(_) => Some(self.common.float),
                Lit::Bool(_) => Some(self.common.boolean),
                Lit::Err => {
                    self.handler.report(expr.span, "Unknown type");
                    None
                }
            },
            ExprKind::Unary { expr, .. } => self.check_expr(expr, bindings),
            ExprKind::Variable(token) => match bindings.get(&token.symbol) {
                Some(t) => Some(t),
                None => {
                    self.handler.report(token.span, "Undefined variable");
                    None
                }
            },
            ExprKind::Block(b) => self.check_block(b, bindings),
            ExprKind::If {
                cond,
                then_clause,
                else_clause,
            } => {
                let c = self.check_expr(cond, bindings)?;
                if c != self.common.boolean {
                    self.handler
                        .report(cond.span, "Conditional must be a boolean expression");
                    return None;
                }

                let a = self.check_block(then_clause, bindings)?;
                let b = match else_clause {
                    Some(e) => self.check_block(e, bindings)?,
                    None => self.common.unit,
                };

                if a != b {
                    self.handler
                        .report(expr.span, "Arms of If Expression must be of same type");
                    return None;
                }
                Some(a)
            }
        }
    }

    fn check_block(&mut self, block: &Block, bindings: &mut Bindings) -> Option<Ty> {
        bindings.enter(|bindings| match &block.stmts[..] {
            [] => Some(self.common.unit),
            [rest @ .., last] => {
                self.check_stmts(rest, bindings)?;
                match last {
                    Stmt::Expr(e) => self.check_expr(e, bindings),
                    _ => Some(self.common.unit),
                }
            }
        })
    }
}
