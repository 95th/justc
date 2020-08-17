use crate::{
    ast::{BinOp, Expr, Lit, Stmt, UnOp},
    symbol::Symbol,
};
use std::collections::HashMap;

macro_rules! bin_op {
    ($a:expr, $op:tt, $b:expr, $msg:literal) => {
        match ($a, $b) {
            (Lit::Number(a), Lit::Number(b)) => Lit::Number(a $op b),
            _ => panic!($msg),
        }
    };
}

macro_rules! bin_cmp_op {
    ($a:expr, $op:tt, $b:expr, $msg:literal) => {
        match ($a, $b) {
            (Lit::Number(a), Lit::Number(b)) => Lit::Bool(a $op b),
            _ => panic!($msg),
        }
    };
}

pub struct Interpreter {
    values: HashMap<Symbol, Option<Lit>>,
}

impl Interpreter {
    pub fn new() -> Self {
        Self {
            values: HashMap::new(),
        }
    }

    pub fn eval_stmt(&mut self, stmt: &Stmt) {
        match stmt {
            Stmt::Print(expr) => {
                let val = self.eval_expr(expr);
                println!("{}", val);
            }
            Stmt::Expr(expr) => {
                self.eval_expr(expr);
            }
            Stmt::Let(name, init) => {
                let mut value = None;
                if let Some(init) = init {
                    value = Some(self.eval_expr(init));
                }
                self.values.insert(name.symbol, value);
            }
            Stmt::Assign(name, expr) => {
                let value = self.eval_expr(expr);
                let old = self.values.insert(name.symbol, Some(value));
                assert!(old.is_some(), "Cannot assign to undeclare variable.")
            }
        }
    }

    pub fn eval_expr(&mut self, expr: &Expr) -> Lit {
        match expr {
            Expr::Binary(op, left, right) => {
                let left = self.eval_expr(left);
                let right = self.eval_expr(right);
                match op {
                    BinOp::Add => bin_op!(left, +, right, "Can only add numbers"),
                    BinOp::Sub => bin_op!(left, -, right, "Can only subtract numbers"),
                    BinOp::Mul => bin_op!(left, *, right, "Can only multiply numbers"),
                    BinOp::Div => bin_op!(left, /, right, "Can only divide numbers"),
                    BinOp::Gt => bin_cmp_op!(left, >, right, "Can only compare numbers"),
                    BinOp::Lt => bin_cmp_op!(left, <, right, "Can only compare numbers"),
                    BinOp::Ge => bin_cmp_op!(left, >=, right, "Can only compare numbers"),
                    BinOp::Le => bin_cmp_op!(left, <=, right, "Can only compare numbers"),
                    BinOp::Ne => bin_cmp_op!(left, !=, right, "Can only compare numbers"),
                    BinOp::Eq => bin_cmp_op!(left, ==, right, "Can only compare numbers"),
                }
            }
            Expr::Grouping(expr) => self.eval_expr(expr),
            Expr::Literal(lit) => lit.clone(),
            Expr::Unary(op, expr) => {
                let val = self.eval_expr(expr);
                match op {
                    UnOp::Not => {
                        if let Lit::Bool(v) = val {
                            Lit::Bool(!v)
                        } else {
                            panic!("Not a boolean")
                        }
                    }
                    UnOp::Neg => {
                        if let Lit::Number(n) = val {
                            Lit::Number(-n)
                        } else {
                            panic!("Not a number")
                        }
                    }
                }
            }
            Expr::Variable(name) => self
                .values
                .get(&name.symbol)
                .expect("Undefined variable")
                .as_ref()
                .cloned()
                .expect("Uninitialized variable"),
        }
    }
}
