use crate::ast::{BinOp, Expr, Lit, UnOp};

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

pub fn eval(expr: &Expr) -> Lit {
    match expr {
        Expr::Binary(op, left, right) => {
            let left = eval(left);
            let right = eval(right);
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
        Expr::Grouping(expr) => eval(expr),
        Expr::Literal(lit) => lit.clone(),
        Expr::Unary(op, expr) => {
            let val = eval(expr);
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
    }
}
