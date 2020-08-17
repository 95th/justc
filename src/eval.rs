use crate::{
    ast::{BinOp, Expr, Lit, Stmt, UnOp},
    err::Result,
    symbol::Symbol,
    token::Token,
};
use std::{collections::HashMap, mem};

macro_rules! bin_op {
    ($a:expr, $op:tt, $b:expr, $msg:literal) => {
        match ($a, $b) {
            (Lit::Number(a), Lit::Number(b)) => Ok(Lit::Number(a $op b)),
            _ => bail!($msg),
        }
    };
}

macro_rules! bin_cmp_op {
    ($a:expr, $op:tt, $b:expr, $msg:literal) => {
        match ($a, $b) {
            (Lit::Number(a), Lit::Number(b)) => Ok(Lit::Bool(a $op b)),
            _ => bail!($msg),
        }
    };
}

#[derive(Default)]
pub struct Interpreter {
    env: Env,
}

type Scope = HashMap<Symbol, Option<Lit>>;

#[derive(Default)]
struct Env {
    current: Scope,
    outer: Vec<Scope>,
}

impl Env {
    fn enter_scope(&mut self) {
        let c = mem::take(&mut self.current);
        self.outer.push(c);
    }

    fn exit_scope(&mut self) {
        self.current = self.outer.pop().unwrap();
    }

    fn declare(&mut self, name: &Token) {
        self.current.insert(name.symbol, None);
    }

    fn define(&mut self, name: &Token, value: Lit) -> Result<()> {
        if self.current.contains_key(&name.symbol) {
            self.current.insert(name.symbol, Some(value));
            return Ok(());
        }

        for scope in self.outer.iter_mut().rev() {
            if scope.contains_key(&name.symbol) {
                scope.insert(name.symbol, Some(value));
                return Ok(());
            }
        }

        bail!("Undeclared variable {}", name.symbol);
    }

    fn get(&self, name: Symbol) -> Result<&Lit> {
        if let Some(val) = self.current.get(&name) {
            match val {
                Some(t) => return Ok(t),
                None => bail!("Uninitialized variable {}", name),
            }
        }

        for scope in self.outer.iter().rev() {
            if let Some(val) = scope.get(&name) {
                match val {
                    Some(t) => return Ok(t),
                    None => bail!("Uninitialized variable {}", name),
                }
            }
        }

        bail!("Undefined variable {}", name)
    }
}

impl Interpreter {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn eval_stmt(&mut self, stmt: &Stmt) -> Result<()> {
        match stmt {
            Stmt::Print(expr) => {
                let val = self.eval_expr(expr)?;
                println!("{}", val);
            }
            Stmt::Expr(expr) => {
                self.eval_expr(expr)?;
            }
            Stmt::Let(name, init) => {
                self.env.declare(name);
                if let Some(init) = init {
                    let val = self.eval_expr(init)?;
                    self.env.define(name, val)?;
                }
            }
            Stmt::Assign(name, expr) => {
                let value = self.eval_expr(expr)?;
                self.env.define(name, value)?;
            }
            Stmt::Block(stmts) => {
                self.execute_block(stmts)?;
            }
            Stmt::If(cond, then, else_branch) => {
                if let Lit::Bool(b) = self.eval_expr(cond)? {
                    if b {
                        self.execute_block(then)?;
                    } else {
                        self.execute_block(else_branch)?;
                    }
                } else {
                    bail!("condition must be a boolean expression");
                }
            }
        }
        Ok(())
    }

    pub fn eval_expr(&mut self, expr: &Expr) -> Result<Lit> {
        match expr {
            Expr::Binary(op, left, right) => {
                let left = self.eval_expr(left)?;
                let right = self.eval_expr(right)?;
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
            Expr::Literal(lit) => Ok(lit.clone()),
            Expr::Unary(op, expr) => {
                let val = self.eval_expr(expr)?;
                match op {
                    UnOp::Not => {
                        if let Lit::Bool(v) = val {
                            Ok(Lit::Bool(!v))
                        } else {
                            bail!("Not a boolean")
                        }
                    }
                    UnOp::Neg => {
                        if let Lit::Number(n) = val {
                            Ok(Lit::Number(-n))
                        } else {
                            bail!("Not a number")
                        }
                    }
                }
            }
            Expr::Variable(name) => self.env.get(name.symbol).map(|t| t.clone()),
        }
    }

    fn execute_block(&mut self, stmts: &[Stmt]) -> Result<()> {
        self.env.enter_scope();

        struct Guard<'a>(&'a mut Interpreter);
        impl Drop for Guard<'_> {
            fn drop(&mut self) {
                self.0.env.exit_scope();
            }
        }

        let guard = Guard(self);
        for s in stmts {
            guard.0.eval_stmt(s)?;
        }
        Ok(())
    }
}
