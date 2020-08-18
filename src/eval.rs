use crate::{
    ast::{BinOp, Expr, Lit, Stmt, UnOp},
    err::Result,
    symbol::Symbol,
    token::Token,
};
use std::{collections::HashMap, mem};

macro_rules! bin_op {
    ($self:expr, $a:expr, $op:tt, $b:expr, $msg:literal) => {{
        let left = $self.eval_expr($a)?;
        let right = $self.eval_expr($b)?;
        match (left, right) {
            (Lit::Number(a), Lit::Number(b)) => Ok(Lit::Number(a $op b)),
            _ => bail!($msg),
        }
    }};
}

macro_rules! bin_cmp_op {
    ($self:expr, $a:expr, $op:tt, $b:expr, $msg:literal) => {{
        let left = $self.eval_expr($a)?;
        let right = $self.eval_expr($b)?;
        match (left, right) {
            (Lit::Number(a), Lit::Number(b)) => Ok(Lit::Bool(a $op b)),
            _ => bail!($msg),
        }
    }};
}

macro_rules! bin_logic_op {
    ($self:expr, $a:expr, $op:tt, $b:expr) => {
        Ok(Lit::Bool(
            get!($self.eval_expr($a)?, Bool) $op get!($self.eval_expr($b)?, Bool),
        ))
    };
}

macro_rules! get {
    ($expr:expr, $pat:ident) => {
        match $expr {
            Lit::$pat(b) => b,
            _ => bail!("value must be a {} expression", stringify!($pat)),
        }
    };
}

#[derive(Default)]
pub struct Interpreter {
    env: Env,
}

type Scope = HashMap<Symbol, Option<Lit>>;

#[derive(Default)]
pub struct Env {
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

    pub fn declare(&mut self, name: &Token) {
        self.current.insert(name.symbol, None);
    }

    pub fn define(&mut self, name: &Token, value: Lit) -> Result<()> {
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
            Stmt::Function(fun) => {
                self.env.declare(&fun.name);
                self.env.define(&fun.name, Lit::Callable(fun.clone()))?;
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
            Stmt::Loop(body) => loop {
                if let Err(e) = self.execute_block(body) {
                    match &e.to_string()[..] {
                        "break" => break,
                        "continue" => continue,
                        _ => return Err(e),
                    }
                }
            },
            Stmt::Assign(name, expr) => {
                let value = self.eval_expr(expr)?;
                self.env.define(name, value)?;
            }
            Stmt::Block(stmts) => {
                self.execute_block(stmts)?;
            }
            Stmt::Break => bail!("break"),
            Stmt::Continue => bail!("continue"),
            Stmt::If(cond, then, else_branch) => {
                if get!(self.eval_expr(cond)?, Bool) {
                    self.execute_block(then)?;
                } else {
                    self.execute_block(else_branch)?;
                }
            }
        }
        Ok(())
    }

    pub fn eval_expr(&mut self, expr: &Expr) -> Result<Lit> {
        match expr {
            Expr::Binary(op, left, right) => match op {
                BinOp::Add => bin_op!(self, left, +, right, "Can only add numbers"),
                BinOp::Sub => bin_op!(self, left, -, right, "Can only subtract numbers"),
                BinOp::Mul => bin_op!(self, left, *, right, "Can only multiply numbers"),
                BinOp::Div => bin_op!(self, left, /, right, "Can only divide numbers"),
                BinOp::Rem => bin_op!(self, left, %, right, "Can only divide numbers"),
                BinOp::Gt => bin_cmp_op!(self, left, >, right, "Can only compare numbers"),
                BinOp::Lt => bin_cmp_op!(self, left, <, right, "Can only compare numbers"),
                BinOp::Ge => bin_cmp_op!(self, left, >=, right, "Can only compare numbers"),
                BinOp::Le => bin_cmp_op!(self, left, <=, right, "Can only compare numbers"),
                BinOp::Ne => bin_cmp_op!(self, left, !=, right, "Can only compare numbers"),
                BinOp::Eq => bin_cmp_op!(self, left, ==, right, "Can only compare numbers"),
                BinOp::And => bin_logic_op!(self, left, &&, right),
                BinOp::Or => bin_logic_op!(self, left, ||, right),
            },
            Expr::Grouping(expr) => self.eval_expr(expr),
            Expr::Literal(lit) => Ok(lit.clone()),
            Expr::Unary(op, expr) => {
                let val = self.eval_expr(expr)?;
                match op {
                    UnOp::Not => Ok(Lit::Bool(!get!(val, Bool))),
                    UnOp::Neg => Ok(Lit::Number(-get!(val, Number))),
                }
            }
            Expr::Variable(name) => self.env.get(name.symbol).map(|t| t.clone()),
            Expr::Call(callee, _paren, args) => {
                let callee = get!(self.eval_expr(callee)?, Callable);
                ensure!(
                    callee.arity() == args.len(),
                    "Expected {} arguments but got {}.",
                    callee.arity(),
                    args.len()
                );

                let mut actual_args = vec![];
                for arg in args {
                    actual_args.push(self.eval_expr(arg)?);
                }
                callee.call(self, actual_args)
            }
        }
    }

    pub fn execute_block(&mut self, stmts: &[Stmt]) -> Result<()> {
        self.execute_block_with(stmts, |_| Ok(()))
    }

    pub fn execute_block_with<F>(&mut self, stmts: &[Stmt], mut f: F) -> Result<()>
    where
        F: FnMut(&mut Env) -> Result<()>,
    {
        self.env.enter_scope();

        struct Guard<'a>(&'a mut Interpreter);
        impl Drop for Guard<'_> {
            fn drop(&mut self) {
                self.0.env.exit_scope();
            }
        }
        let guard = Guard(self);
        f(&mut guard.0.env)?;

        for s in stmts {
            guard.0.eval_stmt(s)?;
        }
        Ok(())
    }
}
