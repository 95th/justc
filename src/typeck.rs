use crate::{
    err::Result,
    parse::ast::{BinOp, Expr, FloatTy, Lit, Stmt, Ty, UnOp},
    symbol::SymbolTable,
    util::OnDrop,
};

#[derive(Default)]
pub struct TyContext {
    table: SymbolTable<Ty>,
}

impl TyContext {
    pub fn type_check_stmt(&mut self, stmt: &Stmt) -> Result<()> {
        match stmt {
            Stmt::Expr(expr) => {
                self.type_check(expr)?;
            }
            Stmt::Function(f) => {
                self.execute_block(&f.body)?;
            }
            Stmt::Print(expr) => {
                self.type_check(expr)?;
            }
            Stmt::Let { init, ty, name } => {
                if let Some(init) = init {
                    let t = self.type_check(init)?;
                    if let Some(ty) = ty {
                        ensure!(t == *ty, "Type mismatch in let");
                    }
                    self.table.add(name.symbol, t);
                }
            }
            Stmt::Loop(body) | Stmt::Block(body) => {
                self.execute_block(body)?;
            }
            Stmt::Assign { name, val } => {
                let t = self.type_check(val)?;
                if let Some(ty) = self.table.find(&name.symbol) {
                    ensure!(ty == &t, "Type mismatch in assignment");
                } else {
                    bail!("Undeclared variable '{}'", name.symbol);
                }
            }
            Stmt::If {
                cond,
                then_branch,
                else_branch,
            } => {
                self.type_check(cond)?;
                self.execute_block(then_branch)?;
                self.execute_block(else_branch)?;
            }
            Stmt::Break => {}
            Stmt::Continue => {}
        }
        Ok(())
    }

    fn execute_block(&mut self, stmts: &[Stmt]) -> Result<()> {
        let mut this = OnDrop::new(self, |this| this.table.exit_scope());
        this.table.enter_scope();
        for s in stmts {
            this.type_check_stmt(s)?;
        }
        Ok(())
    }

    pub fn type_check(&mut self, expr: &Expr) -> Result<Ty> {
        match expr {
            Expr::Binary { op, left, right } => {
                let t1 = self.type_check(left)?;
                let t2 = self.type_check(right)?;
                ensure!(t1 == t2, "Types of operands must match");
                match op {
                    BinOp::Add
                    | BinOp::Sub
                    | BinOp::Mul
                    | BinOp::Div
                    | BinOp::Rem
                    | BinOp::Lt
                    | BinOp::Gt
                    | BinOp::Le
                    | BinOp::Ge => match t1 {
                        Ty::Int(_) | Ty::Float(_) => Ok(t1),
                        _ => bail!("Incompatible operand type"),
                    },
                    BinOp::Ne | BinOp::Eq => match t1 {
                        Ty::Int(_) | Ty::Float(_) | Ty::Bool | Ty::String => Ok(t1),
                        _ => bail!("Incompatible operand type"),
                    },
                    BinOp::And | BinOp::Or => match t1 {
                        Ty::Bool => Ok(t1),
                        _ => bail!("Incompatible operand type for binary op"),
                    },
                }
            }
            Expr::Unary { op, expr } => {
                let t = self.type_check(expr)?;
                match (op, &t) {
                    (UnOp::Not, Ty::Bool) => Ok(t),
                    (UnOp::Neg, Ty::Int(_)) | (UnOp::Neg, Ty::Float(_)) => Ok(t),
                    _ => bail!("Incompatible operand type for unary op"),
                }
            }
            Expr::Literal(lit) => match lit {
                Lit::Str(_) => Ok(Ty::String),
                Lit::Number(_) => Ok(Ty::Float(FloatTy::F64)),
                Lit::Bool(_) => Ok(Ty::Bool),
            },
            _ => todo!(),
        }
    }
}
