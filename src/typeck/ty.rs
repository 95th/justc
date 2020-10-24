use std::{collections::HashMap, fmt};

use crate::{lex::Spanned, symbol::Symbol};

pub struct TyContext {
    counter: u64,
}

impl TyContext {
    pub fn new() -> Self {
        Self { counter: 0 }
    }

    pub fn new_var(&mut self) -> Ty {
        let n = self.counter;
        self.counter += 1;
        Ty::Var(n)
    }
}

#[derive(Clone, PartialEq)]
pub enum Ty {
    Var(u64),
    Unit,
    Bool,
    Int,
    Float,
    Str,
    Fn(Vec<Spanned<Ty>>, Box<Spanned<Ty>>),
    Struct(Symbol, HashMap<Symbol, Spanned<Ty>>),
}

impl fmt::Debug for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Ty::Var(n) => write!(f, "{{unknown {}}}", n)?,
            Ty::Unit => f.write_str("unit")?,
            Ty::Bool => f.write_str("bool")?,
            Ty::Int => f.write_str("int")?,
            Ty::Float => f.write_str("float")?,
            Ty::Str => f.write_str("str")?,
            Ty::Fn(params, ret) => {
                f.write_str("fn(")?;
                let mut first = true;
                for p in params {
                    if first {
                        first = false;
                    } else {
                        f.write_str(", ")?;
                    }
                    write!(f, "{:?}", p.val)?;
                }
                f.write_str(")")?;
                match &ret.val {
                    Ty::Unit => {}
                    ty => write!(f, " -> {:?}", ty)?,
                }
            }
            Ty::Struct(name, fields) => {
                write!(f, "struct {} {{", name)?;
                for (name, ty) in fields {
                    write!(f, " {}: {:?},", name, ty.val)?;
                }
                write!(f, " }}")?;
            }
        }
        Ok(())
    }
}
