use std::{collections::BTreeMap, fmt};

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

#[derive(Clone)]
pub enum Ty {
    Var(u64),
    Unit,
    Bool,
    Int,
    Float,
    Str,
    Fn(Vec<Spanned<Ty>>, Box<Spanned<Ty>>),
    Struct(u64, Symbol, BTreeMap<Symbol, Spanned<Ty>>),
}

impl Ty {
    pub fn tvar(&self) -> Option<u64> {
        match self {
            Ty::Var(v) | Ty::Struct(v, ..) => Some(*v),
            _ => None,
        }
    }
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
            Ty::Struct(_, name, _) => write!(f, "{}", name)?,
        }
        Ok(())
    }
}

impl PartialEq for Ty {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Ty::Unit, Ty::Unit)
            | (Ty::Bool, Ty::Bool)
            | (Ty::Int, Ty::Int)
            | (Ty::Float, Ty::Float)
            | (Ty::Str, Ty::Str) => true,
            (Ty::Var(a), Ty::Var(b)) => a == b,
            (Ty::Struct(id, _, _), Ty::Struct(id2, _, _)) => id == id2,
            (Ty::Fn(params, ret), Ty::Fn(params2, ret2)) => {
                for (a, b) in params.iter().zip(params2) {
                    if a.val != b.val {
                        return false;
                    }
                }

                ret.val == ret2.val
            }
            _ => false,
        }
    }
}
