use crate::lex::Spanned;

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

#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum Ty {
    Var(u64),
    Unit,
    Bool,
    Int,
    Float,
    Str,
    Fn(Vec<Spanned<Ty>>, Box<Spanned<Ty>>),
}
