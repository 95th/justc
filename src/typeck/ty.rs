use std::{cell::Cell, collections::HashMap, rc::Rc};

use crate::symbol::Symbol;

pub struct TyEnv {
    counter: Rc<Cell<u64>>,
    bindings: HashMap<Symbol, Ty>,
    changes: Vec<(Symbol, Option<Ty>)>,
}

impl TyEnv {
    pub fn new() -> Self {
        Self {
            counter: Rc::new(Cell::new(0)),
            bindings: HashMap::new(),
            changes: vec![],
        }
    }

    pub fn new_var(&mut self) -> Ty {
        let n = self.counter.get();
        self.counter.set(n + 1);
        Ty::Var(n)
    }

    pub fn lookup(&self, key: Symbol) -> Option<&Ty> {
        self.bindings.get(&key)
    }

    pub fn define(&mut self, key: Symbol, ty: Ty) {
        let old = self.bindings.insert(key, ty);
        self.changes.push((key, old));
    }

    pub fn in_scope<F, R>(&mut self, f: F) -> R
    where
        F: FnOnce(&mut Self) -> R,
    {
        let size = self.changes.len();
        let result = f(self);
        self.unwind(size);
        result
    }

    fn unwind(&mut self, upto: usize) {
        while self.changes.len() > upto {
            let (k, v) = self.changes.pop().unwrap();
            match v {
                Some(v) => self.bindings.insert(k, v),
                None => self.bindings.remove(&k),
            };
        }
    }
}

#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub enum Ty {
    Var(u64),
    Unit,
    Bool,
    Int,
    Float,
    Str,
    Fn(Vec<Ty>, Box<Ty>),
}
