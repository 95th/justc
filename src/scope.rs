use crate::{symbol::Symbol, typeck::Ty};
use std::collections::HashMap;

pub struct Bindings {
    map: HashMap<Symbol, Ty>,
    changes: Vec<(Symbol, Option<Ty>)>,
}

impl Bindings {
    pub fn new() -> Self {
        Self {
            map: HashMap::new(),
            changes: vec![],
        }
    }

    pub fn insert(&mut self, key: Symbol, value: Ty) {
        let old = self.map.insert(key, value);
        self.changes.push((key, old));
    }

    pub fn get(&self, key: &Symbol) -> Option<Ty> {
        self.map.get(key).copied()
    }

    pub fn enter<F, T>(&mut self, f: F) -> T
    where
        F: FnOnce(&mut Self) -> T,
    {
        let initial_len = self.changes.len();
        let result = f(self);
        self.unwind(initial_len);
        result
    }

    fn unwind(&mut self, upto: usize) {
        while self.changes.len() > upto {
            let (k, old) = self.changes.pop().unwrap();
            match old {
                Some(v) => self.map.insert(k, v),
                None => self.map.remove(&k),
            };
        }
    }
}
