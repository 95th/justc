use crate::symbol::Symbol;
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq)]
pub struct SymbolTable<T> {
    map: HashMap<Symbol, T>,
    changes: Vec<(Symbol, Option<T>)>,
}

impl<T> SymbolTable<T> {
    pub fn new() -> Self {
        Self {
            map: HashMap::new(),
            changes: vec![],
        }
    }

    pub fn insert(&mut self, key: Symbol, value: T) {
        let old = self.map.insert(key, value);
        self.changes.push((key, old));
    }

    pub fn get(&self, key: Symbol) -> Option<&T> {
        self.map.get(&key)
    }

    pub fn enter_scope<F, R>(&mut self, f: F) -> R
    where
        F: FnOnce(&mut Self) -> R,
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
