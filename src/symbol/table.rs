use crate::symbol::Symbol;
use std::collections::HashMap;

pub struct SymbolTable<T> {
    current: HashMap<Symbol, T>,
    outer: Vec<HashMap<Symbol, T>>,
}

impl<T> Default for SymbolTable<T> {
    fn default() -> Self {
        Self {
            current: Default::default(),
            outer: Default::default(),
        }
    }
}

impl<T> SymbolTable<T> {
    pub fn enter_scope(&mut self) {
        let old = std::mem::take(&mut self.current);
        self.outer.push(old);
    }

    pub fn exit_scope(&mut self) {
        self.current = self.outer.pop().unwrap();
    }

    pub fn add(&mut self, sym: Symbol, val: T) {
        self.current.insert(sym, val);
    }

    pub fn check_scope(&self, sym: &Symbol) -> bool {
        self.current.contains_key(sym)
    }

    pub fn find(&self, sym: &Symbol) -> Option<&T> {
        if let Some(t) = self.current.get(sym) {
            return Some(t);
        }

        for scope in self.outer.iter().rev() {
            if let Some(t) = scope.get(sym) {
                return Some(t);
            }
        }

        None
    }
}
