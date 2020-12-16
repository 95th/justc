use crate::symbol::Symbol;
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq)]
pub struct SymbolTable<T> {
    map: HashMap<Symbol, T>,
    changes: Vec<(Symbol, Option<T>)>,
}

impl<T> Default for SymbolTable<T> {
    fn default() -> Self {
        Self {
            map: HashMap::new(),
            changes: vec![],
        }
    }
}

pub struct UndoLog {
    undo_len: usize,
}

impl<T> SymbolTable<T> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn insert(&mut self, key: Symbol, value: T) {
        let old = self.map.insert(key, value);
        self.changes.push((key, old));
    }

    pub fn get(&self, key: Symbol) -> Option<&T> {
        self.map.get(&key)
    }

    pub fn is_defined(&self, key: Symbol) -> bool {
        self.map.contains_key(&key)
    }

    pub fn snapshot(&self) -> UndoLog {
        UndoLog {
            undo_len: self.changes.len(),
        }
    }

    pub fn rollback(&mut self, savepoint: UndoLog) {
        while self.changes.len() > savepoint.undo_len {
            let (k, old) = self.changes.pop().unwrap();
            match old {
                Some(v) => self.map.insert(k, v),
                None => self.map.remove(&k),
            };
        }
    }
}
