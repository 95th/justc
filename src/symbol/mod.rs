mod interner;
mod table;

use std::cell::RefCell;
use std::{fmt, str::FromStr};

use self::interner::Interner;
pub use self::table::SymbolTable;

fn with_interner<T>(f: impl FnOnce(&mut Interner) -> T) -> T {
    thread_local! {
        static INTERNER: RefCell<Interner> = RefCell::new(Interner::default());
    }

    INTERNER.with(|i| f(&mut *i.borrow_mut()))
}

#[derive(Copy, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct Symbol(u32);

impl Symbol {
    pub fn intern(s: &str) -> Self {
        with_interner(|interner| interner.intern(s))
    }

    pub fn parse<T: FromStr>(&self) -> Result<T, T::Err> {
        with_interner(|interner| interner.lookup(self.0).parse())
    }

    pub fn as_str_with<T>(&self, f: impl FnOnce(&str) -> T) -> T {
        with_interner(|interner| f(interner.lookup(self.0)))
    }
}

impl fmt::Debug for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        with_interner(|interner| f.write_str(interner.lookup(self.0)))
    }
}
