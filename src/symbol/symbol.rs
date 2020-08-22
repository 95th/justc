use std::cell::RefCell;
use std::{collections::HashMap, fmt, mem, str::FromStr};

#[derive(Copy, Clone, Eq, PartialEq, Hash)]
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

fn with_interner<T>(f: impl FnOnce(&mut Interner) -> T) -> T {
    thread_local! {
        static INTERNER: RefCell<Interner> = RefCell::new(Interner::default());
    }

    INTERNER.with(|i| f(&mut *i.borrow_mut()))
}

#[derive(Default)]
pub struct Interner {
    map: HashMap<&'static str, Symbol>,
    vec: Vec<&'static str>,
    buf: String,
    full: Vec<String>,
}

impl Interner {
    fn intern(&mut self, name: &str) -> Symbol {
        if let Some(&id) = self.map.get(name) {
            return id;
        }
        let name = unsafe { self.alloc(name) };
        let id = Symbol(self.map.len() as u32);
        self.map.insert(name, id);
        self.vec.push(name);

        debug_assert!(self.lookup(id.0) == name);
        debug_assert!(self.intern(name) == id);
        id
    }

    pub fn lookup(&self, id: u32) -> &str {
        self.vec[id as usize]
    }

    unsafe fn alloc(&mut self, name: &str) -> &'static str {
        let cap = self.buf.capacity();
        if cap < self.buf.len() + name.len() {
            let new_cap = (cap.max(name.len()) + 1).next_power_of_two();
            let new_buf = String::with_capacity(new_cap);
            let old_buf = mem::replace(&mut self.buf, new_buf);
            self.full.push(old_buf);
        }

        let interned = {
            let start = self.buf.len();
            self.buf.push_str(name);
            &self.buf[start..]
        };

        &*(interned as *const str)
    }
}
