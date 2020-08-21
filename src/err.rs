use crate::token::Span;
use std::{cell::Cell, rc::Rc};

pub type Result<T> = anyhow::Result<T>;

pub struct Handler {
    src: Rc<String>,
    had_errors: Cell<bool>,
}

impl Handler {
    pub fn new(src: &Rc<String>) -> Self {
        Self {
            src: src.clone(),
            had_errors: Cell::new(false),
        }
    }

    pub fn report(&self, mut span: Span, msg: &str) {
        self.had_errors.set(true);

        if span.hi >= self.src.len() {
            span = Span {
                lo: self.src.len() - 1,
                hi: self.src.len(),
            };
        }

        let lo = self.line_start(span);
        let hi = self.line_end(span);
        let line = &self.src[lo..hi];
        println!("{}", line);
        println!(
            "{}{} {}",
            " ".repeat(span.lo - lo),
            "^".repeat(span.hi.min(hi) - span.lo),
            msg
        );
    }

    pub fn has_errors(&self) -> bool {
        self.had_errors.get()
    }

    fn line_start(&self, span: Span) -> usize {
        let mut i = span.lo;
        while i > 0 && self.src.as_bytes()[i] != b'\n' {
            i -= 1;
        }
        i
    }

    fn line_end(&self, span: Span) -> usize {
        let mut i = span.lo;
        while i < self.src.len() && self.src.as_bytes()[i] != b'\n' {
            i += 1;
        }
        i
    }
}
