use crate::lex::Span;
use std::{cell::Cell, rc::Rc};

pub type Result<T> = std::result::Result<T, ()>;

#[derive(Debug)]
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

    pub fn mk_err<T>(&self, span: Span, msg: &str) -> Result<T> {
        self.report(span, msg);
        Err(())
    }

    pub fn report(&self, mut span: Span, msg: &str) {
        self.had_errors.set(true);

        let orig_span = span;
        if span.lo() >= self.src.len() {
            span = Span::new(self.src.len() - 1, self.src.len());
        }

        let lo = self.line_start(span);
        let hi = self.line_end(span);
        let line = &self.src[lo..hi];
        println!("{}", line);

        let blank: String = line
            .chars()
            .take(orig_span.lo() - lo)
            .map(|c| if c == '\t' { '\t' } else { ' ' })
            .collect();
        println!("{}{} {}", blank, "^".repeat(span.hi().min(hi) - span.lo()), msg);
    }

    pub fn has_errors(&self) -> bool {
        self.had_errors.get()
    }

    fn line_start(&self, span: Span) -> usize {
        self.src[..span.lo()].rfind('\n').map(|i| i + 1).unwrap_or(0)
    }

    fn line_end(&self, span: Span) -> usize {
        self.src[span.lo()..]
            .find('\n')
            .map(|i| span.lo() + i)
            .unwrap_or_else(|| self.src.len())
    }
}
