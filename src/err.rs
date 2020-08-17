use crate::token::Token;
use std::fmt::Display;

pub type Result<T> = anyhow::Result<T>;

pub struct Handler {
    had_errors: bool,
}

impl Handler {
    pub fn new() -> Self {
        Self { had_errors: false }
    }

    pub fn with_token<T>(&mut self, token: Option<&Token>, msg: &'static str) -> Result<T> {
        if let Some(t) = token {
            self.report(t.line, format!(" at '{}'", t.symbol), msg);
        } else {
            self.report(0, " at the end", msg);
        }

        bail!(msg)
    }

    pub fn error(&mut self, line: usize, err: impl Display) {
        self.report(line, "", err);
    }

    pub fn report(&mut self, line: usize, location: impl Display, err: impl Display) {
        println!("[line {}] Error {}: {}", line, location, err);
        self.had_errors = true;
    }

    pub fn has_errors(&self) -> bool {
        self.had_errors
    }

    pub fn reset(&mut self) {
        self.had_errors = false;
    }
}
