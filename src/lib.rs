use self::{err::Handler, parse::Parser};
use std::rc::Rc;
pub use util::Args;

mod err;
mod lex;
mod parse;
mod symbol;
mod util;

pub struct Compiler {}

impl Compiler {
    pub fn new() -> Self {
        Self {}
    }

    pub fn run(&mut self, src: String) {
        let src = Rc::new(src);
        let handler = Rc::new(Handler::new(&src));
        let mut parser = Parser::new(src, &handler);
        let stmts = match parser.parse() {
            Some(t) => t,
            None => return,
        };

        dbg!(stmts);

        if handler.has_errors() {
            return;
        }
    }
}
