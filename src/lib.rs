use self::{err::Handler, parse::Parser};
use std::rc::Rc;
use symbol::SymbolTable;
use typeck::TyCtxt;
pub use util::Args;

mod err;
mod lex;
mod parse;
mod symbol;
mod typeck;
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

        let bindings = &mut SymbolTable::new();
        let tcx = &mut TyCtxt::new(&handler);
        tcx.check_stmts(&stmts, bindings);

        if handler.has_errors() {
            return;
        }
    }
}
