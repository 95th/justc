use self::{err::Handler, parse::Parser};
use std::rc::Rc;
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

        let mut stmts = match crate::typeck::annotate::annotate(stmts, &handler) {
            Some(s) => s,
            None => return,
        };

        let constraints = crate::typeck::constraints::collect(&mut stmts);
        let mut constraints = constraints.into_iter().collect::<Vec<_>>();

        let subst = match crate::typeck::unify::unify(&mut constraints, &handler) {
            Some(s) => s,
            None => return,
        };
        dbg!(&subst);

        subst.fill_ast(&mut stmts);
        dbg!(&stmts);

        if handler.has_errors() {
            return;
        }
    }
}
