use crate::typeck::Typeck;

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

    pub fn run(&mut self, src: String) -> Option<()> {
        let src = Rc::new(src);
        let handler = Rc::new(Handler::new(&src));
        let ast = Parser::new(src, &handler).parse()?;
        Typeck::new(&handler).typeck(ast).ok()?;
        Some(())
    }
}
