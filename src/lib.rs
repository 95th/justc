use crate::typeck::Typeck;

use self::{
    err::{ErrHandler, Result},
    parse::Parser,
};
use std::rc::Rc;
pub use util::Args;

mod err;
mod lex;
mod parse;
mod symbol;
mod typeck;
mod util;

#[derive(Default)]
pub struct Compiler {}

impl Compiler {
    pub fn new() -> Self {
        Self {}
    }

    pub fn run(&mut self, src: String) -> Result<()> {
        let src = Rc::from(src);
        let handler = Rc::new(ErrHandler::new(&src));
        let ast = Parser::new(src, &handler).parse()?;
        Typeck::new(&handler).typeck(&ast)?;
        Ok(())
    }
}
