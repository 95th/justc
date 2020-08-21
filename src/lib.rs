#[macro_use]
extern crate anyhow;

use self::{err::Handler, parse::Parser};
use std::rc::Rc;
use typeck::TyContext;

pub mod args;
mod ast;
mod err;
mod eval;
mod parse;
mod scan;
mod symbol;
mod token;
mod typeck;

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

        let mut ctx = TyContext::default();
        for s in &stmts {
            if let Err(e) = ctx.type_check_stmt(s) {
                println!("{}", e);
                return;
            }
        }

        if handler.has_errors() {
            return;
        }
    }
}
