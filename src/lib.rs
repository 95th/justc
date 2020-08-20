#[macro_use]
extern crate anyhow;

use self::{err::Handler, parse::Parser, scan::Scanner};
use eval::Interpreter;
use typeck::TyEnv;

pub mod args;
mod ast;
mod err;
mod eval;
mod parse;
mod scan;
mod symbol;
mod token;
mod typeck;

pub struct Compiler {
    handler: Handler,
    interpreter: Interpreter,
}

impl Compiler {
    pub fn new() -> Self {
        Self {
            handler: Handler::new(),
            interpreter: Interpreter::new(),
        }
    }

    pub fn run(&mut self, source: String) {
        self.handler.reset();
        let scanner = Scanner::new(&source, &mut self.handler);
        let tokens = match scanner.scan_tokens() {
            Ok(t) => t,
            Err(e) => {
                println!("{}", e);
                return;
            }
        };

        let mut parser = Parser::new(tokens, &mut self.handler);
        let stmts = parser.parse();

        let mut env = TyEnv::default();
        for s in &stmts {
            if let Err(e) = env.type_check_stmt(s) {
                println!("{}", e);
                return;
            }
        }

        if self.handler.has_errors() {
            return;
        }

        for s in &stmts {
            if let Err(e) = self.interpreter.eval_stmt(s) {
                println!("{}", e);
                break;
            }
        }
    }
}
