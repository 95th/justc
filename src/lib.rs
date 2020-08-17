use self::{err::Handler, parse::Parser, scan::Scanner};
use eval::Interpreter;

pub mod args;
mod ast;
mod err;
mod eval;
mod parse;
mod scan;
mod symbol;
mod token;

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

        if self.handler.has_errors() {
            return;
        }

        for s in &stmts {
            self.interpreter.eval_stmt(s);
        }
    }
}
