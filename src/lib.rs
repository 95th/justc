use self::{err::Handler, parse::Parser, scan::Scanner};

pub mod args;
mod ast;
mod err;
mod eval;
mod parse;
mod scan;
mod token;

pub struct Compiler {
    handler: Handler,
}

impl Compiler {
    pub fn new() -> Self {
        Self {
            handler: Handler::new(),
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

        for t in &tokens {
            println!("{:#?}", t);
        }

        let mut parser = Parser::new(&source, tokens, &mut self.handler);
        let expr = match parser.parse() {
            Ok(t) => t,
            Err(e) => {
                println!("{}", e);
                return;
            }
        };

        println!("{:?}", expr);
    }
}
