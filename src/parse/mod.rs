pub mod ast;

use crate::{
    err::Handler,
    lex::{Lexer, LiteralKind, Token, TokenKind, TokenKind::*},
};
use ast::{BinOp, Block, Expr, Lit, LitKind, Stmt, Ty, TyKind, UnOp};
use std::rc::Rc;

pub struct Parser {
    lexer: Lexer,
    handler: Rc<Handler>,
    curr: Token,
    prev: Token,
}

impl Parser {
    pub fn new(src: Rc<String>, handler: &Rc<Handler>) -> Self {
        let mut lexer = Lexer::new(src, handler);
        let curr = lexer.next_token();
        Self {
            lexer,
            handler: handler.clone(),
            curr,
            prev: Token::dummy(),
        }
    }

    pub fn parse(&mut self) -> Option<Vec<Stmt>> {
        let mut stmts = vec![];
        while !self.eof() {
            stmts.push(self.decl()?);
        }
        Some(stmts)
    }

    fn decl(&mut self) -> Option<Stmt> {
        let stmt = if self.eat(Let) {
            self.let_decl()
        } else {
            self.stmt()
        };
        match stmt {
            Some(s) => Some(s),
            None => {
                self.synchronize();
                return None;
            }
        }
    }

    fn stmt(&mut self) -> Option<Stmt> {
        if self.eat(OpenBrace) {
            let block = self.block()?;
            Some(Stmt::Expr(Box::new(Expr::Block(block))))
        } else {
            self.expr_stmt()
        }
    }

    fn block(&mut self) -> Option<Block> {
        let mut stmts = vec![];
        while !self.check(CloseBrace) && !self.eof() {
            if let Some(s) = self.decl() {
                stmts.push(s);
            }
        }
        self.consume(CloseBrace, "Expect '}' after block.")?;
        Some(Block { stmts })
    }

    fn let_decl(&mut self) -> Option<Stmt> {
        let name = self.consume(Ident, "Expect variable name.")?;

        let ty = if self.eat(Colon) {
            Some(self.parse_ty()?)
        } else {
            None
        };

        let mut init = None;
        if self.eat(Eq) {
            init = Some(self.expr()?);
        }

        self.consume(SemiColon, "Expect ';' after variable declaration.")?;
        Some(Stmt::Let { name, ty, init })
    }

    fn expr_stmt(&mut self) -> Option<Stmt> {
        let expr = self.expr()?;

        if self.eat(Eq) {
            let eq = self.prev().clone();
            let val = self.expr()?;

            if let Expr::Variable(name) = *expr {
                self.consume(SemiColon, "Expect ';' after assignment.")?;
                return Some(Stmt::Assign { name, val });
            } else {
                self.handler.report(eq.span, "Invalid assignment target.");
                return None;
            }
        }
        self.consume(SemiColon, "Expect ';' after value.")?;
        Some(Stmt::Expr(expr))
    }

    fn expr(&mut self) -> Option<Box<Expr>> {
        self.logic_or()
    }

    fn logic_or(&mut self) -> Option<Box<Expr>> {
        let mut left = self.logic_and()?;

        while self.eat(Or) {
            let right = self.logic_and()?;
            left = Box::new(Expr::Binary {
                op: BinOp::Or,
                left,
                right,
            });
        }

        Some(left)
    }

    fn logic_and(&mut self) -> Option<Box<Expr>> {
        let mut left = self.equality()?;

        while self.eat(And) {
            let right = self.equality()?;
            left = Box::new(Expr::Binary {
                op: BinOp::And,
                left,
                right,
            });
        }

        Some(left)
    }

    fn equality(&mut self) -> Option<Box<Expr>> {
        let mut left = self.comparison()?;

        loop {
            let op = if self.eat(Ne) {
                BinOp::Ne
            } else if self.eat(EqEq) {
                BinOp::Eq
            } else {
                break;
            };
            let right = self.comparison()?;
            left = Box::new(Expr::Binary { op, left, right });
        }

        Some(left)
    }

    fn comparison(&mut self) -> Option<Box<Expr>> {
        let mut left = self.addition()?;

        loop {
            let op = if self.eat(Gt) {
                BinOp::Gt
            } else if self.eat(Ge) {
                BinOp::Ge
            } else if self.eat(Lt) {
                BinOp::Lt
            } else if self.eat(Le) {
                BinOp::Le
            } else {
                break;
            };
            let right = self.addition()?;
            left = Box::new(Expr::Binary { op, left, right });
        }

        Some(left)
    }

    fn addition(&mut self) -> Option<Box<Expr>> {
        let mut left = self.multiplication()?;

        loop {
            let op = if self.eat(Minus) {
                BinOp::Sub
            } else if self.eat(Plus) {
                BinOp::Add
            } else {
                break;
            };
            let right = self.multiplication()?;
            left = Box::new(Expr::Binary { op, left, right });
        }

        Some(left)
    }

    fn multiplication(&mut self) -> Option<Box<Expr>> {
        let mut left = self.unary()?;

        loop {
            let op = if self.eat(Slash) {
                BinOp::Div
            } else if self.eat(Star) {
                BinOp::Mul
            } else if self.eat(Percent) {
                BinOp::Rem
            } else {
                break;
            };
            let right = self.unary()?;
            left = Box::new(Expr::Binary { op, left, right });
        }

        Some(left)
    }

    fn unary(&mut self) -> Option<Box<Expr>> {
        let op = if self.eat(Not) {
            UnOp::Not
        } else if self.eat(Minus) {
            UnOp::Neg
        } else {
            return self.primary();
        };

        let expr = self.unary()?;
        Some(Box::new(Expr::Unary { op, expr }))
    }

    fn primary(&mut self) -> Option<Box<Expr>> {
        let lit = if self.eat(False) {
            Lit {
                kind: LitKind::Bool(false),
                span: self.prev().span,
            }
        } else if self.eat(True) {
            Lit {
                kind: LitKind::Bool(true),
                span: self.prev().span,
            }
        } else if self.eat(Literal {
            kind: LiteralKind::Int,
        }) {
            let token = self.prev();
            let kind = token
                .symbol
                .parse()
                .map(LitKind::Integer)
                .unwrap_or(LitKind::Err);
            Lit {
                kind,
                span: token.span,
            }
        } else if self.eat(Literal {
            kind: LiteralKind::Float,
        }) {
            let token = self.prev();
            Lit {
                kind: LitKind::Float(token.symbol),
                span: token.span,
            }
        } else if self.eat(Literal {
            kind: LiteralKind::Str,
        }) {
            let token = self.prev();
            Lit {
                kind: LitKind::Str(token.symbol),
                span: token.span,
            }
        } else if self.eat(Ident) {
            return Some(Box::new(Expr::Variable(self.prev().clone())));
        } else if self.eat(OpenParen) {
            let expr = self.expr()?;
            self.consume(CloseParen, "Expect ')' after expr")?;
            return Some(Box::new(Expr::Grouping(expr)));
        } else if self.eat(OpenBrace) {
            let block = self.block()?;
            return Some(Box::new(Expr::Block(block)));
        } else {
            self.handler.report(self.peek().span, "Expected expression");
            return None;
        };

        Some(Box::new(Expr::Literal(lit)))
    }

    fn parse_ty(&mut self) -> Option<Ty> {
        let token = self.consume(Ident, "Expect Type name")?;
        let span = token.span;

        let kind = match &token.symbol.to_string()[..] {
            "_" => TyKind::Infer,
            "i16" => TyKind::Ident(token),
            _ => {
                self.handler.report(token.span, "Unknown type");
                TyKind::Err
            }
        };

        Some(Ty { span, kind })
    }

    fn synchronize(&mut self) {
        self.advance();
        while !self.eof() {
            match self.prev().kind {
                SemiColon => return,
                Struct | Fn | Let | For | If | While | Return => return,
                _ => self.advance(),
            }
        }
    }

    fn consume(&mut self, kind: TokenKind, msg: &'static str) -> Option<Token> {
        if self.check(kind) {
            self.advance();
            return Some(self.prev().clone());
        }

        self.handler.report(self.peek().span, msg);
        None
    }

    fn eat(&mut self, kind: TokenKind) -> bool {
        if self.check(kind) {
            self.advance();
            true
        } else {
            false
        }
    }

    fn check(&self, kind: TokenKind) -> bool {
        self.peek().kind == kind
    }

    fn peek(&self) -> &Token {
        &self.curr
    }

    fn prev(&self) -> &Token {
        &self.prev
    }

    fn advance(&mut self) {
        self.prev = std::mem::replace(&mut self.curr, self.lexer.next_token())
    }

    fn eof(&self) -> bool {
        self.peek().kind == Eof
    }
}
