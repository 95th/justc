use crate::{
    ast::{BinOp, Expr, Lit, UnOp},
    err::{Handler, Result},
    token::{Token, TokenKind},
};

pub struct Parser<'a> {
    src: &'a str,
    tokens: Vec<Token>,
    handler: &'a mut Handler,
    pos: usize,
}

impl<'a> Parser<'a> {
    pub fn new(src: &'a str, tokens: Vec<Token>, handler: &'a mut Handler) -> Self {
        Self {
            src,
            tokens,
            handler,
            pos: 0,
        }
    }

    pub fn parse(&mut self) -> Result<Box<Expr>> {
        match self.expr() {
            Ok(t) => Ok(t),
            Err(e) => {
                self.synchronize();
                return Err(e);
            }
        }
    }

    pub fn expr(&mut self) -> Result<Box<Expr>> {
        self.equality()
    }

    fn equality(&mut self) -> Result<Box<Expr>> {
        let mut expr = self.comparison()?;

        loop {
            let op = if self.eat(TokenKind::Ne) {
                BinOp::Ne
            } else if self.eat(TokenKind::EqEq) {
                BinOp::Eq
            } else {
                break;
            };
            let right = self.comparison()?;
            expr = Box::new(Expr::Binary(op, expr, right));
        }

        Ok(expr)
    }

    fn comparison(&mut self) -> Result<Box<Expr>> {
        let mut expr = self.addition()?;

        loop {
            let op = if self.eat(TokenKind::Gt) {
                BinOp::Gt
            } else if self.eat(TokenKind::Ge) {
                BinOp::Ge
            } else if self.eat(TokenKind::Lt) {
                BinOp::Lt
            } else if self.eat(TokenKind::Le) {
                BinOp::Le
            } else {
                break;
            };
            let right = self.addition()?;
            expr = Box::new(Expr::Binary(op, expr, right));
        }

        Ok(expr)
    }

    fn addition(&mut self) -> Result<Box<Expr>> {
        let mut expr = self.multiplication()?;

        loop {
            let op = if self.eat(TokenKind::Minus) {
                BinOp::Sub
            } else if self.eat(TokenKind::Plus) {
                BinOp::Add
            } else {
                break;
            };
            let right = self.multiplication()?;
            expr = Box::new(Expr::Binary(op, expr, right));
        }

        Ok(expr)
    }

    fn multiplication(&mut self) -> Result<Box<Expr>> {
        let mut expr = self.unary()?;

        loop {
            let op = if self.eat(TokenKind::Slash) {
                BinOp::Div
            } else if self.eat(TokenKind::Star) {
                BinOp::Mul
            } else {
                break;
            };
            let right = self.unary()?;
            expr = Box::new(Expr::Binary(op, expr, right));
        }

        Ok(expr)
    }

    fn unary(&mut self) -> Result<Box<Expr>> {
        let op = if self.eat(TokenKind::Not) {
            UnOp::Not
        } else if self.eat(TokenKind::Minus) {
            UnOp::Neg
        } else {
            return self.primary();
        };

        let expr = self.unary()?;
        Ok(Box::new(Expr::Unary(op, expr)))
    }

    fn primary(&mut self) -> Result<Box<Expr>> {
        let lit = if self.eat(TokenKind::False) {
            Lit::Bool(false)
        } else if self.eat(TokenKind::True) {
            Lit::Bool(true)
        } else if self.eat(TokenKind::Num) {
            let token = self.prev().unwrap();
            let s = &self.src[token.span.range()];
            let val = s.parse().unwrap();
            Lit::Number(val)
        } else if self.eat(TokenKind::Str) {
            let token = self.prev().unwrap();
            let val = &self.src[token.span.lo + 1..token.span.hi - 1];
            Lit::Str(val.to_owned())
        } else if self.eat(TokenKind::OpenParen) {
            let expr = self.expr()?;
            self.consume(TokenKind::CloseParen, "Expect ')' after expr")?;
            return Ok(Box::new(Expr::Grouping(expr)));
        } else {
            return self.handler.with_token(
                self.tokens.get(self.pos),
                self.src,
                "Expected expression",
            );
        };

        Ok(Box::new(Expr::Literal(lit)))
    }

    fn synchronize(&mut self) {
        use TokenKind::*;
        self.advance();
        while let Some(t) = self.peek() {
            match t.kind {
                SemiColon => return,
                Struct | Fn | Let | For | If | While | Return => return,
                _ => self.advance(),
            }
        }
    }

    fn consume(&mut self, kind: TokenKind, msg: &'static str) -> Result<()> {
        if self.check(kind) {
            self.advance();
            return Ok(());
        }

        return Err(msg);
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
        matches!(self.peek(), Some(t) if t.kind == kind)
    }

    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.pos)
    }

    fn prev(&self) -> Option<&Token> {
        self.tokens.get(self.pos - 1)
    }

    fn advance(&mut self) {
        self.pos += 1;
    }
}
