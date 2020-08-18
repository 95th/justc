use crate::{
    ast::{BinOp, Expr, Lit, Stmt, UnOp},
    err::{Handler, Result},
    token::{Token, TokenKind},
};

pub struct Parser<'a> {
    tokens: Vec<Token>,
    handler: &'a mut Handler,
    pos: usize,
}

impl<'a> Parser<'a> {
    pub fn new(tokens: Vec<Token>, handler: &'a mut Handler) -> Self {
        Self {
            tokens,
            handler,
            pos: 0,
        }
    }

    pub fn parse(&mut self) -> Vec<Stmt> {
        let mut stmts = vec![];
        while !self.eof() {
            if let Some(s) = self.decl() {
                stmts.push(s);
            }
        }
        stmts
    }

    fn decl(&mut self) -> Option<Stmt> {
        let stmt = if self.eat(TokenKind::Let) {
            self.let_decl()
        } else {
            self.stmt()
        };
        match stmt {
            Ok(s) => Some(s),
            Err(e) => {
                println!("{}", e);
                self.synchronize();
                return None;
            }
        }
    }

    fn stmt(&mut self) -> Result<Stmt> {
        if self.eat(TokenKind::If) {
            self.if_stmt()
        } else if self.eat(TokenKind::Print) {
            self.print_stmt()
        } else if self.eat(TokenKind::While) {
            self.while_stmt()
        } else if self.eat(TokenKind::For) {
            self.for_stmt()
        } else if self.eat(TokenKind::Loop) {
            self.loop_stmt()
        } else if self.eat(TokenKind::OpenBrace) {
            Ok(Stmt::Block(self.block()?))
        } else if self.eat(TokenKind::Break) {
            self.consume(
                TokenKind::SemiColon,
                "Expect ';' after variable declaration.",
            )?;
            Ok(Stmt::Break)
        } else if self.eat(TokenKind::Continue) {
            self.consume(
                TokenKind::SemiColon,
                "Expect ';' after variable declaration.",
            )?;
            Ok(Stmt::Continue)
        } else {
            self.expr_stmt()
        }
    }

    fn if_stmt(&mut self) -> Result<Stmt> {
        let cond = self.expr()?;
        self.consume(TokenKind::OpenBrace, "Expect '{' after if condition")?;
        let then = self.block()?;
        let else_branch = if self.eat(TokenKind::Else) {
            self.consume(TokenKind::OpenBrace, "Expect '{' after else")?;
            self.block()?
        } else {
            vec![]
        };
        Ok(Stmt::If(cond, then, else_branch))
    }

    fn while_stmt(&mut self) -> Result<Stmt> {
        let cond = self.expr()?;
        self.consume(TokenKind::OpenBrace, "Expect '{' after while condition")?;
        let body = self.block()?;

        let mut stmts = vec![];
        stmts.push(Stmt::If(cond, vec![], vec![Stmt::Break]));
        stmts.extend(body);

        Ok(Stmt::Loop(stmts))
    }

    fn for_stmt(&mut self) -> Result<Stmt> {
        let name = self.consume(TokenKind::Ident, "Expect loop variable name")?;
        self.consume(TokenKind::In, "Expect 'in' after for loop variable")?;
        let start = self.expr()?;

        let op = self.consume2(
            TokenKind::Range,
            TokenKind::RangeClosed,
            "Expect either '..' or '..=' in 'for' loop expression",
        )?;

        let op = match op.kind {
            TokenKind::Range => BinOp::Lt,
            TokenKind::RangeClosed => BinOp::Le,
            _ => unreachable!(),
        };

        let end = self.expr()?;

        self.consume(TokenKind::OpenBrace, "Expect '{' after while condition")?;
        let body = self.block()?;

        let mut block = vec![];
        block.push(Stmt::Let(name.clone(), Some(start)));

        let mut loop_body = vec![];
        loop_body.push(Stmt::If(
            Box::new(Expr::Binary(
                op,
                Box::new(Expr::Variable(name.clone())),
                end,
            )),
            vec![],
            vec![Stmt::Break],
        ));
        loop_body.extend(body);
        loop_body.push(Stmt::Assign(
            name.clone(),
            Box::new(Expr::Binary(
                BinOp::Add,
                Box::new(Expr::Variable(name)),
                Box::new(Expr::Literal(Lit::Number(1.0))),
            )),
        ));

        block.push(Stmt::Loop(loop_body));
        Ok(Stmt::Block(block))
    }

    fn loop_stmt(&mut self) -> Result<Stmt> {
        self.consume(TokenKind::OpenBrace, "Expect '{' after while condition")?;
        let body = self.block()?;
        Ok(Stmt::Loop(body))
    }

    fn block(&mut self) -> Result<Vec<Stmt>> {
        let mut stmts = vec![];
        while !self.check(TokenKind::CloseBrace) && !self.eof() {
            if let Some(s) = self.decl() {
                stmts.push(s);
            }
        }
        self.consume(TokenKind::CloseBrace, "Expect '}' after block.")?;
        Ok(stmts)
    }

    fn let_decl(&mut self) -> Result<Stmt> {
        let name = self.consume(TokenKind::Ident, "Expect variable name.")?;

        let mut init = None;
        if self.eat(TokenKind::Eq) {
            init = Some(self.expr()?);
        }

        self.consume(
            TokenKind::SemiColon,
            "Expect ';' after variable declaration.",
        )?;
        Ok(Stmt::Let(name, init))
    }

    fn print_stmt(&mut self) -> Result<Stmt> {
        let val = self.expr()?;
        self.consume(TokenKind::SemiColon, "Expect ';' after value")?;
        Ok(Stmt::Print(val))
    }

    fn expr_stmt(&mut self) -> Result<Stmt> {
        let expr = self.expr()?;

        if self.eat(TokenKind::Eq) {
            let eq = self.prev().cloned();
            let val = self.expr()?;

            if let Expr::Variable(name) = *expr {
                self.consume(TokenKind::SemiColon, "Expect ';' after assignment")?;
                return Ok(Stmt::Assign(name, val));
            } else {
                return self
                    .handler
                    .with_token(eq.as_ref(), "Invalid assignment target");
            }
        }
        self.consume(TokenKind::SemiColon, "Expect ';' after value")?;
        Ok(Stmt::Expr(expr))
    }

    fn expr(&mut self) -> Result<Box<Expr>> {
        self.logic_or()
    }

    fn logic_or(&mut self) -> Result<Box<Expr>> {
        let mut expr = self.logic_and()?;

        while self.eat(TokenKind::Or) {
            let right = self.logic_and()?;
            expr = Box::new(Expr::Binary(BinOp::Or, expr, right));
        }

        Ok(expr)
    }

    fn logic_and(&mut self) -> Result<Box<Expr>> {
        let mut expr = self.equality()?;

        while self.eat(TokenKind::And) {
            let right = self.equality()?;
            expr = Box::new(Expr::Binary(BinOp::And, expr, right));
        }

        Ok(expr)
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
            } else if self.eat(TokenKind::Percent) {
                BinOp::Rem
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
            let val = token.symbol.parse().unwrap();
            Lit::Number(val)
        } else if self.eat(TokenKind::Str) {
            let token = self.prev().unwrap();
            let val = token.symbol.to_string();
            Lit::Str(val.to_owned().into())
        } else if self.eat(TokenKind::Ident) {
            return Ok(Box::new(Expr::Variable(self.prev().unwrap().clone())));
        } else if self.eat(TokenKind::OpenParen) {
            let expr = self.expr()?;
            self.consume(TokenKind::CloseParen, "Expect ')' after expr")?;
            return Ok(Box::new(Expr::Grouping(expr)));
        } else {
            return self
                .handler
                .with_token(self.tokens.get(self.pos), "Expected expression");
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

    fn consume(&mut self, kind: TokenKind, msg: &'static str) -> Result<Token> {
        if self.check(kind) {
            self.advance();
            return Ok(self.prev().unwrap().clone());
        }

        bail!(msg)
    }

    fn consume2(&mut self, kind: TokenKind, kind2: TokenKind, msg: &'static str) -> Result<Token> {
        if self.check(kind) || self.check(kind2) {
            self.advance();
            return Ok(self.prev().unwrap().clone());
        }

        bail!(msg)
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

    fn eof(&self) -> bool {
        self.pos >= self.tokens.len()
    }
}
