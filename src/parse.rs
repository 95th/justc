use crate::{
    ast::{BinOp, Expr, Function, Lit, Param, Stmt, Ty, UnOp},
    err::{Handler, Result},
    token::{Token, TokenKind, TokenKind::*},
};
use std::rc::Rc;

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
        let stmt = if self.eat(Let) {
            self.let_decl()
        } else if self.eat(Fn) {
            self.fn_decl()
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
        if self.eat(If) {
            self.if_stmt()
        } else if self.eat(Print) {
            self.print_stmt()
        } else if self.eat(While) {
            self.while_stmt()
        } else if self.eat(For) {
            self.for_stmt()
        } else if self.eat(Loop) {
            self.loop_stmt()
        } else if self.eat(OpenBrace) {
            Ok(Stmt::Block(self.block()?))
        } else if self.eat(Break) {
            self.consume(SemiColon, "Expect ';' after variable declaration.")?;
            Ok(Stmt::Break)
        } else if self.eat(Continue) {
            self.consume(SemiColon, "Expect ';' after variable declaration.")?;
            Ok(Stmt::Continue)
        } else {
            self.expr_stmt()
        }
    }

    fn if_stmt(&mut self) -> Result<Stmt> {
        let cond = self.expr()?;
        self.consume(OpenBrace, "Expect '{' after if condition.")?;
        let then_branch = self.block()?;
        let else_branch = if self.eat(Else) {
            self.consume(OpenBrace, "Expect '{' after else.")?;
            self.block()?
        } else {
            vec![]
        };
        Ok(Stmt::If {
            cond,
            then_branch,
            else_branch,
        })
    }

    fn while_stmt(&mut self) -> Result<Stmt> {
        let cond = self.expr()?;
        self.consume(OpenBrace, "Expect '{' after while condition.")?;
        let body = self.block()?;

        let mut stmts = vec![];
        stmts.push(Stmt::If {
            cond,
            then_branch: vec![],
            else_branch: vec![Stmt::Break],
        });
        stmts.extend(body);

        Ok(Stmt::Loop(stmts))
    }

    fn for_stmt(&mut self) -> Result<Stmt> {
        let name = self.consume(Ident, "Expect loop variable name.")?;
        self.consume(In, "Expect 'in' after for loop variable.")?;
        let start = self.expr()?;

        let op = self.consume2(
            Range,
            RangeClosed,
            "Expect either '..' or '..=' in 'for' loop expression.",
        )?;

        let op = match op.kind {
            Range => BinOp::Lt,
            RangeClosed => BinOp::Le,
            _ => unreachable!(),
        };

        let end = self.expr()?;

        self.consume(OpenBrace, "Expect '{' after while condition")?;
        let body = self.block()?;

        let mut block = vec![];
        block.push(Stmt::Let {
            name: name.clone(),
            ty: Ty::Infer,
            init: Some(start),
        });

        let mut loop_body = vec![];
        loop_body.push(Stmt::If {
            cond: Box::new(Expr::Binary {
                op,
                left: Box::new(Expr::Variable(name.clone())),
                right: end,
            }),
            then_branch: vec![],
            else_branch: vec![Stmt::Break],
        });
        loop_body.extend(body);
        loop_body.push(Stmt::Assign {
            name: name.clone(),
            val: Box::new(Expr::Binary {
                op: BinOp::Add,
                left: Box::new(Expr::Variable(name)),
                right: Box::new(Expr::Literal(Lit::Number(1.0))),
            }),
        });

        block.push(Stmt::Loop(loop_body));
        Ok(Stmt::Block(block))
    }

    fn loop_stmt(&mut self) -> Result<Stmt> {
        self.consume(OpenBrace, "Expect '{' after while condition")?;
        let body = self.block()?;
        Ok(Stmt::Loop(body))
    }

    fn block(&mut self) -> Result<Vec<Stmt>> {
        let mut stmts = vec![];
        while !self.check(CloseBrace) && !self.eof() {
            if let Some(s) = self.decl() {
                stmts.push(s);
            }
        }
        self.consume(CloseBrace, "Expect '}' after block.")?;
        Ok(stmts)
    }

    fn let_decl(&mut self) -> Result<Stmt> {
        let name = self.consume(Ident, "Expect variable name.")?;

        let ty = if self.eat(Colon) {
            self.parse_ty()?
        } else {
            Ty::Infer
        };

        let mut init = None;
        if self.eat(Eq) {
            init = Some(self.expr()?);
        }

        self.consume(SemiColon, "Expect ';' after variable declaration.")?;
        Ok(Stmt::Let { name, ty, init })
    }

    fn fn_decl(&mut self) -> Result<Stmt> {
        let name = self.consume(Ident, "Expect fn name.")?;
        self.consume(OpenParen, "Expect '(' after fn name.")?;
        let mut params = vec![];

        if !self.check(CloseParen) {
            loop {
                if params.len() >= 255 {
                    let token = self.peek().cloned();
                    return self
                        .handler
                        .with_token(token.as_ref(), "Cannot have more than 255 parameters.");
                }

                let name = self.consume(Ident, "Expect parameter name.")?;
                self.consume(Colon, "Expect ':' after parameter name.")?;
                let ty = self.parse_ty()?;
                params.push(Param { name, ty });

                if !self.eat(Comma) {
                    break;
                }
            }
        }
        self.consume(CloseParen, "Expect ')' after fn parameters.")?;

        let mut ret_ty = Ty::Unit;
        if self.eat(Arrow) {
            ret_ty = self.parse_ty()?;
        }

        self.consume(OpenBrace, "Expect '{' after while condition.")?;
        let body = self.block()?;

        Ok(Stmt::Function(Rc::new(Function {
            name,
            params,
            ret_ty,
            body,
        })))
    }

    fn print_stmt(&mut self) -> Result<Stmt> {
        let val = self.expr()?;
        self.consume(SemiColon, "Expect ';' after value.")?;
        Ok(Stmt::Print(val))
    }

    fn expr_stmt(&mut self) -> Result<Stmt> {
        let expr = self.expr()?;

        if self.eat(Eq) {
            let eq = self.prev().clone();
            let val = self.expr()?;

            if let Expr::Variable(name) = *expr {
                self.consume(SemiColon, "Expect ';' after assignment.")?;
                return Ok(Stmt::Assign { name, val });
            } else {
                return self
                    .handler
                    .with_token(Some(&eq), "Invalid assignment target.");
            }
        }
        self.consume(SemiColon, "Expect ';' after value.")?;
        Ok(Stmt::Expr(expr))
    }

    fn expr(&mut self) -> Result<Box<Expr>> {
        self.logic_or()
    }

    fn logic_or(&mut self) -> Result<Box<Expr>> {
        let mut left = self.logic_and()?;

        while self.eat(Or) {
            let right = self.logic_and()?;
            left = Box::new(Expr::Binary {
                op: BinOp::Or,
                left,
                right,
            });
        }

        Ok(left)
    }

    fn logic_and(&mut self) -> Result<Box<Expr>> {
        let mut left = self.equality()?;

        while self.eat(And) {
            let right = self.equality()?;
            left = Box::new(Expr::Binary {
                op: BinOp::And,
                left,
                right,
            });
        }

        Ok(left)
    }

    fn equality(&mut self) -> Result<Box<Expr>> {
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

        Ok(left)
    }

    fn comparison(&mut self) -> Result<Box<Expr>> {
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

        Ok(left)
    }

    fn addition(&mut self) -> Result<Box<Expr>> {
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

        Ok(left)
    }

    fn multiplication(&mut self) -> Result<Box<Expr>> {
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

        Ok(left)
    }

    fn unary(&mut self) -> Result<Box<Expr>> {
        let op = if self.eat(Not) {
            UnOp::Not
        } else if self.eat(Minus) {
            UnOp::Neg
        } else {
            return self.call();
        };

        let expr = self.unary()?;
        Ok(Box::new(Expr::Unary { op, expr }))
    }

    fn call(&mut self) -> Result<Box<Expr>> {
        let mut expr = self.primary()?;

        loop {
            if self.eat(OpenParen) {
                expr = self.finish_call(expr)?;
            } else {
                break;
            }
        }

        Ok(expr)
    }

    fn finish_call(&mut self, callee: Box<Expr>) -> Result<Box<Expr>> {
        let mut args = vec![];
        if !self.check(CloseParen) {
            loop {
                if args.len() >= 255 {
                    let token = self.peek().cloned();
                    return self
                        .handler
                        .with_token(token.as_ref(), "Cannot have more than 255 arguments");
                }

                args.push(*self.expr()?);
                if !self.eat(Comma) {
                    break;
                }
            }
        }

        let paren = self.consume(CloseParen, "Expect ')' after arguments.")?;
        Ok(Box::new(Expr::Call {
            callee,
            paren,
            args,
        }))
    }

    fn primary(&mut self) -> Result<Box<Expr>> {
        let lit = if self.eat(False) {
            Lit::Bool(false)
        } else if self.eat(True) {
            Lit::Bool(true)
        } else if self.eat(Num) {
            let token = self.prev();
            let val = token.symbol.parse().unwrap();
            Lit::Number(val)
        } else if self.eat(Str) {
            let token = self.prev();
            let val = token.symbol.to_string();
            Lit::Str(val.to_owned().into())
        } else if self.eat(Ident) {
            return Ok(Box::new(Expr::Variable(self.prev().clone())));
        } else if self.eat(OpenParen) {
            let expr = self.expr()?;
            self.consume(CloseParen, "Expect ')' after expr")?;
            return Ok(Box::new(Expr::Grouping(expr)));
        } else {
            return self
                .handler
                .with_token(self.tokens.get(self.pos), "Expected expression");
        };

        Ok(Box::new(Expr::Literal(lit)))
    }

    fn parse_ty(&mut self) -> Result<Ty> {
        if self.eat(OpenParen) {
            self.parse_tuple()
        } else {
            let start = self.consume(Ident, "Expect Type name")?;
            let mut path = vec![start];
            while self.eat(ColonColon) {
                let frag = self.consume(Ident, "Expect Type name")?;
                path.push(frag);
            }
            Ok(Ty::Path(path))
        }
    }

    fn parse_tuple(&mut self) -> Result<Ty> {
        if self.eat(CloseParen) {
            return Ok(Ty::Unit);
        }

        let mut types = vec![];
        loop {
            types.push(self.parse_ty()?);
            if !self.eat(Comma) {
                break;
            }
        }
        self.consume(CloseParen, "Expect ')' at tuple end")?;
        Ok(Ty::Tuple(types))
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

    fn consume(&mut self, kind: TokenKind, msg: &'static str) -> Result<Token> {
        if self.check(kind) {
            self.advance();
            return Ok(self.prev().clone());
        }

        bail!(msg)
    }

    fn consume2(&mut self, kind: TokenKind, kind2: TokenKind, msg: &'static str) -> Result<Token> {
        if self.check(kind) || self.check(kind2) {
            self.advance();
            return Ok(self.prev().clone());
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

    fn prev(&self) -> &Token {
        &self.tokens[self.pos - 1]
    }

    fn advance(&mut self) {
        self.pos += 1;
    }

    fn eof(&self) -> bool {
        self.pos >= self.tokens.len()
    }
}
