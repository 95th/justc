pub mod ast;

use crate::{
    err::Handler,
    lex::{Lexer, Token, TokenKind, TokenKind::*},
};
use ast::{BinOp, Expr, FloatTy, Function, IntTy, Lit, Param, Stmt, Ty, UnOp};
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
        } else if self.eat(Fn) {
            self.fn_decl()
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
            Some(Stmt::Block(self.block()?))
        } else if self.eat(Break) {
            self.consume(SemiColon, "Expect ';' after variable declaration.")?;
            Some(Stmt::Break)
        } else if self.eat(Continue) {
            self.consume(SemiColon, "Expect ';' after variable declaration.")?;
            Some(Stmt::Continue)
        } else {
            self.expr_stmt()
        }
    }

    fn if_stmt(&mut self) -> Option<Stmt> {
        let cond = self.expr()?;
        self.consume(OpenBrace, "Expect '{' after if condition.")?;
        let then_branch = self.block()?;
        let else_branch = if self.eat(Else) {
            self.consume(OpenBrace, "Expect '{' after else.")?;
            self.block()?
        } else {
            vec![]
        };
        Some(Stmt::If {
            cond,
            then_branch,
            else_branch,
        })
    }

    fn while_stmt(&mut self) -> Option<Stmt> {
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

        Some(Stmt::Loop(stmts))
    }

    fn for_stmt(&mut self) -> Option<Stmt> {
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
            ty: None,
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
        Some(Stmt::Block(block))
    }

    fn loop_stmt(&mut self) -> Option<Stmt> {
        self.consume(OpenBrace, "Expect '{' after while condition")?;
        let body = self.block()?;
        Some(Stmt::Loop(body))
    }

    fn block(&mut self) -> Option<Vec<Stmt>> {
        let mut stmts = vec![];
        while !self.check(CloseBrace) && !self.eof() {
            if let Some(s) = self.decl() {
                stmts.push(s);
            }
        }
        self.consume(CloseBrace, "Expect '}' after block.")?;
        Some(stmts)
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

    fn fn_decl(&mut self) -> Option<Stmt> {
        let name = self.consume(Ident, "Expect fn name.")?;
        self.consume(OpenParen, "Expect '(' after fn name.")?;
        let mut params = vec![];

        if !self.check(CloseParen) {
            loop {
                if params.len() >= 255 {
                    self.handler
                        .report(self.peek().span, "Cannot have more than 255 parameters.");
                    return None;
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

        Some(Stmt::Function(Rc::new(Function {
            name,
            params,
            ret_ty,
            body,
        })))
    }

    fn print_stmt(&mut self) -> Option<Stmt> {
        let val = self.expr()?;
        self.consume(SemiColon, "Expect ';' after value.")?;
        Some(Stmt::Print(val))
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
            return self.call();
        };

        let expr = self.unary()?;
        Some(Box::new(Expr::Unary { op, expr }))
    }

    fn call(&mut self) -> Option<Box<Expr>> {
        let mut expr = self.primary()?;

        loop {
            if self.eat(OpenParen) {
                expr = self.finish_call(expr)?;
            } else {
                break;
            }
        }

        Some(expr)
    }

    fn finish_call(&mut self, callee: Box<Expr>) -> Option<Box<Expr>> {
        let mut args = vec![];
        if !self.check(CloseParen) {
            loop {
                if args.len() >= 255 {
                    self.handler
                        .report(self.peek().span, "Cannot have more than 255 arguments");
                    return None;
                }

                args.push(*self.expr()?);
                if !self.eat(Comma) {
                    break;
                }
            }
        }

        let paren = self.consume(CloseParen, "Expect ')' after arguments.")?;
        Some(Box::new(Expr::Call {
            callee,
            paren,
            args,
        }))
    }

    fn primary(&mut self) -> Option<Box<Expr>> {
        let lit = if self.eat(False) {
            Lit::Bool(false)
        } else if self.eat(True) {
            Lit::Bool(true)
        } else if self.eat(Num) {
            let token = self.prev();
            let val = token.symbol.parse().unwrap();
            Lit::Number(val)
        } else if self.eat(Str) {
            Lit::Str(self.prev().symbol)
        } else if self.eat(Ident) {
            return Some(Box::new(Expr::Variable(self.prev().clone())));
        } else if self.eat(OpenParen) {
            let expr = self.expr()?;
            self.consume(CloseParen, "Expect ')' after expr")?;
            return Some(Box::new(Expr::Grouping(expr)));
        } else {
            self.handler.report(self.peek().span, "Expected expression");
            return None;
        };

        Some(Box::new(Expr::Literal(lit)))
    }

    fn parse_ty(&mut self) -> Option<Ty> {
        let start = self.consume(Ident, "Expect Type name")?;

        match &start.symbol.to_string()[..] {
            "i8" => Some(Ty::Int(IntTy::I8)),
            "i16" => Some(Ty::Int(IntTy::I16)),
            "i32" => Some(Ty::Int(IntTy::I32)),
            "i64" => Some(Ty::Int(IntTy::I64)),
            "f32" => Some(Ty::Float(FloatTy::F32)),
            "f64" => Some(Ty::Float(FloatTy::F64)),
            "String" => Some(Ty::String),
            _ => {
                self.handler.report(start.span, "Unknown type");
                None
            }
        }
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

    fn consume2(&mut self, kind: TokenKind, kind2: TokenKind, msg: &'static str) -> Option<Token> {
        if self.check(kind) || self.check(kind2) {
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
