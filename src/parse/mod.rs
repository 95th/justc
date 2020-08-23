pub mod ast;

use crate::{
    err::Handler,
    lex::{Lexer, LiteralKind, Token, TokenKind, TokenKind::*},
};
use ast::{BinOp, Block, Expr, ExprKind, Lit, Stmt, Ty, TyKind, UnOp};
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
            stmts.push(self.stmt()?);
        }
        Some(stmts)
    }

    fn stmt(&mut self) -> Option<Stmt> {
        match self.full_stmt_without_recovery() {
            Some(s) => Some(s),
            None => {
                self.synchronize();
                return None;
            }
        }
    }

    fn full_stmt_without_recovery(&mut self) -> Option<Stmt> {
        if self.eat(Let) {
            self.let_decl()
        } else if self.eat(OpenBrace) {
            let lo = self.prev.span;
            let block = self.block()?;

            let block = Expr {
                kind: ExprKind::Block(block),
                span: lo.to(self.prev.span),
            };

            Some(Stmt::Expr(Box::new(block)))
        } else {
            self.expr_stmt()
        }
    }

    fn block(&mut self) -> Option<Block> {
        let mut stmts = vec![];
        while !self.check(CloseBrace) && !self.eof() {
            let s = self.full_stmt_without_recovery()?;
            let last_stmt = matches!(s, Stmt::Expr(_));
            stmts.push(s);

            // If statement was an expression without ';',
            // then it must be the last one in this block
            if last_stmt {
                break;
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
            if let ExprKind::Variable(name) = expr.kind {
                let val = self.expr()?;
                self.consume(SemiColon, "Expect ';' after assignment.")?;
                return Some(Stmt::Assign { name, val });
            } else {
                self.handler.report(expr.span, "Invalid assignment target.");
                return None;
            }
        }
        if self.eat(SemiColon) {
            Some(Stmt::SemiExpr(expr))
        } else {
            Some(Stmt::Expr(expr))
        }
    }

    fn expr(&mut self) -> Option<Box<Expr>> {
        self.logic_or()
    }

    fn logic_or(&mut self) -> Option<Box<Expr>> {
        let mut left = self.logic_and()?;

        while self.eat(Or) {
            let right = self.logic_and()?;

            let span = left.span.to(right.span);
            left = Box::new(Expr {
                kind: ExprKind::Binary {
                    op: BinOp::Or,
                    left,
                    right,
                },
                span,
            });
        }

        Some(left)
    }

    fn logic_and(&mut self) -> Option<Box<Expr>> {
        let mut left = self.equality()?;

        while self.eat(And) {
            let right = self.equality()?;
            let span = left.span.to(right.span);

            left = Box::new(Expr {
                kind: ExprKind::Binary {
                    op: BinOp::And,
                    left,
                    right,
                },
                span,
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
            let span = left.span.to(right.span);

            left = Box::new(Expr {
                kind: ExprKind::Binary { op, left, right },
                span,
            });
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
            let span = left.span.to(right.span);

            left = Box::new(Expr {
                kind: ExprKind::Binary { op, left, right },
                span,
            });
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
            let span = left.span.to(right.span);

            left = Box::new(Expr {
                kind: ExprKind::Binary { op, left, right },
                span,
            });
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
            let span = left.span.to(right.span);

            left = Box::new(Expr {
                kind: ExprKind::Binary { op, left, right },
                span,
            });
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
        let lo = self.prev.span;

        let expr = self.unary()?;
        let span = lo.to(self.prev.span);

        Some(Box::new(Expr {
            kind: ExprKind::Unary { op, expr },
            span,
        }))
    }

    fn primary(&mut self) -> Option<Box<Expr>> {
        let lit = if self.eat(False) {
            Lit::Bool(false)
        } else if self.eat(True) {
            Lit::Bool(true)
        } else if self.eat(Literal {
            kind: LiteralKind::Int,
        }) {
            self.prev
                .symbol
                .parse()
                .map(Lit::Integer)
                .unwrap_or(Lit::Err)
        } else if self.eat(Literal {
            kind: LiteralKind::Float,
        }) {
            Lit::Float(self.prev.symbol)
        } else if self.eat(Literal {
            kind: LiteralKind::Str,
        }) {
            Lit::Str(self.prev.symbol)
        } else if self.eat(Ident) {
            return Some(Box::new(Expr {
                kind: ExprKind::Variable(self.prev.clone()),
                span: self.prev.span,
            }));
        } else if self.eat(OpenParen) {
            let lo = self.prev.span;
            let expr = self.expr()?;
            self.consume(CloseParen, "Expect ')' after expr")?;
            let span = lo.to(self.prev.span);

            return Some(Box::new(Expr {
                kind: ExprKind::Grouping(expr),
                span,
            }));
        } else if self.eat(OpenBrace) {
            let lo = self.prev.span;
            let block = self.block()?;
            let span = lo.to(self.prev.span);

            return Some(Box::new(Expr {
                kind: ExprKind::Block(block),
                span,
            }));
        } else if self.eat(If) {
            let lo = self.prev.span;
            let cond = self.expr()?;
            self.consume(OpenBrace, "Expect '{' after if condition")?;
            let then_clause = self.block()?;
            let mut else_clause = None;
            if self.eat(Else) {
                self.consume(OpenBrace, "Expect '{' after else")?;
                else_clause = Some(self.block()?);
            }
            let span = lo.to(self.prev.span);
            return Some(Box::new(Expr {
                kind: ExprKind::If {
                    cond,
                    then_clause,
                    else_clause,
                },
                span,
            }));
        } else {
            self.handler.report(self.curr.span, "Expected expression");
            return None;
        };

        Some(Box::new(Expr {
            kind: ExprKind::Literal(lit),
            span: self.prev.span,
        }))
    }

    fn parse_ty(&mut self) -> Option<Ty> {
        let token = self.consume(Ident, "Expect Type name")?;
        let symbol = token.symbol;

        let kind = symbol.as_str_with(|s| match s {
            "_" => TyKind::Infer,
            _ => TyKind::Ident(token),
        });

        Some(Ty {
            span: self.prev.span,
            kind,
        })
    }

    fn synchronize(&mut self) {
        self.advance();
        while !self.eof() {
            match self.prev.kind {
                SemiColon => return,
                Struct | Fn | Let | For | If | While | Return => return,
                _ => self.advance(),
            }
        }
    }

    fn consume(&mut self, kind: TokenKind, msg: &'static str) -> Option<Token> {
        if self.check(kind) {
            self.advance();
            return Some(self.prev.clone());
        }

        self.handler.report(self.curr.span, msg);
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
        self.curr.kind == kind
    }

    fn advance(&mut self) {
        self.prev = std::mem::replace(&mut self.curr, self.lexer.next_token())
    }

    fn eof(&self) -> bool {
        self.curr.kind == Eof
    }
}
