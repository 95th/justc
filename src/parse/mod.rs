pub mod ast;

use self::ast::{
    Ast, BinOp, Block, Expr, ExprKind, Field, Function, Lit, Param, Stmt, Ty, TyKind, UnOp,
};
use crate::{
    err::Handler,
    lex::{Lexer, LiteralKind, Spanned, Token, TokenKind, TokenKind::*},
    symbol::Symbol,
};
use std::{collections::HashSet, rc::Rc};

pub struct Parser {
    lexer: Lexer,
    handler: Rc<Handler>,
    curr: Token,
    prev: Token,
    restrictions: Restrictions,
}

bitflags::bitflags! {
    struct Restrictions: u8 {
        const NO_STRUCT_LITERAL = 1 << 0;
    }
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
            restrictions: Restrictions::empty(),
        }
    }

    pub fn parse(&mut self) -> Option<Ast> {
        let mut stmts = vec![];
        let mut functions = vec![];
        let mut structs = vec![];
        let mut impls = vec![];
        let mut declared_fns = HashSet::new();
        let mut declared_structs = HashSet::new();

        while !self.eof() {
            if self.eat(Fn) {
                let fun = self.function(false, &mut declared_fns)?;
                functions.push(fun);
            } else if self.eat(Struct) {
                let item = self.struct_item(&mut declared_structs)?;
                structs.push(item);
            } else if self.eat(Impl) {
                let item = self.impl_item()?;
                impls.push(item);
            } else {
                let stmt = self.stmt()?;
                stmts.push(stmt);
            }
        }

        if self.handler.has_errors() {
            None
        } else {
            Some(Ast {
                stmts,
                functions,
                structs,
                impls,
            })
        }
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

            Some(Stmt::Expr(Box::new(block), false))
        } else if self.eat(While) {
            let cond =
                self.with_restrictions(Restrictions::NO_STRUCT_LITERAL, |this| this.expr())?;

            self.consume(OpenBrace, "Expected '{' after the condition")?;
            let body = self.block()?;
            Some(Stmt::While { cond, body })
        } else if self.eat(Return) {
            let span = self.prev.span;
            let mut expr = None;
            if !self.check(SemiColon) {
                expr = Some(self.expr()?);
            }
            self.consume(SemiColon, "Expected ';' after return");
            Some(Stmt::Return(span, expr))
        } else if self.eat(Continue) {
            let span = self.prev.span;
            self.consume(SemiColon, "Expected ';' after continue");
            Some(Stmt::Continue(span))
        } else if self.eat(Break) {
            let span = self.prev.span;
            self.consume(SemiColon, "Expected ';' after break");
            Some(Stmt::Break(span))
        } else {
            self.expr_stmt()
        }
    }

    fn block(&mut self) -> Option<Block> {
        let lo = self.prev.span;
        let mut stmts = vec![];
        let mut functions = vec![];
        let mut structs = vec![];
        let mut impls = vec![];
        let mut declared_fns = HashSet::new();
        let mut declared_structs = HashSet::new();

        while !self.check(CloseBrace) && !self.eof() {
            if self.eat(Fn) {
                let fun = self.function(false, &mut declared_fns)?;
                functions.push(fun);
            } else if self.eat(Struct) {
                let s = self.struct_item(&mut declared_structs)?;
                structs.push(s);
            } else if self.eat(Impl) {
                let item = self.impl_item()?;
                impls.push(item);
            } else {
                let s = self.full_stmt_without_recovery()?;
                stmts.push(s);
            }
        }
        self.consume(CloseBrace, "Expected '}' after block.")?;
        let span = lo.to(self.prev.span);
        Some(Block {
            stmts,
            span,
            functions,
            structs,
            impls,
        })
    }

    fn function(
        &mut self,
        allow_self: bool,
        declared_fns: &mut HashSet<Symbol>,
    ) -> Option<Function> {
        let name = self.consume(Ident, "Expected function name")?;
        if !declared_fns.insert(name.symbol) {
            self.handler.report(
                name.span,
                "Function with same name already defined in this scope",
            );
        }

        self.consume(OpenParen, "Expected '('")?;
        let mut params = vec![];
        while !self.check(CloseParen) && !self.eof() {
            let param = self.param(allow_self, false)?;
            params.push(param);
            if !self.eat(Comma) {
                break;
            }
        }
        self.consume(CloseParen, "Expected ')'")?;

        let ret = if self.eat(Arrow) {
            self.parse_ty()?
        } else {
            TyKind::Unit.into()
        };

        self.consume(OpenBrace, "Expected '{'")?;
        let body = self.block()?;

        Some(Function {
            name,
            params,
            ret,
            body,
        })
    }

    fn impl_item(&mut self) -> Option<ast::Impl> {
        let name = self.consume(Ident, "Expected type name")?;
        self.consume(OpenBrace, "Expected '{'")?;

        let mut functions = vec![];
        let mut declared_fns = HashSet::new();

        while self.eat(Fn) {
            let fun = self.function(true, &mut declared_fns)?;
            functions.push(fun);
        }

        self.consume(CloseBrace, "Expected '}'")?;

        Some(ast::Impl { name, functions })
    }

    fn struct_item(&mut self, declared_structs: &mut HashSet<Symbol>) -> Option<ast::Struct> {
        let name = self.consume(Ident, "Expected struct name")?;
        if !declared_structs.insert(name.symbol) {
            self.handler.report(
                name.span,
                "Struct with same name already defined in this scope",
            );
        }

        self.consume(OpenBrace, "Expected '{'")?;
        let mut fields = vec![];
        while !self.check(CloseBrace) && !self.eof() {
            let field = self.struct_field()?;
            fields.push(field);
            if !self.eat(Comma) {
                break;
            }
        }
        self.consume(CloseBrace, "Expected '}'")?;

        Some(ast::Struct { name, fields })
    }

    fn struct_field(&mut self) -> Option<ast::StructField> {
        let name = self.consume(Ident, "Expected field name")?;
        self.consume(Colon, "Expected ':' after field name")?;
        let ty = self.parse_ty()?;
        if ty.kind == TyKind::Infer {
            self.handler
                .report(ty.span, "not allowed in type signatures");
            return None;
        }

        Some(ast::StructField { name, ty })
    }

    fn let_decl(&mut self) -> Option<Stmt> {
        let name = self.consume(Ident, "Expected variable name.")?;

        let ty = if self.eat(Colon) {
            self.parse_ty()?
        } else {
            TyKind::Infer.into()
        };

        let mut init = None;
        if self.eat(Eq) {
            init = Some(self.expr()?);
        }

        self.consume(SemiColon, "Expected ';' after variable declaration.")?;
        Some(Stmt::Let { name, ty, init })
    }

    fn expr_stmt(&mut self) -> Option<Stmt> {
        let expr = self.expr()?;

        if self.eat(Eq) {
            if let ExprKind::Variable(_) = expr.kind {
                let val = self.expr()?;
                self.consume(SemiColon, "Expected ';' after assignment.")?;
                return Some(Stmt::Assign { name: expr, val });
            } else {
                self.handler.report(expr.span, "Invalid assignment target.");
                return None;
            }
        }
        Some(Stmt::Expr(expr, self.eat(SemiColon)))
    }

    fn expr(&mut self) -> Option<Box<Expr>> {
        self.logic_or()
    }

    fn logic_or(&mut self) -> Option<Box<Expr>> {
        let mut left = self.logic_and()?;

        while self.eat(OrOr) {
            let op_span = self.prev.span;
            let right = self.logic_and()?;

            let span = left.span.to(right.span);
            left = Box::new(Expr {
                kind: ExprKind::Binary {
                    op: Spanned::new(BinOp::Or, op_span),
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

        while self.eat(AndAnd) {
            let op_span = self.prev.span;
            let right = self.equality()?;
            let span = left.span.to(right.span);

            left = Box::new(Expr {
                kind: ExprKind::Binary {
                    op: Spanned::new(BinOp::And, op_span),
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
            let op_span = self.prev.span;
            let right = self.comparison()?;
            let span = left.span.to(right.span);

            left = Box::new(Expr {
                kind: ExprKind::Binary {
                    op: Spanned::new(op, op_span),
                    left,
                    right,
                },
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
            let op_span = self.prev.span;
            let right = self.addition()?;
            let span = left.span.to(right.span);

            left = Box::new(Expr {
                kind: ExprKind::Binary {
                    op: Spanned::new(op, op_span),
                    left,
                    right,
                },
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
            let op_span = self.prev.span;
            let right = self.multiplication()?;
            let span = left.span.to(right.span);

            left = Box::new(Expr {
                kind: ExprKind::Binary {
                    op: Spanned::new(op, op_span),
                    left,
                    right,
                },
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
            let op_span = self.prev.span;
            let right = self.unary()?;
            let span = left.span.to(right.span);

            left = Box::new(Expr {
                kind: ExprKind::Binary {
                    op: Spanned::new(op, op_span),
                    left,
                    right,
                },
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
            return self.call();
        };
        let op_span = self.prev.span;

        let expr = self.unary()?;
        let span = op_span.to(self.prev.span);

        Some(Box::new(Expr {
            kind: ExprKind::Unary {
                op: Spanned::new(op, op_span),
                expr,
            },
            span,
        }))
    }

    fn call(&mut self) -> Option<Box<Expr>> {
        let mut expr = self.primary()?;

        loop {
            if self.eat(OpenParen) {
                expr = self.finish_call(expr)?;
            } else if self.eat(Dot) {
                let name = self.consume(Ident, "Expected field or method name")?;
                let span = expr.span.to(name.span);
                expr = Box::new(Expr {
                    kind: ExprKind::Field(expr, name),
                    span,
                })
            } else {
                break;
            }
        }

        Some(expr)
    }

    fn finish_call(&mut self, callee: Box<Expr>) -> Option<Box<Expr>> {
        let mut args = vec![];
        while !self.check(CloseParen) && !self.eof() {
            let arg = self.expr()?;
            args.push(arg);

            if !self.eat(Comma) {
                break;
            }
        }

        self.consume(CloseParen, "Expected ')' after arguments");
        let span = callee.span.to(self.prev.span);
        Some(Box::new(Expr {
            kind: ExprKind::Call { callee, args },
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
            return self.path_or_struct();
        } else if self.eat(Celf) {
            let span = self.prev.span;
            let name = self.prev.clone();
            return Some(Box::new(Expr {
                kind: ExprKind::Variable(name),
                span,
            }));
        } else if self.eat(OpenParen) {
            let lo = self.prev.span;
            let expr = self.with_restrictions(Restrictions::empty(), |this| this.expr())?;
            self.consume(CloseParen, "Expected ')' after expr")?;
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
            return self.if_expr();
        } else if self.eat(Or) || self.eat(OrOr) {
            return self.closure();
        } else {
            self.handler.report(self.curr.span, "Expected expression");
            return None;
        };

        Some(Box::new(Expr {
            kind: ExprKind::Literal(lit, self.prev.span),
            span: self.prev.span,
        }))
    }

    fn path_or_struct(&mut self) -> Option<Box<Expr>> {
        let mut span = self.prev.span;
        let name = self.prev.clone();

        let kind = if self.check(OpenBrace) && self.is_certainly_not_a_block() {
            self.consume(OpenBrace, "Expected '{'")?;
            let mut fields = vec![];

            while !self.check(CloseBrace) && !self.eof() {
                let name = self.consume(Ident, "Expected field name")?;
                let expr = if self.eat(Colon) {
                    self.expr()?
                } else {
                    let var_span = name.span;
                    Box::new(Expr {
                        kind: ExprKind::Variable(name.clone()),
                        span: var_span,
                    })
                };
                fields.push(Field { name, expr });

                if !self.eat(Comma) {
                    break;
                }
            }
            self.consume(CloseBrace, "Expected '}'")?;
            span = span.to(self.prev.span);

            if self.restrictions.contains(Restrictions::NO_STRUCT_LITERAL) {
                self.handler.report(
                    span,
                    "struct literal not allowed here. Use parentheses around it",
                );
                return None;
            }

            ExprKind::Struct(name, fields)
        } else {
            ExprKind::Variable(name)
        };

        Some(Box::new(Expr { kind, span }))
    }

    fn closure(&mut self) -> Option<Box<Expr>> {
        let lo = self.prev.span;
        let mut params = vec![];

        if self.prev.kind == Or {
            while !self.check(Or) && !self.eof() {
                let param = self.param(false, true)?;
                params.push(param);
                if !self.eat(Comma) {
                    break;
                }
            }
            self.consume(Or, "Expected '|' after closure parameters")?;
        }

        let mut only_block_allowed = false;
        let ret = if self.eat(Arrow) {
            only_block_allowed = true;
            self.parse_ty()?
        } else {
            TyKind::Infer.into()
        };

        let body = if only_block_allowed {
            self.consume(OpenBrace, "Expected '{'")?;
            let lo = self.prev.span;
            let block = self.block()?;
            let span = lo.to(self.prev.span);

            Box::new(Expr {
                kind: ExprKind::Block(block),
                span,
            })
        } else {
            self.expr()?
        };

        let span = lo.to(self.prev.span);
        Some(Box::new(Expr {
            kind: ExprKind::Closure { params, ret, body },
            span,
        }))
    }

    fn if_expr(&mut self) -> Option<Box<Expr>> {
        let lo = self.prev.span;
        let cond = self.expr()?;
        self.consume(OpenBrace, "Expected '{' after if condition")?;
        let then_clause = self.block()?;
        let mut else_clause = None;
        if self.eat(Else) {
            if self.eat(If) {
                else_clause = Some(self.if_expr()?);
            } else {
                self.consume(OpenBrace, "Expected '{' after else")?;
                let block = self.block()?;
                let span = block.span;
                else_clause = Some(Box::new(Expr {
                    kind: ExprKind::Block(block),
                    span,
                }));
            }
        }
        let span = lo.to(self.prev.span);
        Some(Box::new(Expr {
            kind: ExprKind::If {
                cond,
                then_clause,
                else_clause,
            },
            span,
        }))
    }

    fn param(&mut self, allow_self: bool, infer_ty: bool) -> Option<Param> {
        if self.eat(Celf) {
            let span = self.prev.span;
            if !allow_self {
                self.handler.report(span, "`self` not allowed here");
                return None;
            }

            let name = self.prev.clone();
            let ty = Ty {
                kind: TyKind::Celf,
                span,
            };
            return Some(Param { name, ty });
        }

        let name = self.consume(Ident, "Expected parameter name")?;

        let ty = if self.eat(Colon) {
            self.parse_ty()?
        } else if infer_ty {
            TyKind::Infer.into()
        } else {
            self.handler
                .report(self.curr.span, "Expected parameter type");
            return None;
        };

        Some(Param { name, ty })
    }

    fn parse_ty(&mut self) -> Option<Ty> {
        if self.eat(Fn) {
            let lo = self.prev.span;
            self.consume(OpenParen, "Expected '('")?;
            let mut params = vec![];

            while !self.check(CloseParen) && !self.eof() {
                let param = self.parse_ty()?;
                params.push(param);

                if !self.eat(Comma) {
                    break;
                }
            }

            self.consume(CloseParen, "Expected ')'")?;

            let ret = if self.eat(Arrow) {
                self.parse_ty()?
            } else {
                TyKind::Unit.into()
            };

            let span = lo.to(self.prev.span);
            return Some(Ty {
                kind: TyKind::Fn(params, Box::new(ret)),
                span,
            });
        }

        let token = self.consume(Ident, "Expected Type name")?;
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

    fn is_certainly_not_a_block(&mut self) -> bool {
        if !self.lexer.look_ahead(1, |t| t.kind == Ident) {
            return false;
        }

        if self.lexer.look_ahead(2, |t| t.kind == Comma) {
            return true;
        }

        self.lexer.look_ahead(2, |t| t.kind == Colon)
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

    fn with_restrictions<F, R>(&mut self, new_restrictions: Restrictions, f: F) -> R
    where
        F: FnOnce(&mut Self) -> R,
    {
        let save = self.restrictions;
        self.restrictions = new_restrictions;
        let result = f(self);
        self.restrictions = save;
        result
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lex::Span;

    fn parse(src: &str) -> Vec<Stmt> {
        let src = Rc::new(String::from(src));
        let handler = Rc::new(Handler::new(&src));
        let mut parser = Parser::new(src, &handler);
        parser.parse().unwrap().stmts
    }

    macro_rules! expr {
        ($kind:expr, ($lo:expr, $hi:expr)) => {
            Box::new(Expr {
                kind: $kind,
                span: Span::new($lo, $hi),
            })
        };
    }

    macro_rules! litint {
        ($val:literal, ($lo:expr, $hi:expr)) => {
            expr!(
                ExprKind::Literal(Lit::Integer($val), Span::DUMMY),
                ($lo, $hi)
            )
        };
    }

    macro_rules! binop {
        ($op:ident, $left:expr, $right:expr, ($lo:expr, $hi:expr)) => {
            expr!(
                ExprKind::Binary {
                    op: Spanned::new(BinOp::$op, Span::DUMMY),
                    left: $left,
                    right: $right,
                },
                ($lo, $hi)
            )
        };
    }

    #[test]
    fn add() {
        assert_eq!(
            parse("1 + 1"),
            vec![Stmt::Expr(
                binop!(Add, litint!(1, (0, 1)), litint!(1, (4, 5)), (0, 5)),
                false
            )]
        );
    }

    #[test]
    fn combine() {
        assert_eq!(
            parse("1 * 1 - 1 / 1 + 1"),
            vec![Stmt::Expr(
                binop!(
                    Add,
                    binop!(
                        Sub,
                        binop!(Mul, litint!(1, (0, 1)), litint!(1, (4, 5)), (0, 5)),
                        binop!(Div, litint!(1, (8, 9)), litint!(1, (12, 13)), (8, 13)),
                        (0, 13)
                    ),
                    litint!(1, (16, 17)),
                    (0, 17)
                ),
                false
            )]
        );
    }
}
