pub mod ast;

use self::ast::{
    Ast, BinOp, Block, Expr, ExprKind, Field, Function, Lit, Param, Stmt, Ty, TyKind, UnOp,
};
use crate::{
    err::{Handler, Result},
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
        const ALLOW_SELF = 1 << 1;
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

    pub fn parse(&mut self) -> Result<Ast> {
        let mut stmts = vec![];
        let mut functions = vec![];
        let mut structs = vec![];
        let mut impls = vec![];
        let mut declared_fns = HashSet::new();
        let mut declared_structs = HashSet::new();

        while !self.eof() {
            if self.eat(Fn) {
                let fun = self.function(&mut declared_fns)?;
                functions.push(fun);
            } else if self.eat(Struct) {
                let item = self.struct_item(&mut declared_structs, &mut declared_fns)?;
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
            Err(())
        } else {
            Ok(Ast {
                stmts,
                functions,
                structs,
                impls,
            })
        }
    }

    fn stmt(&mut self) -> Result<Stmt> {
        match self.full_stmt_without_recovery() {
            Ok(s) => Ok(s),
            Err(()) => {
                self.synchronize();
                return Err(());
            }
        }
    }

    fn full_stmt_without_recovery(&mut self) -> Result<Stmt> {
        if self.eat(Let) {
            self.let_decl()
        } else if self.eat(OpenBrace) {
            let lo = self.prev.span;
            let block = self.block()?;

            let block = Expr {
                kind: ExprKind::Block(block),
                span: lo.to(self.prev.span),
            };

            Ok(Stmt::Expr(Box::new(block), false))
        } else if self.eat(While) {
            let cond =
                self.with_restrictions(Restrictions::NO_STRUCT_LITERAL, |this| this.expr())?;

            self.consume(OpenBrace, "Expected '{' after the condition")?;
            let body = self.block()?;
            Ok(Stmt::While { cond, body })
        } else if self.eat(Return) {
            let span = self.prev.span;
            let mut expr = None;
            if !self.check(SemiColon) {
                expr = Some(self.expr()?);
            }
            self.consume(SemiColon, "Expected ';' after return")?;
            Ok(Stmt::Return(span, expr))
        } else if self.eat(Continue) {
            let span = self.prev.span;
            self.consume(SemiColon, "Expected ';' after continue")?;
            Ok(Stmt::Continue(span))
        } else if self.eat(Break) {
            let span = self.prev.span;
            self.consume(SemiColon, "Expected ';' after break")?;
            Ok(Stmt::Break(span))
        } else {
            self.expr_stmt()
        }
    }

    fn block(&mut self) -> Result<Block> {
        let lo = self.prev.span;
        let mut stmts = vec![];
        let mut functions = vec![];
        let mut structs = vec![];
        let mut impls = vec![];
        let mut declared_fns = HashSet::new();
        let mut declared_structs = HashSet::new();

        while !self.check(CloseBrace) && !self.eof() {
            if self.eat(Fn) {
                let fun = self.function(&mut declared_fns)?;
                functions.push(fun);
            } else if self.eat(Struct) {
                let s = self.struct_item(&mut declared_structs, &mut declared_fns)?;
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
        Ok(Block {
            stmts,
            span,
            functions,
            structs,
            impls,
        })
    }

    fn function(&mut self, declared_fns: &mut HashSet<Symbol>) -> Result<Function> {
        let name = self.consume(Ident, "Expected function name")?;
        if !declared_fns.insert(name.symbol) {
            return self.handler.mk_err(
                name.span,
                "Function with same name already defined in this scope",
            );
        }

        self.consume(OpenParen, "Expected '('")?;
        let params = self.params(CloseParen, false)?;
        self.consume(CloseParen, "Expected ')'")?;

        let ret = if self.eat(Arrow) {
            self.parse_ty()?
        } else {
            TyKind::Unit.into()
        };

        self.consume(OpenBrace, "Expected '{'")?;
        let body = self.block()?;

        Ok(Function {
            name,
            params,
            ret,
            body,
        })
    }

    fn impl_item(&mut self) -> Result<ast::Impl> {
        self.with_restrictions(Restrictions::ALLOW_SELF, |this| {
            let name = this.consume(Ident, "Expected type name")?;
            this.consume(OpenBrace, "Expected '{'")?;

            let mut functions = vec![];
            let mut declared_fns = HashSet::new();

            while this.eat(Fn) {
                let fun = this.function(&mut declared_fns)?;
                functions.push(fun);
            }

            this.consume(CloseBrace, "Expected '}'")?;
            Ok(ast::Impl { name, functions })
        })
    }

    fn struct_item(
        &mut self,
        declared_structs: &mut HashSet<Symbol>,
        declared_fns: &mut HashSet<Symbol>,
    ) -> Result<ast::Struct> {
        self.without_restrictions(Restrictions::ALLOW_SELF, |this| {
            this.struct_item_inner(declared_structs, declared_fns)
        })
    }

    fn struct_item_inner(
        &mut self,
        declared_structs: &mut HashSet<Symbol>,
        declared_fns: &mut HashSet<Symbol>,
    ) -> Result<ast::Struct> {
        let name = self.consume(Ident, "Expected struct name")?;
        if !declared_structs.insert(name.symbol) {
            return self.handler.mk_err(
                name.span,
                "Struct with same name already defined in this scope",
            );
        }

        if self.eat(OpenBrace) {
            let mut fields = vec![];
            while !self.check(CloseBrace) && !self.eof() {
                let field = self.struct_field()?;
                fields.push(field);
                if !self.eat(Comma) {
                    break;
                }
            }
            self.consume(CloseBrace, "Expected '}'")?;

            Ok(ast::Struct { name, fields })
        } else if self.eat(OpenParen) {
            if !declared_fns.insert(name.symbol) {
                return self.handler.mk_err(
                    name.span,
                    "Another item with same name already defined in this scope",
                );
            }

            let mut fields = vec![];
            while !self.check(CloseParen) && !self.eof() {
                let ty = self.parse_ty()?;
                let name = Token {
                    span: ty.span,
                    kind: TokenKind::Ident,
                    symbol: Symbol::intern(&fields.len().to_string()),
                };

                fields.push(ast::StructField { name, ty });
                if !self.eat(Comma) {
                    break;
                }
            }
            self.consume(CloseParen, "Expected ')'")?;
            self.consume(SemiColon, "Expected ';'")?;

            Ok(ast::Struct { name, fields })
        } else {
            self.handler.mk_err(self.curr.span, "Expected '{' or '('")
        }
    }

    fn struct_field(&mut self) -> Result<ast::StructField> {
        let name = self.consume(Ident, "Expected field name")?;
        self.consume(Colon, "Expected ':' after field name")?;
        let ty = self.parse_ty()?;
        if ty.kind == TyKind::Infer {
            return self
                .handler
                .mk_err(ty.span, "not allowed in type signatures");
        }

        Ok(ast::StructField { name, ty })
    }

    fn let_decl(&mut self) -> Result<Stmt> {
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
        Ok(Stmt::Let { name, ty, init })
    }

    fn expr_stmt(&mut self) -> Result<Stmt> {
        let expr = self.expr()?;

        if self.eat(Eq) {
            if !expr.is_assignable() {
                return self
                    .handler
                    .mk_err(expr.span, "Cannot assign to this expression");
            }

            let val = self.expr()?;
            self.consume(SemiColon, "Expected ';' after assignment.")?;
            return Ok(Stmt::Assign {
                lhs: expr,
                rhs: val,
            });
        } else if self.eat(PlusEq) || self.eat(MinusEq) || self.eat(StarEq) || self.eat(SlashEq) {
            if !expr.is_assignable() {
                return self
                    .handler
                    .mk_err(expr.span, "Cannot assign to this expression");
            }

            let op = match self.prev.kind {
                PlusEq => BinOp::Add,
                MinusEq => BinOp::Sub,
                StarEq => BinOp::Mul,
                SlashEq => BinOp::Sub,
                _ => unreachable!(),
            };
            let op = Spanned::new(op, self.prev.span);
            let val = self.expr()?;
            self.consume(SemiColon, "Expected ';' after assignment.")?;
            return Ok(Stmt::OpAssign {
                lhs: expr,
                rhs: val,
                op,
            });
        }
        Ok(Stmt::Expr(expr, self.eat(SemiColon)))
    }

    fn expr(&mut self) -> Result<Box<Expr>> {
        self.logic_or()
    }

    fn logic_or(&mut self) -> Result<Box<Expr>> {
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

        Ok(left)
    }

    fn logic_and(&mut self) -> Result<Box<Expr>> {
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
        let op_span = self.prev.span;

        let expr = self.unary()?;
        let span = op_span.to(self.prev.span);

        Ok(Box::new(Expr {
            kind: ExprKind::Unary {
                op: Spanned::new(op, op_span),
                expr,
            },
            span,
        }))
    }

    fn call(&mut self) -> Result<Box<Expr>> {
        let mut expr = self.primary()?;

        loop {
            if self.eat(OpenParen) {
                let args = self.finish_call()?;
                let span = expr.span.to(self.prev.span);
                if let ExprKind::Field(callee, name) = expr.kind {
                    expr = Box::new(Expr {
                        kind: ExprKind::MethodCall { callee, name, args },
                        span,
                    });
                } else {
                    expr = Box::new(Expr {
                        kind: ExprKind::Call { callee: expr, args },
                        span,
                    });
                }
            } else if self.eat(Dot) {
                let name = if self.eat(Ident)
                    || self.eat(Literal {
                        kind: LiteralKind::Int,
                    }) {
                    self.prev.clone()
                } else {
                    return self
                        .handler
                        .mk_err(self.curr.span, "Expected field or method name");
                };
                let span = expr.span.to(name.span);
                expr = Box::new(Expr {
                    kind: ExprKind::Field(expr, name),
                    span,
                })
            } else {
                break;
            }
        }

        Ok(expr)
    }

    fn finish_call(&mut self) -> Result<Vec<Box<Expr>>> {
        let mut args = vec![];
        while !self.check(CloseParen) && !self.eof() {
            let arg = self.expr()?;
            args.push(arg);

            if !self.eat(Comma) {
                break;
            }
        }

        self.consume(CloseParen, "Expected ')' after arguments")?;
        Ok(args)
    }

    fn primary(&mut self) -> Result<Box<Expr>> {
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
        } else if self.eat(SelfTy) {
            if !self.restrictions.contains(Restrictions::ALLOW_SELF) {
                return self
                    .handler
                    .mk_err(self.prev.span, "`Self` not allowed here");
            }
            return self.path_or_struct();
        } else if self.eat(SelfParam) {
            let span = self.prev.span;
            let name = self.prev.clone();
            return Ok(Box::new(Expr {
                kind: ExprKind::Variable(name),
                span,
            }));
        } else if self.eat(OpenParen) {
            let lo = self.prev.span;
            let mut exprs = vec![];
            while !self.check(CloseParen) && !self.eof() {
                let expr =
                    self.without_restrictions(Restrictions::NO_STRUCT_LITERAL, |this| this.expr())?;
                exprs.push(expr);

                if !self.eat(Comma) {
                    break;
                }
            }

            self.consume(CloseParen, "Expected ')' after expr")?;
            let span = lo.to(self.prev.span);

            return Ok(Box::new(Expr {
                kind: ExprKind::Tuple(exprs),
                span,
            }));
        } else if self.eat(OpenBrace) {
            let lo = self.prev.span;
            let block = self.block()?;
            let span = lo.to(self.prev.span);

            return Ok(Box::new(Expr {
                kind: ExprKind::Block(block),
                span,
            }));
        } else if self.eat(If) {
            return self.if_expr();
        } else if self.eat(Or) || self.eat(OrOr) {
            return self.closure();
        } else {
            return self.handler.mk_err(self.curr.span, "Expected expression");
        };

        Ok(Box::new(Expr {
            kind: ExprKind::Literal(lit, self.prev.span),
            span: self.prev.span,
        }))
    }

    fn path_or_struct(&mut self) -> Result<Box<Expr>> {
        let mut span = self.prev.span;
        let name = self.prev.clone();

        let struct_allowed = !self.restrictions.contains(Restrictions::NO_STRUCT_LITERAL);
        let kind = if self.check(OpenBrace) && (struct_allowed || self.is_certainly_not_a_block()) {
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
                return self.handler.mk_err(
                    span,
                    "struct literal not allowed here. Use parentheses around it",
                );
            }

            ExprKind::Struct(name, fields, false)
        } else if self.eat(OpenParen) {
            let mut fields = vec![];
            while !self.check(CloseParen) && !self.eof() {
                let expr = self.expr()?;
                let name = Token {
                    span: expr.span,
                    kind: TokenKind::Ident,
                    symbol: Symbol::intern(&fields.len().to_string()),
                };
                fields.push(Field { name, expr });
                if !self.eat(Comma) {
                    break;
                }
            }
            self.consume(CloseParen, "Expected ')'")?;
            span = span.to(self.prev.span);
            ExprKind::Struct(name, fields, true)
        } else if self.check(ColonColon) {
            let ty = self.token_to_ty()?;
            self.consume(ColonColon, "Expected '::'")?;
            let method_name = self.consume(Ident, "Expected identifier")?;
            span = span.to(self.prev.span);
            let assoc_method = ExprKind::AssocMethod {
                ty,
                name: method_name,
            };

            if self.eat(OpenParen) {
                let callee = Box::new(Expr {
                    kind: assoc_method,
                    span,
                });
                let args = self.finish_call()?;
                span = span.to(self.prev.span);
                ExprKind::Call { callee, args }
            } else {
                assoc_method
            }
        } else {
            ExprKind::Variable(name)
        };

        Ok(Box::new(Expr { kind, span }))
    }

    fn closure(&mut self) -> Result<Box<Expr>> {
        let lo = self.prev.span;
        let params = match self.prev.kind {
            Or => {
                let params = self.params(Or, true)?;
                self.consume(Or, "Expected '|' after closure parameters")?;
                params
            }
            _ => vec![],
        };

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
        Ok(Box::new(Expr {
            kind: ExprKind::Closure { params, ret, body },
            span,
        }))
    }

    fn if_expr(&mut self) -> Result<Box<Expr>> {
        let lo = self.prev.span;
        let cond = self.with_restrictions(Restrictions::NO_STRUCT_LITERAL, |this| this.expr())?;
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
        Ok(Box::new(Expr {
            kind: ExprKind::If {
                cond,
                then_clause,
                else_clause,
            },
            span,
        }))
    }

    fn params(&mut self, closing_delim: TokenKind, infer_ty: bool) -> Result<Vec<Param>> {
        let mut params = vec![];
        let mut names = HashSet::new();
        while !self.check(closing_delim) && !self.eof() {
            let param = self.param(infer_ty)?;
            if !names.insert(param.name.symbol) {
                return self
                    .handler
                    .mk_err(param.name.span, "Duplicate parameter name");
            }
            params.push(param);
            if !self.eat(Comma) {
                break;
            }
        }
        Ok(params)
    }

    fn param(&mut self, infer_ty: bool) -> Result<Param> {
        if self.eat(SelfParam) {
            let span = self.prev.span;
            if !self.restrictions.contains(Restrictions::ALLOW_SELF) {
                return self.handler.mk_err(span, "`self` not allowed here");
            }

            let name = self.prev.clone();
            let ty = Ty {
                kind: TyKind::SelfTy,
                span,
            };
            return Ok(Param { name, ty });
        }

        let name = self.consume(Ident, "Expected parameter name")?;

        let ty = if self.eat(Colon) {
            self.parse_ty()?
        } else if infer_ty {
            TyKind::Infer.into()
        } else {
            return self
                .handler
                .mk_err(self.curr.span, "Expected parameter type");
        };

        Ok(Param { name, ty })
    }

    fn parse_ty(&mut self) -> Result<Ty> {
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
            return Ok(Ty {
                kind: TyKind::Fn(params, Box::new(ret)),
                span,
            });
        } else if self.eat(SelfTy) {
            return self.token_to_ty();
        } else if self.eat(OpenParen) {
            let lo = self.prev.span;
            let mut tys = vec![];
            while !self.check(CloseParen) && !self.eof() {
                let ty = self.parse_ty()?;
                tys.push(ty);

                if !self.eat(Comma) {
                    break;
                }
            }
            self.consume(CloseParen, "Expected ')'")?;
            let span = lo.to(self.prev.span);

            let kind = match tys.len() {
                0 => TyKind::Unit,
                1 => return Ok(tys.pop().unwrap()),
                _ => TyKind::Tuple(tys),
            };

            return Ok(Ty { kind, span });
        }

        self.consume(Ident, "Expected Type name")?;
        self.token_to_ty()
    }

    fn token_to_ty(&self) -> Result<Ty> {
        if self.prev.is_self_ty() {
            if !self.restrictions.contains(Restrictions::ALLOW_SELF) {
                return self
                    .handler
                    .mk_err(self.prev.span, "`Self` not allowed here");
            }
            return Ok(Ty {
                span: self.prev.span,
                kind: TyKind::SelfTy,
            });
        }

        let symbol = self.prev.symbol;

        let kind = symbol.as_str_with(|s| match s {
            "_" => TyKind::Infer,
            _ => TyKind::Ident(self.prev.clone()),
        });

        Ok(Ty {
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

    fn with_restrictions<F, R>(&mut self, to_add: Restrictions, f: F) -> R
    where
        F: FnOnce(&mut Self) -> R,
    {
        let save = self.restrictions;
        self.restrictions |= to_add;
        let result = f(self);
        self.restrictions = save;
        result
    }

    fn without_restrictions<F, R>(&mut self, to_remove: Restrictions, f: F) -> R
    where
        F: FnOnce(&mut Self) -> R,
    {
        let save = self.restrictions;
        self.restrictions -= to_remove;
        let result = f(self);
        self.restrictions = save;
        result
    }

    fn consume(&mut self, kind: TokenKind, msg: &'static str) -> Result<Token> {
        if self.check(kind) {
            self.advance();
            return Ok(self.prev.clone());
        }

        return self.handler.mk_err(self.curr.span, msg);
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
