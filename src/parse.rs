pub mod ast;

use self::ast::*;
use crate::{
    err::{ErrHandler, Result},
    lex::{Lexer, LiteralKind, Span, Spanned, Token, TokenKind, TokenKind::*},
    symbol::Symbol,
};
use std::{collections::HashSet, rc::Rc};

pub struct Parser {
    lexer: Lexer,
    handler: Rc<ErrHandler>,
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
    pub fn new(src: Rc<str>, handler: &Rc<ErrHandler>) -> Self {
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
        let mut enums = vec![];
        let mut impls = vec![];
        let mut declared_fns = HashSet::new();
        let mut declared_items = HashSet::new();

        while !self.eof() {
            if self.eat(Fn) {
                let fun = self.function(&mut declared_fns)?;
                functions.push(fun);
            } else if self.eat(Struct) {
                let item = self.struct_item(&mut declared_items, &mut declared_fns)?;
                structs.push(item);
            } else if self.eat(Enum) {
                let e = self.enum_item(&mut declared_items)?;
                enums.push(e);
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
                enums,
                impls,
            })
        }
    }

    fn stmt(&mut self) -> Result<Stmt> {
        match self.full_stmt_without_recovery() {
            Ok(s) => Ok(s),
            Err(()) => {
                self.synchronize();
                Err(())
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

            Ok(Stmt::Expr(block, false))
        } else {
            self.expr_stmt()
        }
    }

    fn block(&mut self) -> Result<Block> {
        let lo = self.prev.span;
        let mut stmts = vec![];
        let mut functions = vec![];
        let mut structs = vec![];
        let mut enums = vec![];
        let mut impls = vec![];
        let mut declared_fns = HashSet::new();
        let mut declared_items = HashSet::new();

        while !self.check(CloseBrace) && !self.eof() {
            if self.eat(Fn) {
                let fun =
                    self.without_restrictions(Restrictions::ALLOW_SELF, |this| this.function(&mut declared_fns))?;
                functions.push(fun);
            } else if self.eat(Struct) {
                let s = self.struct_item(&mut declared_items, &mut declared_fns)?;
                structs.push(s);
            } else if self.eat(Enum) {
                let e = self.enum_item(&mut declared_items)?;
                enums.push(e);
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
            enums,
            impls,
        })
    }

    fn function(&mut self, declared_fns: &mut HashSet<Symbol>) -> Result<Function> {
        let name = self.consume(Ident, "Expected function name")?;
        if !declared_fns.insert(name.symbol) {
            return self
                .handler
                .mk_err(name.span, "Function with same name already defined in this scope");
        }

        let generics = self.generic_params()?;
        self.consume(OpenParen, "Expected '('")?;
        let params = self.params(CloseParen, false)?;
        self.consume(CloseParen, "Expected ')'")?;

        let ret = if self.eat(Arrow) {
            self.parse_ty()?
        } else {
            Ty {
                kind: TyKind::Unit,
                span: name.span,
            }
        };

        self.consume(OpenBrace, "Expected '{'")?;
        let body = self.block()?;

        Ok(Function {
            name,
            generics,
            params,
            ret,
            body,
        })
    }

    fn impl_item(&mut self) -> Result<ast::Impl> {
        let generics = self.generic_params()?;
        let ty = self.parse_ty()?;
        self.with_restrictions(Restrictions::ALLOW_SELF, |this| {
            this.consume(OpenBrace, "Expected '{'")?;

            let mut functions = vec![];
            let mut declared_fns = HashSet::new();

            while this.eat(Fn) {
                let fun = this.function(&mut declared_fns)?;
                functions.push(fun);
            }

            this.consume(CloseBrace, "Expected '}'")?;
            Ok(ast::Impl {
                ty,
                generics,
                methods: functions,
            })
        })
    }

    fn enum_item(&mut self, declared_items: &mut HashSet<Symbol>) -> Result<ast::Enum> {
        self.with_restrictions(Restrictions::ALLOW_SELF, |this| this.enum_item_inner(declared_items))
    }

    fn enum_item_inner(&mut self, declared_items: &mut HashSet<Symbol>) -> Result<ast::Enum> {
        let name = self.consume(Ident, "Expected enum name")?;
        if !declared_items.insert(name.symbol) {
            return self
                .handler
                .mk_err(name.span, "An item with same name already defined in this scope");
        }

        self.consume(OpenBrace, "Expected '{'")?;
        let mut variants = vec![];
        let mut names = HashSet::new();
        while !self.check(CloseBrace) && !self.eof() {
            let variant = self.variant()?;
            if !names.insert(variant.name.symbol) {
                return self.handler.mk_err(variant.name.span, "Duplicate variant name");
            }
            variants.push(variant);
            if !self.eat(Comma) {
                break;
            }
        }
        self.consume(CloseBrace, "Expected '}'")?;

        Ok(ast::Enum { name, variants })
    }

    fn variant(&mut self) -> Result<ast::EnumVariant> {
        let name = self.consume(Ident, "Expected variant name")?;
        let kind = if self.check(OpenBrace) {
            ast::EnumVariantKind::Struct(self.struct_fields(&name, None)?)
        } else if self.check(OpenParen) {
            ast::EnumVariantKind::Tuple(self.struct_fields(&name, None)?)
        } else {
            ast::EnumVariantKind::Empty
        };
        Ok(ast::EnumVariant { name, kind })
    }

    fn struct_item(
        &mut self,
        declared_items: &mut HashSet<Symbol>,
        declared_fns: &mut HashSet<Symbol>,
    ) -> Result<ast::Struct> {
        self.with_restrictions(Restrictions::ALLOW_SELF, |this| {
            this.struct_item_inner(declared_items, declared_fns)
        })
    }

    fn struct_item_inner(
        &mut self,
        declared_items: &mut HashSet<Symbol>,
        declared_fns: &mut HashSet<Symbol>,
    ) -> Result<ast::Struct> {
        let name = self.consume(Ident, "Expected struct name")?;
        if !declared_items.insert(name.symbol) {
            return self
                .handler
                .mk_err(name.span, "An item with same name already defined in this scope");
        }

        let generics = self.generic_params()?;
        let is_tuple = self.check(OpenParen);
        let fields = self.struct_fields(&name, Some(declared_fns))?;
        if is_tuple {
            self.consume(SemiColon, "Expected ';'")?;
        }
        Ok(ast::Struct {
            name,
            generics,
            fields,
            is_tuple,
        })
    }

    fn generic_params(&mut self) -> Result<GenericParams> {
        if !self.eat(Lt) {
            return Ok(GenericParams {
                params: Vec::new(),
                span: Span::DUMMY,
            });
        }

        let mut params = Vec::<GenericParam>::new();
        let lo = self.curr.span;
        while !self.check(Gt) && !self.eof() {
            let name = self.consume(Ident, "Expected generic parameter")?;
            if params.iter().any(|g| g.name.symbol == name.symbol) {
                return self.handler.mk_err(name.span, "Duplicate generic parameter name");
            }
            params.push(GenericParam { name });
            if !self.eat(Comma) {
                break;
            }
        }
        let span = lo.to(self.prev.span);
        self.consume(Gt, "Expected '>'")?;
        Ok(GenericParams { params, span })
    }

    fn generic_args(&mut self) -> Result<GenericArgs> {
        if !self.eat(Lt) {
            return Ok(GenericArgs {
                args: Vec::new(),
                span: Span::DUMMY,
            });
        }

        let lo = self.curr.span;
        let mut args = Vec::<GenericArg>::new();
        while !self.check(Gt) && !self.eof() {
            let ty = self.parse_ty()?;
            args.push(GenericArg { ty });
            if !self.eat(Comma) {
                break;
            }
        }
        let span = lo.to(self.prev.span);
        self.consume(Gt, "Expected '>'")?;
        Ok(GenericArgs { args, span })
    }

    fn struct_fields(
        &mut self,
        name: &Token,
        declared_fns: Option<&mut HashSet<Symbol>>,
    ) -> Result<Vec<ast::StructField>> {
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

            Ok(fields)
        } else if self.eat(OpenParen) {
            if let Some(declared_fns) = declared_fns {
                if !declared_fns.insert(name.symbol) {
                    return self
                        .handler
                        .mk_err(name.span, "Another item with same name already defined in this scope");
                }
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

            Ok(fields)
        } else {
            self.handler.mk_err(self.curr.span, "Expected '{' or '('")
        }
    }

    fn struct_field(&mut self) -> Result<ast::StructField> {
        let name = self.consume(Ident, "Expected field name")?;
        self.consume(Colon, "Expected ':' after field name")?;
        let ty = self.parse_ty()?;
        if ty.kind == TyKind::Infer {
            return self.handler.mk_err(ty.span, "not allowed in type signatures");
        }

        Ok(ast::StructField { name, ty })
    }

    fn let_decl(&mut self) -> Result<Stmt> {
        let name = self.consume(Ident, "Expected variable name.")?;

        let ty = if self.eat(Colon) {
            self.parse_ty()?
        } else {
            Ty {
                kind: TyKind::Infer,
                span: name.span,
            }
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

        if self.eat(SemiColon) {
            return Ok(Stmt::Expr(expr, true));
        }

        if self.require_semi(&expr) {
            return self
                .handler
                .mk_err(self.curr.span, "Expected one of `.`, `;`, `}` or an operator");
        }

        Ok(Stmt::Expr(expr, false))
    }

    fn require_semi(&self, expr: &Expr) -> bool {
        if self.check(Dot) || self.check(CloseBrace) || self.check_op() || expr.is_block_like() {
            return false;
        }

        true
    }

    fn expr(&mut self) -> Result<Expr> {
        let mut expr = self.logic_or()?;

        if self.eat(Eq) {
            let val = self.logic_or()?;
            let span = expr.span.to(self.prev.span);
            expr = Expr {
                kind: ExprKind::Assign {
                    lhs: Box::new(expr),
                    rhs: Box::new(val),
                },
                span,
            };
        } else if self.eat(PlusEq) || self.eat(MinusEq) || self.eat(StarEq) || self.eat(SlashEq) {
            let op = match self.prev.kind {
                PlusEq => BinOp::Add,
                MinusEq => BinOp::Sub,
                StarEq => BinOp::Mul,
                SlashEq => BinOp::Sub,
                _ => unreachable!(),
            };
            let op = Spanned::new(op, self.prev.span);
            let val = self.logic_or()?;
            let span = expr.span.to(self.prev.span);
            expr = Expr {
                kind: ExprKind::OpAssign {
                    lhs: Box::new(expr),
                    rhs: Box::new(val),
                    op,
                },
                span,
            };
        }
        Ok(expr)
    }

    fn logic_or(&mut self) -> Result<Expr> {
        let mut lhs = self.logic_and()?;

        while self.eat(OrOr) {
            let op_span = self.prev.span;
            let rhs = self.logic_and()?;

            let span = lhs.span.to(rhs.span);
            lhs = Expr {
                kind: ExprKind::Binary {
                    op: Spanned::new(BinOp::Or, op_span),
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                },
                span,
            };
        }

        Ok(lhs)
    }

    fn logic_and(&mut self) -> Result<Expr> {
        let mut lhs = self.equality()?;

        while self.eat(AndAnd) {
            let op_span = self.prev.span;
            let rhs = self.equality()?;
            let span = lhs.span.to(rhs.span);

            lhs = Expr {
                kind: ExprKind::Binary {
                    op: Spanned::new(BinOp::And, op_span),
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                },
                span,
            };
        }

        Ok(lhs)
    }

    fn equality(&mut self) -> Result<Expr> {
        let mut lhs = self.comparison()?;

        loop {
            let op = if self.eat(Ne) {
                BinOp::Ne
            } else if self.eat(EqEq) {
                BinOp::Eq
            } else {
                break;
            };
            let op_span = self.prev.span;
            let rhs = self.comparison()?;
            let span = lhs.span.to(rhs.span);

            lhs = Expr {
                kind: ExprKind::Binary {
                    op: Spanned::new(op, op_span),
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                },
                span,
            };
        }

        Ok(lhs)
    }

    fn comparison(&mut self) -> Result<Expr> {
        let mut lhs = self.addition()?;

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
            let rhs = self.addition()?;
            let span = lhs.span.to(rhs.span);

            lhs = Expr {
                kind: ExprKind::Binary {
                    op: Spanned::new(op, op_span),
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                },
                span,
            };
        }

        Ok(lhs)
    }

    fn addition(&mut self) -> Result<Expr> {
        let mut lhs = self.multiplication()?;

        loop {
            let op = if self.eat(Minus) {
                BinOp::Sub
            } else if self.eat(Plus) {
                BinOp::Add
            } else {
                break;
            };
            let op_span = self.prev.span;
            let rhs = self.multiplication()?;
            let span = lhs.span.to(rhs.span);

            lhs = Expr {
                kind: ExprKind::Binary {
                    op: Spanned::new(op, op_span),
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                },
                span,
            };
        }

        Ok(lhs)
    }

    fn multiplication(&mut self) -> Result<Expr> {
        let mut lhs = self.unary()?;

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
            let rhs = self.unary()?;
            let span = lhs.span.to(rhs.span);

            lhs = Expr {
                kind: ExprKind::Binary {
                    op: Spanned::new(op, op_span),
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                },
                span,
            };
        }

        Ok(lhs)
    }

    fn unary(&mut self) -> Result<Expr> {
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

        Ok(Expr {
            kind: ExprKind::Unary {
                op: Spanned::new(op, op_span),
                expr: Box::new(expr),
            },
            span,
        })
    }

    fn call(&mut self) -> Result<Expr> {
        let mut expr = self.primary()?;

        loop {
            if self.eat(OpenParen) {
                let args = self.finish_call()?;
                let span = expr.span.to(self.prev.span);
                if let ExprKind::Field(callee, name) = expr.kind {
                    expr = Expr {
                        kind: ExprKind::MethodCall { callee, name, args },
                        span,
                    };
                } else {
                    expr = Expr {
                        kind: ExprKind::Call {
                            callee: Box::new(expr),
                            args,
                        },
                        span,
                    };
                }
            } else if self.eat(Dot) {
                expr = self.parse_dot_suffix_expr(expr)?;
            } else if self.eat(OpenSquare) {
                let index = self.expr()?;
                self.consume(CloseSquare, "Expected ']'")?;
                let span = expr.span.to(self.prev.span);
                expr = Expr {
                    kind: ExprKind::ArrayAccess(Box::new(expr), Box::new(index)),
                    span,
                };
            } else {
                break;
            }
        }

        Ok(expr)
    }

    fn parse_dot_suffix_expr(&mut self, mut expr: Expr) -> Result<Expr> {
        match self.curr.kind {
            Ident | Literal { kind: LiteralKind::Int } => {
                self.advance();
                let name = self.prev.clone();
                let span = expr.span.to(name.span);
                Ok(Expr {
                    kind: ExprKind::Field(Box::new(expr), name),
                    span,
                })
            }
            Literal {
                kind: LiteralKind::Float,
            } => {
                let mut lo = self.curr.span.lo();
                for s in self.curr.symbol.to_string().split('.') {
                    let token_span = Span::new(lo, lo + s.len());
                    lo += 1 + s.len();
                    let token = Token::new(Literal { kind: LiteralKind::Int }, Symbol::intern(s), token_span);
                    let span = expr.span.to(token.span);
                    expr = Expr {
                        kind: ExprKind::Field(Box::new(expr), token),
                        span,
                    }
                }
                self.advance();
                Ok(expr)
            }
            _ => return self.handler.mk_err(self.curr.span, "Expected field or method name"),
        }
    }

    fn finish_call(&mut self) -> Result<Vec<Expr>> {
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

    fn primary(&mut self) -> Result<Expr> {
        if let Some(lit) = self.lit() {
            return lit;
        }

        if self.eat(Ident) {
            return self.path_or_struct();
        }

        if self.eat(While) {
            let span = self.prev.span;
            let cond = self.with_restrictions(Restrictions::NO_STRUCT_LITERAL, |this| this.expr())?;

            self.consume(OpenBrace, "Expected '{' after the condition")?;
            let body = self.block()?;
            let span = span.to(self.prev.span);
            return Ok(Expr {
                kind: ExprKind::While {
                    cond: Box::new(cond),
                    body,
                },
                span,
            });
        }

        if self.eat(Loop) {
            let span = self.prev.span;
            self.consume(OpenBrace, "Expected '{'")?;
            let block = self.block()?;
            let span = span.to(self.prev.span);
            return Ok(Expr {
                kind: ExprKind::Loop(block),
                span,
            });
        }

        if self.eat(SelfTy) {
            if !self.restrictions.contains(Restrictions::ALLOW_SELF) {
                return self.handler.mk_err(self.prev.span, "`Self` not allowed here");
            }
            return self.path_or_struct();
        }

        if self.eat(SelfParam) {
            let span = self.prev.span;
            let name = self.prev.clone();
            return Ok(Expr {
                kind: ExprKind::Variable(name),
                span,
            });
        }

        if self.eat(OpenParen) {
            let lo = self.prev.span;
            let mut exprs = vec![];
            while !self.check(CloseParen) && !self.eof() {
                let expr = self.without_restrictions(Restrictions::NO_STRUCT_LITERAL, |this| this.expr())?;
                exprs.push(expr);

                if !self.eat(Comma) {
                    break;
                }
            }

            self.consume(CloseParen, "Expected ')' after expr")?;
            let span = lo.to(self.prev.span);

            return Ok(Expr {
                kind: ExprKind::Tuple(exprs),
                span,
            });
        }

        if self.eat(OpenSquare) {
            let lo = self.prev.span;

            let mut values = vec![];

            if !self.check(CloseSquare) {
                let expr = self.expr()?;

                if self.eat(SemiColon) {
                    let times = self.expr()?;
                    self.consume(CloseSquare, "Expected ']'")?;
                    let span = lo.to(self.prev.span);
                    return Ok(Expr {
                        kind: ExprKind::ArrayRepeat(Box::new(expr), Box::new(times)),
                        span,
                    });
                }

                values.push(expr);
                while self.eat(Comma) && !self.check(CloseSquare) && !self.eof() {
                    let expr = self.expr()?;
                    values.push(expr);
                }
            }

            self.consume(CloseSquare, "Expected ']'")?;
            let span = lo.to(self.prev.span);
            return Ok(Expr {
                kind: ExprKind::Array(values),
                span,
            });
        }

        if self.eat(OpenBrace) {
            let lo = self.prev.span;
            let block = self.block()?;
            let span = lo.to(self.prev.span);

            return Ok(Expr {
                kind: ExprKind::Block(block),
                span,
            });
        }

        if self.eat(If) {
            return self.if_expr();
        }

        if self.eat(Or) || self.eat(OrOr) {
            return self.closure();
        }

        if self.eat(Return) {
            let mut span = self.prev.span;
            let mut expr = None;
            if !self.check(Comma) && !self.check(SemiColon) && !self.check(CloseBrace) {
                expr = Some(Box::new(self.expr()?));
                span = span.to(self.prev.span);
            }
            return Ok(Expr {
                kind: ExprKind::Return(expr),
                span,
            });
        }

        if self.eat(Continue) {
            return Ok(Expr {
                kind: ExprKind::Continue,
                span: self.prev.span,
            });
        }

        if self.eat(Break) {
            let mut span = self.prev.span;
            let mut expr = None;
            if !self.check(Comma) && !self.check(SemiColon) && !self.check(CloseBrace) {
                expr = Some(Box::new(self.expr()?));
                span = span.to(self.prev.span);
            }
            return Ok(Expr {
                kind: ExprKind::Break(expr),
                span,
            });
        }

        self.handler.mk_err(self.curr.span, "Expected expression")
    }

    fn lit(&mut self) -> Option<Result<Expr>> {
        let lit = if self.eat(False) {
            Lit::Bool(false)
        } else if self.eat(True) {
            Lit::Bool(true)
        } else if self.eat(Literal { kind: LiteralKind::Int }) {
            match self.prev.symbol.parse().map(Lit::Integer) {
                Ok(lit) => lit,
                Err(_) => {
                    self.handler
                        .report(self.prev.span, "Number too large to fit into `int`");
                    Lit::Err
                }
            }
        } else if self.eat(Literal {
            kind: LiteralKind::Float,
        }) {
            Lit::Float(self.prev.symbol)
        } else if self.eat(Literal { kind: LiteralKind::Str }) {
            Lit::Str(self.prev.symbol)
        } else {
            return None;
        };
        Some(Ok(Expr {
            kind: ExprKind::Literal(lit, self.prev.span),
            span: self.prev.span,
        }))
    }

    fn path_or_struct(&mut self) -> Result<Expr> {
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
                    Expr {
                        kind: ExprKind::Variable(name.clone()),
                        span: var_span,
                    }
                };
                fields.push(Field { name, expr });

                if !self.eat(Comma) {
                    break;
                }
            }
            self.consume(CloseBrace, "Expected '}'")?;
            span = span.to(self.prev.span);

            if self.restrictions.contains(Restrictions::NO_STRUCT_LITERAL) {
                return self
                    .handler
                    .mk_err(span, "struct literal not allowed here. Use parentheses around it");
            }

            ExprKind::Struct(name.into(), fields, false)
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
            ExprKind::Struct(name.into(), fields, true)
        } else if self.check(ColonColon) {
            let mut path_segments = vec![name];
            while self.eat(ColonColon) {
                let segment = self.consume(Ident, "Expected identifier")?;
                path_segments.push(segment);
            }
            span = span.to(self.prev.span);
            let path = ExprKind::Path(path_segments.into());

            if self.eat(OpenParen) {
                let callee = Box::new(Expr { kind: path, span });
                let args = self.finish_call()?;
                span = span.to(self.prev.span);
                ExprKind::Call { callee, args }
            } else {
                path
            }
        } else {
            ExprKind::Variable(name)
        };

        Ok(Expr { kind, span })
    }

    fn closure(&mut self) -> Result<Expr> {
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
            let span = lo.to(self.prev.span);
            Ty {
                kind: TyKind::Infer,
                span,
            }
        };

        let body = if only_block_allowed {
            self.consume(OpenBrace, "Expected '{'")?;
            let lo = self.prev.span;
            let block = self.block()?;
            let span = lo.to(self.prev.span);

            Expr {
                kind: ExprKind::Block(block),
                span,
            }
        } else {
            self.expr()?
        };

        let span = lo.to(self.prev.span);
        Ok(Expr {
            kind: ExprKind::Closure {
                params,
                ret,
                body: Box::new(body),
            },
            span,
        })
    }

    fn if_expr(&mut self) -> Result<Expr> {
        let lo = self.prev.span;
        let cond = self.with_restrictions(Restrictions::NO_STRUCT_LITERAL, |this| this.expr())?;
        self.consume(OpenBrace, "Expected '{' after if condition")?;
        let then_clause = self.block()?;
        let mut else_clause = None;
        if self.eat(Else) {
            if self.eat(If) {
                else_clause = Some(Box::new(self.if_expr()?));
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
        Ok(Expr {
            kind: ExprKind::If {
                cond: Box::new(cond),
                then_clause,
                else_clause,
            },
            span,
        })
    }

    fn params(&mut self, closing_delim: TokenKind, infer_ty: bool) -> Result<Vec<Param>> {
        let mut params = vec![];
        let mut names = HashSet::new();
        while !self.check(closing_delim) && !self.eof() {
            let param = self.param(infer_ty)?;
            if !names.insert(param.name.symbol) {
                return self.handler.mk_err(param.name.span, "Duplicate parameter name");
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
            Ty {
                kind: TyKind::Infer,
                span: name.span,
            }
        } else {
            return self.handler.mk_err(self.curr.span, "Expected parameter type");
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
                let span = lo.to(self.prev.span);
                Ty {
                    kind: TyKind::Unit,
                    span,
                }
            };

            let span = lo.to(self.prev.span);
            return Ok(Ty {
                kind: TyKind::Fn(params, Box::new(ret)),
                span,
            });
        } else if self.restrictions.contains(Restrictions::ALLOW_SELF) && self.eat(SelfTy) {
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
        } else if self.eat(OpenSquare) {
            let lo = self.prev.span;
            let ty = self.parse_ty()?;
            self.consume(CloseSquare, "Expected ']'")?;
            let span = lo.to(self.prev.span);
            return Ok(Ty {
                kind: TyKind::Array(Box::new(ty)),
                span,
            });
        }

        self.consume(Ident, "Expected Type name")?;
        self.token_to_ty()
    }

    fn token_to_ty(&mut self) -> Result<Ty> {
        if self.prev.is_self_ty() {
            if !self.restrictions.contains(Restrictions::ALLOW_SELF) {
                return self.handler.mk_err(self.prev.span, "`Self` not allowed here");
            }
            return Ok(Ty {
                span: self.prev.span,
                kind: TyKind::SelfTy,
            });
        }

        let symbol = self.prev.symbol;

        let kind = if symbol == Symbol::intern("_") {
            TyKind::Infer
        } else {
            let ident = self.prev.clone();
            let generic_args = self.generic_args()?;
            TyKind::Ident(ident, generic_args)
        };

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

    fn check_op(&self) -> bool {
        self.curr.kind.is_op()
    }

    fn consume(&mut self, kind: TokenKind, msg: &'static str) -> Result<Token> {
        if self.check(kind) {
            self.advance();
            return Ok(self.prev.clone());
        }

        self.handler.mk_err(self.curr.span, msg)
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
    use crate::lex::Span;

    use super::*;

    fn parse_expr(src: &str) -> Expr {
        let src: Rc<str> = Rc::from(src);
        let handler = Rc::new(ErrHandler::new(&src));
        let mut parser = Parser::new(src, &handler);
        parser.expr().unwrap()
    }

    macro_rules! expr {
        ($kind:expr, $span:expr) => {
            Expr {
                kind: $kind,
                span: $span.into(),
            }
        };
    }

    macro_rules! litint {
        ($val:literal, $span:expr) => {
            expr!(ExprKind::Literal(Lit::Integer($val), $span.into()), $span)
        };
    }

    macro_rules! litbool {
        ($val:literal, $span:expr) => {
            expr!(ExprKind::Literal(Lit::Bool($val), $span.into()), $span)
        };
    }

    macro_rules! binop {
        ($op:ident @ $op_span:expr, $lhs:expr, $rhs:expr, $span:expr) => {
            expr!(
                ExprKind::Binary {
                    op: Spanned::new(BinOp::$op, $op_span.into()),
                    lhs: Box::new($lhs),
                    rhs: Box::new($rhs),
                },
                $span
            )
        };
    }

    macro_rules! block {
        ($stmts:expr, $span:expr) => {
            Block {
                stmts: $stmts,
                span: $span.into(),
                functions: vec![],
                structs: vec![],
                enums: vec![],
                impls: vec![],
            }
        };
    }

    #[test]
    fn add() {
        assert_eq!(
            parse_expr("1 + 1"),
            binop!(Add @ 2..3, litint!(1, 0..1), litint!(1, 4.. 5), 0.. 5),
        );
    }

    #[test]
    fn combine() {
        assert_eq!(
            parse_expr("1 * 1 - 1 / 1 + 1"),
            binop!(
                Add @ 14..15,
                binop!(
                    Sub @ 6..7,
                    binop!(Mul @ 2..3, litint!(1, 0..1), litint!(1, 4..5), 0..5),
                    binop!(Div @ 10..11, litint!(1, 8..9), litint!(1, 12..13), 8..13),
                    0..13
                ),
                litint!(1, 16..17),
                0..17
            ),
        );
    }

    #[test]
    fn if_expr() {
        assert_eq!(
            parse_expr("if true { 10 }"),
            Expr {
                kind: ExprKind::If {
                    cond: Box::new(litbool!(true, 3..7)),
                    then_clause: block! {
                        vec![Stmt::Expr(litint!(10, 10..12), false)], 8..14
                    },
                    else_clause: None,
                },
                span: Span::new(0, 14),
            }
        );
    }

    #[test]
    fn if_else_expr() {
        assert_eq!(
            parse_expr("if true { 10 } else { 20 }"),
            Expr {
                kind: ExprKind::If {
                    cond: Box::new(litbool!(true, 3..7)),
                    then_clause: block! {
                        vec![Stmt::Expr(litint!(10, 10..12), false)], 8..14
                    },
                    else_clause: Some(Box::new(Expr {
                        kind: ExprKind::Block(block! {
                            vec![Stmt::Expr(litint!(20, 22..24), false)], 20..26
                        }),
                        span: Span::new(20, 26),
                    })),
                },
                span: Span::new(0, 26),
            }
        );
    }
}
