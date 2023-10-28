use std::{collections::HashMap, rc::Rc};

use crate::{
    err::{ErrHandler, Result},
    lex::Token,
    parse::ast::{self, GenericArgs, GenericParams},
    symbol::SymbolTable,
};

use super::{
    hir,
    ty::{Ty, TyContext, TypeVar},
};

pub fn annotate(ast: &ast::Ast, env: &mut TyContext, handler: &ErrHandler) -> Result<hir::Ast> {
    Annotate::new(env, handler).annotate_ast(ast)
}

struct Annotate<'a> {
    tyctx: &'a mut TyContext,
    bindings: SymbolTable<TypeVar>,
    functions: SymbolTable<TypeVar>,
    types: SymbolTable<TypeVar>,
    handler: &'a ErrHandler,
    has_enclosing_fn: bool,
    has_enclosing_loop: bool,
    enclosing_self_ty: Option<TypeVar>,
}

impl<'a> Annotate<'a> {
    fn new(env: &'a mut TyContext, handler: &'a ErrHandler) -> Self {
        Self {
            tyctx: env,
            bindings: SymbolTable::new(),
            functions: SymbolTable::new(),
            types: SymbolTable::new(),
            handler,
            has_enclosing_fn: false,
            has_enclosing_loop: false,
            enclosing_self_ty: None,
        }
    }

    fn annotate_ast(&mut self, ast: &ast::Ast) -> Result<hir::Ast> {
        self.declare_structs(&ast.structs);
        self.declare_enums(&ast.enums);
        let structs = self.annotate_structs(&ast.structs)?;
        let enums = self.annotate_enums(&ast.enums)?;
        self.annotate_fn_headers(&ast.functions);
        let impls = self.annotate_impls(&ast.impls)?;
        let functions = self.annotate_fns(&ast.functions)?;
        let stmts = self.annotate_stmts(&ast.stmts)?;
        Ok(hir::Ast {
            structs,
            enums,
            impls,
            functions,
            stmts,
        })
    }

    fn annotate_stmts(&mut self, stmts: &[ast::Stmt]) -> Result<Vec<hir::Stmt>> {
        stmts.iter().map(|s| self.annotate_stmt(s)).collect()
    }

    fn annotate_stmt(&mut self, stmt: &ast::Stmt) -> Result<hir::Stmt> {
        match stmt {
            ast::Stmt::Expr(expr, semicolon) => Ok(hir::Stmt::Expr(self.annotate_expr(expr)?, *semicolon)),
            ast::Stmt::Let { name, init, ty } => {
                let init = match init {
                    Some(e) => Some(self.annotate_expr(e)?),
                    None => None,
                };

                let let_ty = self.ast_ty_to_ty(ty)?;
                self.bindings.insert(name.symbol, let_ty);

                Ok(hir::Stmt::Let {
                    name: name.clone(),
                    ty: let_ty,
                    init,
                })
            }
        }
    }

    fn annotate_expr(&mut self, expr: &ast::Expr) -> Result<hir::Expr> {
        let ty = self.tyctx.new_type_var();
        let (kind, span) = (&expr.kind, expr.span);
        let kind = match kind {
            ast::ExprKind::Binary { op, lhs, rhs } => {
                let lhs = self.annotate_expr(lhs)?;
                let rhs = self.annotate_expr(rhs)?;
                hir::ExprKind::Binary {
                    op: *op,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                }
            }
            ast::ExprKind::Tuple(exprs) => match &exprs[..] {
                [] => hir::ExprKind::Literal(ast::Lit::Unit, self.tyctx.unit(), expr.span),
                [e] => return self.annotate_expr(&e),
                exprs => {
                    let exprs = exprs.iter().map(|e| self.annotate_expr(e)).collect::<Result<_>>()?;
                    hir::ExprKind::Tuple(exprs)
                }
            },
            ast::ExprKind::Literal(lit, span) => {
                let ty = match lit {
                    ast::Lit::Unit => self.tyctx.unit(),
                    ast::Lit::Str(_) => self.tyctx.str(),
                    ast::Lit::Integer(_) => self.tyctx.int(),
                    ast::Lit::Float(_) => self.tyctx.float(),
                    ast::Lit::Bool(_) => self.tyctx.bool(),
                    ast::Lit::Err => self.tyctx.new_type_var(),
                };
                hir::ExprKind::Literal(lit.clone(), ty, *span)
            }
            ast::ExprKind::Unary { op, expr } => {
                let expr = self.annotate_expr(expr)?;
                hir::ExprKind::Unary {
                    op: *op,
                    expr: Box::new(expr),
                }
            }
            ast::ExprKind::Variable(t) => match self.bindings.get(t.symbol).or_else(|| self.functions.get(t.symbol)) {
                Some(ty) => hir::ExprKind::Variable(t.clone(), *ty),
                None => {
                    log::debug!("Variable `{}` not found", t.symbol);
                    log::trace!("Bindings: {:?}", self.bindings);
                    log::trace!("Functions: {:?}", self.functions);
                    return self.handler.mk_err(t.span, "Not found in this scope");
                }
            },
            ast::ExprKind::Block(block) => hir::ExprKind::Block(self.annotate_block(block)?),
            ast::ExprKind::If {
                cond,
                then_clause,
                else_clause,
            } => {
                let cond = self.annotate_expr(cond)?;
                let then_clause = self.annotate_block(then_clause)?;
                let else_clause = match else_clause {
                    Some(e) => {
                        let e = self.annotate_expr(e)?;
                        Some(Box::new(e))
                    }
                    None => None,
                };
                hir::ExprKind::If {
                    cond: Box::new(cond),
                    then_clause,
                    else_clause,
                }
            }
            ast::ExprKind::Closure { params, ret, body } => self.enter_block_scope(|this| {
                let params = this.annotate_params(params)?;
                let ret = this.ast_ty_to_ty(ret)?;
                this.has_enclosing_fn = true;
                let body = this.annotate_expr(body)?;
                this.has_enclosing_fn = false;
                Ok(hir::ExprKind::Closure {
                    params,
                    ret,
                    body: Box::new(body),
                })
            })?,
            ast::ExprKind::Call { callee, args } => {
                let callee = self.annotate_expr(callee)?;
                let args = args.iter().map(|arg| self.annotate_expr(arg)).collect::<Result<_>>()?;
                hir::ExprKind::Call {
                    callee: Box::new(callee),
                    args,
                }
            }
            ast::ExprKind::Struct(name, fields, tuple) => {
                let name = match &name.segments[..] {
                    [name] => name,
                    _ => panic!("Expected single segment in path"),
                };
                if name.is_self_ty() {
                    let ty = self.tyctx.instantiate_generic_ty(self.enclosing_self_ty.unwrap());
                    hir::ExprKind::Struct(name.clone(), self.annotate_fields(fields)?, ty)
                } else {
                    match self.types.get(name.symbol).copied() {
                        Some(ty) => {
                            let ty = self.tyctx.instantiate_generic_ty(ty);
                            hir::ExprKind::Struct(name.clone(), self.annotate_fields(fields)?, ty)
                        }
                        None if *tuple => {
                            if self.functions.is_defined(name.symbol) || self.bindings.is_defined(name.symbol) {
                                let callee = ast::Expr {
                                    span: name.span,
                                    kind: ast::ExprKind::Variable(name.clone()),
                                };
                                let callee = self.annotate_expr(&callee)?;
                                let args = fields
                                    .iter()
                                    .map(|f| self.annotate_expr(&f.expr))
                                    .collect::<Result<_>>()?;
                                hir::ExprKind::Call {
                                    callee: Box::new(callee),
                                    args,
                                }
                            } else {
                                log::debug!("Function `{}` not found", name.symbol);
                                return self.handler.mk_err(name.span, "Not found in this scope");
                            }
                        }
                        None => {
                            log::debug!("Struct `{}` not found", name.symbol);
                            return self.handler.mk_err(name.span, "Not found in this scope");
                        }
                    }
                }
            }
            ast::ExprKind::Field(expr, name) => {
                let expr = self.annotate_expr(expr)?;
                hir::ExprKind::Field(Box::new(expr), name.clone())
            }
            ast::ExprKind::MethodCall { callee, name, args } => {
                let callee = self.annotate_expr(callee)?;
                let args = args.iter().map(|arg| self.annotate_expr(arg)).collect::<Result<_>>()?;
                hir::ExprKind::MethodCall {
                    callee: Box::new(callee),
                    name: name.clone(),
                    args,
                }
            }
            ast::ExprKind::Path(path) => {
                if let [first, second] = &path.segments[..] {
                    let tvar = match self.types.get(first.symbol) {
                        Some(x) => *x,
                        None => return self.handler.mk_err(first.span, "Unknown type"),
                    };
                    hir::ExprKind::AssocMethod {
                        ty: tvar,
                        name: second.clone(),
                    }
                } else {
                    return self.handler.mk_err(expr.span, "Invalid path: Must of form `X::Y`");
                }
            }
            ast::ExprKind::Assign { lhs, rhs } => {
                if !lhs.is_assignable() {
                    return self.handler.mk_err(expr.span, "Cannot assign to this expression");
                }
                let lhs = self.annotate_expr(lhs)?;
                let rhs = self.annotate_expr(rhs)?;
                hir::ExprKind::Assign {
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                }
            }
            ast::ExprKind::OpAssign { lhs, rhs, op } => {
                if !lhs.is_assignable() {
                    return self.handler.mk_err(expr.span, "Cannot assign to this expression");
                }
                let lhs = self.annotate_expr(lhs)?;
                let rhs = self.annotate_expr(rhs)?;
                let rhs = hir::Expr {
                    span: lhs.span.to(rhs.span),
                    kind: hir::ExprKind::Binary {
                        lhs: Box::new(lhs.clone()),
                        rhs: Box::new(rhs),
                        op: *op,
                    },
                    ty: self.tyctx.new_type_var(),
                };
                hir::ExprKind::Assign {
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                }
            }
            ast::ExprKind::Return(e) => {
                if !self.has_enclosing_fn {
                    return self.handler.mk_err(span, "Cannot return without enclosing function");
                }

                let e = match e {
                    Some(e) => {
                        let e = self.annotate_expr(e)?;
                        Some(Box::new(e))
                    }
                    None => None,
                };

                hir::ExprKind::Return(e)
            }
            ast::ExprKind::Break(e) => {
                if !self.has_enclosing_loop {
                    return self.handler.mk_err(span, "Cannot break without an enclosing loop");
                }

                let e = match e {
                    Some(e) => {
                        let e = self.annotate_expr(e)?;
                        Some(Box::new(e))
                    }
                    None => None,
                };

                hir::ExprKind::Break(e)
            }
            ast::ExprKind::Continue => {
                if !self.has_enclosing_loop {
                    return self.handler.mk_err(span, "Cannot continue without an enclosing loop");
                }

                hir::ExprKind::Continue
            }
            ast::ExprKind::While { cond, body } => {
                let cond = self.annotate_expr(cond)?;
                let mut body = self.enter_loop_scope(|this| this.annotate_block(body))?;
                let then_clause = hir::Block {
                    stmts: vec![hir::Stmt::Expr(
                        hir::Expr {
                            kind: hir::ExprKind::Break(None),
                            span,
                            ty: self.tyctx.unit(),
                        },
                        true,
                    )],
                    enums: vec![],
                    structs: vec![],
                    impls: vec![],
                    functions: vec![],
                    span,
                    ty: self.tyctx.unit(),
                };
                let if_expr = hir::Expr {
                    kind: hir::ExprKind::If {
                        cond: Box::new(cond),
                        then_clause,
                        else_clause: None,
                    },
                    span,
                    ty: self.tyctx.unit(),
                };
                let mut stmts = vec![hir::Stmt::Expr(if_expr, false)];
                stmts.append(&mut body.stmts);
                body = hir::Block { stmts, ..body };
                hir::ExprKind::Loop(body)
            }
            ast::ExprKind::Loop(body) => {
                let body = self.enter_loop_scope(|this| this.annotate_block(body))?;
                hir::ExprKind::Loop(body)
            }
            ast::ExprKind::Array(values) => {
                let values = values.iter().map(|e| self.annotate_expr(e)).collect::<Result<_>>()?;
                hir::ExprKind::Array(values)
            }
            ast::ExprKind::ArrayRepeat(e, times) => {
                let e = Box::new(self.annotate_expr(e)?);
                let times = Box::new(self.annotate_expr(times)?);
                hir::ExprKind::ArrayRepeat(e, times)
            }
            ast::ExprKind::ArrayAccess(receiver, index) => {
                let receiver = Box::new(self.annotate_expr(receiver)?);
                let index = Box::new(self.annotate_expr(index)?);
                hir::ExprKind::ArrayAccess(receiver, index)
            }
        };
        Ok(hir::Expr { kind, span, ty })
    }

    fn annotate_block(&mut self, block: &ast::Block) -> Result<hir::Block> {
        self.enter_block_scope(|this| {
            this.declare_structs(&block.structs);
            this.declare_enums(&block.enums);
            let structs = this.annotate_structs(&block.structs)?;
            let enums = this.annotate_enums(&block.enums)?;
            this.annotate_fn_headers(&block.functions);
            let impls = this.annotate_impls(&block.impls)?;
            let functions = this.annotate_fns(&block.functions)?;
            let stmts = this.annotate_stmts(&block.stmts)?;
            Ok(hir::Block {
                structs,
                enums,
                impls,
                functions,
                stmts,
                ty: this.tyctx.new_type_var(),
                span: block.span,
            })
        })
    }

    fn annotate_fn_headers(&mut self, functions: &[ast::Function]) {
        for func in functions {
            self.functions.insert(func.name.symbol, self.tyctx.new_type_var());
        }
    }

    fn annotate_methods(&mut self, functions: &[ast::Function]) -> Result<Vec<hir::Function>> {
        let mut out = vec![];
        for func in functions {
            let ty = self.tyctx.new_type_var();
            let func = self.annotate_fn(func, ty)?;
            out.push(func);
        }
        Ok(out)
    }

    fn annotate_fns(&mut self, functions: &[ast::Function]) -> Result<Vec<hir::Function>> {
        let mut out = vec![];
        for func in functions {
            let ty = *self.functions.get(func.name.symbol).unwrap();
            let func = self.annotate_fn(func, ty)?;
            out.push(func);
        }
        Ok(out)
    }

    fn annotate_fn(&mut self, func: &ast::Function, ty: TypeVar) -> Result<hir::Function> {
        self.enter_fn_scope(|this| {
            let params = this.annotate_params(&func.params)?;
            let ret = this.ast_ty_to_ty(&func.ret)?;
            this.has_enclosing_fn = true;
            let body = this.annotate_block(&func.body)?;
            this.has_enclosing_fn = false;
            Ok(hir::Function {
                name: func.name.clone(),
                params,
                ret,
                body,
                ty,
            })
        })
    }

    fn annotate_params(&mut self, params: &[ast::Param]) -> Result<Vec<hir::Param>> {
        params
            .iter()
            .map(|p| {
                let param_ty = self.ast_ty_to_ty(&p.ty)?;
                self.bindings.insert(p.name.symbol, param_ty);
                Ok(hir::Param {
                    name: p.name.clone(),
                    param_ty,
                })
            })
            .collect()
    }

    fn ast_ty_to_ty(&mut self, ast_ty: &ast::Ty) -> Result<TypeVar> {
        let ty = match &ast_ty.kind {
            ast::TyKind::Fn(params, ret) => {
                let params = params.iter().map(|p| self.ast_ty_to_ty(p)).collect::<Result<_>>()?;
                let ret = self.ast_ty_to_ty(ret)?;
                self.tyctx.alloc_ty(Ty::Fn(params, ret))
            }
            ast::TyKind::Ident(t, generic_args) => self.token_to_ty(t, generic_args)?,
            ast::TyKind::Tuple(types) => {
                let types = types.iter().map(|t| self.ast_ty_to_ty(t)).collect::<Result<_>>()?;
                self.tyctx.alloc_ty(Ty::Tuple(types))
            }
            ast::TyKind::Infer => self.tyctx.new_type_var(),
            ast::TyKind::Unit => self.tyctx.unit(),
            ast::TyKind::SelfTy => self.enclosing_self_ty.unwrap(),
            ast::TyKind::Array(ty) => {
                let ty = self.ast_ty_to_ty(ty)?;
                self.tyctx.alloc_ty(Ty::Array(ty))
            }
        };

        Ok(ty)
    }

    fn annotate_impls(&mut self, impls: &[ast::Impl]) -> Result<Vec<hir::Impl>> {
        impls.iter().map(|i| self.annotate_impl(i)).collect()
    }

    fn annotate_impl(&mut self, i: &ast::Impl) -> Result<hir::Impl> {
        let ty = match self.types.get(i.name.symbol) {
            Some(ty) => *ty,
            None => {
                return self.handler.mk_err(i.name.span, "Not found in this scope");
            }
        };
        let functions = self.enter_self_scope(ty, |this| this.annotate_methods(&i.functions))?;
        Ok(hir::Impl { ty, functions })
    }

    fn declare_enums(&mut self, enums: &[ast::Enum]) {
        for e in enums {
            self.types.insert(e.name.symbol, self.tyctx.new_type_var());
        }
    }

    fn annotate_enums(&mut self, enums: &[ast::Enum]) -> Result<Vec<hir::Enum>> {
        enums.iter().map(|e| self.annotate_enum(e)).collect()
    }

    fn annotate_enum(&mut self, e: &ast::Enum) -> Result<hir::Enum> {
        let ty = *self.types.get(e.name.symbol).unwrap();
        let variants = self.enter_self_scope(ty, |this| this.annotate_enum_variants(&e.variants))?;
        Ok(hir::Enum {
            name: e.name.clone(),
            variants,
            ty,
        })
    }

    fn annotate_enum_variants(&mut self, variants: &[ast::EnumVariant]) -> Result<Vec<hir::EnumVariant>> {
        variants.iter().map(|v| self.annotate_enum_variant(v)).collect()
    }

    fn annotate_enum_variant(&mut self, variant: &ast::EnumVariant) -> Result<hir::EnumVariant> {
        let kind = match &variant.kind {
            ast::EnumVariantKind::Empty => hir::EnumVariantKind::Empty,
            ast::EnumVariantKind::Struct(fields) => hir::EnumVariantKind::Struct(self.annotate_struct_fields(fields)?),
            ast::EnumVariantKind::Tuple(fields) => hir::EnumVariantKind::Tuple(self.annotate_struct_fields(fields)?),
        };
        Ok(hir::EnumVariant {
            name: variant.name.clone(),
            kind,
        })
    }

    fn declare_structs(&mut self, structs: &[ast::Struct]) {
        for s in structs {
            let generics = self.annotate_generic_params(&s.generics);
            let ty = self.tyctx.new_type_var();
            self.tyctx.unify_value(ty, Ty::Struct(ty, s.name.symbol, generics));
            self.types.insert(s.name.symbol, ty);
        }
    }

    fn annotate_structs(&mut self, structs: &[ast::Struct]) -> Result<Vec<hir::Struct>> {
        structs
            .iter()
            .map(|s| self.enter_block_scope(|this| this.annotate_struct(s)))
            .collect()
    }

    fn annotate_generic_params(&mut self, generic_params: &GenericParams) -> Rc<[TypeVar]> {
        let mut generic_tys = vec![];
        for g in generic_params.params.iter() {
            let ty = self.tyctx.new_generic(g.name.symbol);
            self.types.insert(g.name.symbol, ty);
            generic_tys.push(ty);
        }
        generic_tys.into()
    }

    fn annotate_struct(&mut self, s: &ast::Struct) -> Result<hir::Struct> {
        let ty = *self.types.get(s.name.symbol).unwrap();
        let fields = self.enter_self_scope(ty, |this| this.annotate_struct_fields(&s.fields))?;
        if s.is_tuple {
            let ctor_ty = self.tyctx.alloc_ty(Ty::Fn(fields.iter().map(|f| f.ty).collect(), ty));
            self.functions.insert(s.name.symbol, ctor_ty);
        }
        let field_tys = fields.iter().map(|f| (f.name.symbol, f.ty)).collect();
        self.tyctx.add_fields(ty, field_tys);
        Ok(hir::Struct {
            name: s.name.clone(),
            fields,
            ty,
        })
    }

    fn annotate_struct_fields(&mut self, fields: &[ast::StructField]) -> Result<Vec<hir::StructField>> {
        fields.iter().map(|f| self.annotate_struct_field(f)).collect()
    }

    fn annotate_struct_field(&mut self, field: &ast::StructField) -> Result<hir::StructField> {
        Ok(hir::StructField {
            name: field.name.clone(),
            ty: self.ast_ty_to_ty(&field.ty)?,
        })
    }

    fn annotate_fields(&mut self, fields: &[ast::Field]) -> Result<Vec<hir::Field>> {
        fields.iter().map(|f| self.annotate_field(f)).collect()
    }

    fn annotate_field(&mut self, field: &ast::Field) -> Result<hir::Field> {
        Ok(hir::Field {
            name: field.name.clone(),
            expr: self.annotate_expr(&field.expr)?,
        })
    }

    fn token_to_ty(&mut self, token: &Token, generic_args: &GenericArgs) -> Result<TypeVar> {
        let mut generic_tys = Vec::new();
        for g in generic_args.args.iter() {
            let ty = self.ast_ty_to_ty(&g.ty)?;
            generic_tys.push(ty);
        }
        let ty = token.symbol.as_str_with(|s| {
            Some(match s {
                "bool" => self.tyctx.bool(),
                "int" => self.tyctx.int(),
                "str" => self.tyctx.str(),
                "float" => self.tyctx.float(),
                _ => return None,
            })
        });

        if let Some(ty) = ty {
            return Ok(ty);
        }

        match self.types.get(token.symbol) {
            Some(ty) => {
                let generic_params = self.tyctx.generic_params(*ty);
                if generic_params.len() != generic_args.args.len() {
                    let message = format!(
                        "Expected {} generic arguments, found {}",
                        generic_params.len(),
                        generic_args.args.len()
                    );
                    return self.handler.mk_err(generic_args.span, &message);
                }
                let mut subst = HashMap::new();
                for (param, arg) in generic_params.iter().zip(generic_tys.iter()) {
                    subst.insert(*param, *arg);
                }
                let ty = self.tyctx.subst_ty(*ty, &subst);
                Ok(ty)
            }
            None => self.handler.mk_err(token.span, "Unknown type"),
        }
    }

    fn enter_block_scope<F, R>(&mut self, f: F) -> R
    where
        F: FnOnce(&mut Self) -> R,
    {
        let types_log = self.types.snapshot();
        let functions_log = self.functions.snapshot();
        let bindings_log = self.bindings.snapshot();

        let result = f(self);

        self.bindings.rollback(bindings_log);
        self.functions.rollback(functions_log);
        self.types.rollback(types_log);

        result
    }

    fn enter_loop_scope<F, R>(&mut self, f: F) -> R
    where
        F: FnOnce(&mut Self) -> R,
    {
        let has_enclosing_loop = self.has_enclosing_loop;
        self.has_enclosing_loop = true;
        let result = f(self);
        self.has_enclosing_loop = has_enclosing_loop;
        result
    }

    fn enter_fn_scope<F, R>(&mut self, f: F) -> R
    where
        F: FnOnce(&mut Self) -> R,
    {
        let has_enclosing_fn = self.has_enclosing_fn;
        let has_enclosing_loop = self.has_enclosing_loop;

        let bindings = std::mem::take(&mut self.bindings);
        self.has_enclosing_fn = true;
        self.has_enclosing_loop = false;

        let result = self.enter_block_scope(|this| f(this));

        self.has_enclosing_loop = has_enclosing_loop;
        self.has_enclosing_fn = has_enclosing_fn;
        self.bindings = bindings;

        result
    }

    fn enter_self_scope<F, R>(&mut self, ty: TypeVar, f: F) -> R
    where
        F: FnOnce(&mut Self) -> R,
    {
        let save_ty = self.enclosing_self_ty.take();
        self.enclosing_self_ty = Some(ty);
        let result = f(self);
        self.enclosing_self_ty = save_ty;
        result
    }
}
