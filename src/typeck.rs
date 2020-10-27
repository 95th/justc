use std::rc::Rc;

use self::{hir::Ast, ty::TyContext};
use crate::{err::Handler, parse::ast};

mod annotate;
mod constraints;
mod hir;
mod ty;

pub struct Typeck {
    handler: Rc<Handler>,
}

impl Typeck {
    pub fn new(handler: &Rc<Handler>) -> Self {
        Self {
            handler: handler.clone(),
        }
    }

    pub fn typeck(&self, ast: ast::Ast) -> Option<Ast> {
        let mut env = TyContext::new(&self.handler);
        let ast = self::annotate::annotate(ast, &mut env, &self.handler)?;
        dbg!(&ast);

        self::constraints::collect(&ast, &mut env, &self.handler)?;

        // self.typeck_fns(&ast.functions)?;
        // self.typeck_stmts(&ast.stmts)?;

        Some(ast)
    }

    // fn typeck_stmts(&self, stmts: &[Stmt]) -> Option<()> {
    //     for stmt in stmts {
    //         self.typeck_stmt(stmt)?;
    //     }
    //     Some(())
    // }

    // fn typeck_stmt(&self, stmt: &Stmt) -> Option<()> {
    //     use Stmt::*;
    //     match stmt {
    //         Expr(expr, _) => self.typeck_expr(expr),
    //         Let { ty, init, .. } => {
    //             if let Some(init) = init {
    //                 self.typeck_expr(init)?;
    //                 self.typeck_eq(ty, &init.ty, &init.span)?;
    //             }
    //             Some(())
    //         }
    //         Assign { name, val } => {
    //             self.typeck_expr(val)?;
    //             self.typeck_eq(&name.ty, &val.ty, &val.span)
    //         }
    //         While { cond, body } => {
    //             self.typeck_expr(cond)?;
    //             self.typeck_eq(&Ty::Bool, &cond.ty, &cond.span)?;
    //             self.typeck_block(body)
    //         }
    //         Return(_, e) => {
    //             if let Some(e) = e {
    //                 self.typeck_expr(e)
    //             } else {
    //                 Some(())
    //             }
    //         }
    //         Continue(_) | Break(_) => Some(()),
    //     }
    // }

    // fn typeck_expr(&self, expr: &Expr) -> Option<()> {
    //     use ExprKind::*;
    //     match &expr.kind {
    //         Binary { op, left, right } => {
    //             self.typeck_eq(&left.ty, &right.ty, &right.span)?;

    //             use ast::BinOp::*;
    //             match op.val {
    //                 Add | Sub | Mul | Div | Rem | Lt | Gt | Le | Ge => match &left.ty {
    //                     Ty::Int | Ty::Float => Some(()),
    //                     ty => {
    //                         self.handler
    //                             .report(op.span, &format!("Not supported for {:?}", ty));
    //                         None
    //                     }
    //                 },

    //                 Ne | Eq => match &left.ty {
    //                     Ty::Int | Ty::Float | Ty::Bool => Some(()),
    //                     ty => {
    //                         self.handler
    //                             .report(op.span, &format!("Not supported for {:?}", ty));
    //                         None
    //                     }
    //                 },
    //                 And | Or => match &left.ty {
    //                     Ty::Bool => Some(()),
    //                     ty => {
    //                         self.handler
    //                             .report(op.span, &format!("Not supported for {:?}", ty));
    //                         None
    //                     }
    //                 },
    //             }
    //         }
    //         Literal(..) => Some(()),
    //         Unary { op, expr } => match op.val {
    //             ast::UnOp::Not => match &expr.ty {
    //                 Ty::Bool => Some(()),
    //                 ty => {
    //                     self.handler
    //                         .report(op.span, &format!("Not supported for {:?}", ty));
    //                     None
    //                 }
    //             },
    //             ast::UnOp::Neg => match &expr.ty {
    //                 Ty::Int | Ty::Float => Some(()),
    //                 ty => {
    //                     self.handler
    //                         .report(op.span, &format!("Not supported for {:?}", ty));
    //                     None
    //                 }
    //             },
    //         },
    //         Variable(_, _) => Some(()),
    //         Block(block) => self.typeck_block(block),
    //         If {
    //             cond,
    //             then_clause,
    //             else_clause,
    //         } => {
    //             self.typeck_expr(cond)?;
    //             self.typeck_block(then_clause)?;
    //             if let Some(else_clause) = else_clause {
    //                 self.typeck_expr(else_clause)?;
    //             }
    //             Some(())
    //         }
    //         Closure { params, ret, body } => {
    //             for p in params {
    //                 self.typeck_no_var(&p.ty, &p.name.span)?;
    //             }
    //             self.typeck_expr(body)?;
    //             self.typeck_eq(ret, &body.ty, &body.span)
    //         }
    //         Call { callee, args } => {
    //             self.typeck_expr(callee)?;
    //             for arg in args {
    //                 self.typeck_expr(arg)?;
    //             }
    //             Some(())
    //         }
    //         Struct(_, fields, _) => {
    //             for f in fields {
    //                 self.typeck_expr(&f.expr)?;
    //             }

    //             Some(())
    //         }
    //         Field(expr, _) => {
    //             self.typeck_expr(expr)?;
    //             Some(())
    //         }
    //     }
    // }

    // fn typeck_block(&self, block: &Block) -> Option<()> {
    //     self.typeck_fns(&block.functions)?;
    //     self.typeck_stmts(&block.stmts)?;

    //     if let Some(Stmt::Expr(expr, false)) = block.stmts.last() {
    //         self.typeck_eq(&expr.ty, &block.ty, &expr.span)?;
    //     }

    //     Some(())
    // }

    // fn typeck_fns(&self, func: &[Function]) -> Option<()> {
    //     for f in func {
    //         self.typeck_fn(f)?;
    //     }
    //     Some(())
    // }

    // fn typeck_fn(&self, func: &Function) -> Option<()> {
    //     self.typeck_eq(&func.ret, &func.body.ty, &func.body.span)?;
    //     self.typeck_block(&func.body)
    // }

    // fn typeck_eq(&self, a: &Ty, b: &Ty, span: &Span) -> Option<()> {
    //     self.typeck_no_var(a, span)?;
    //     self.typeck_no_var(b, span)?;

    //     if a == b {
    //         Some(())
    //     } else {
    //         self.handler.report(
    //             *span,
    //             &format!("Type mismatch: Expected: {:?}, Actual: {:?}", a, b),
    //         );
    //         None
    //     }
    // }

    // fn typeck_no_var(&self, ty: &Ty, span: &Span) -> Option<()> {
    //     if matches!(ty, Ty::Var(_)) {
    //         self.handler.report(
    //             *span,
    //             "Type cannot be inferred. Please add type annotations",
    //         );
    //         None
    //     } else {
    //         Some(())
    //     }
    // }
}
