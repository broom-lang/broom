use std::rc::Rc;
use std::cell::RefCell;
use std::fmt::{self, Display, Formatter};

use crate::ast;
use crate::ftype::{Type, TypeRef};
use crate::fast;
use crate::compiler::{Compiler, Id};
use crate::pos::{Span, Spanning};
use crate::type_env::{EnvRef, Env};

pub fn convert(cmp: &mut Compiler, expr: ast::SpanningExpr) -> Result<fast::TypedExpr, Vec<Spanning<Error>>> {
    let mut typer = Typer::new(cmp);
    let env = Rc::new(RefCell::new(Env::new()));
    
    let expr = expr.typed(&mut typer, env);

    if typer.errors.len() == 0 {
        Ok(expr)
    } else {
        Err(typer.errors)
    }
}

pub enum Error {
    Unbound(String)
}

impl Display for Error {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        use Error::*;

        match *self {
            Unbound(ref name) => write!(f, "Unbound variable {}", name)
        }
    }
}

impl Error {
    fn spanning(self, span: Span) -> Spanning<Error> { Spanning {v: self, span} }
}

pub struct Typer<'a> {
    pub cmp: &'a mut Compiler,

    int: TypeRef,

    errors: Vec<Spanning<Error>>
}

impl<'a> Typer<'a> {
    fn new(cmp: &'a mut Compiler) -> Self {
        Typer {
            cmp,

            int: Rc::new(Type::Int),

            errors: Vec::new()
        }
    }

    fn int(&self) -> TypeRef { self.int.clone() }

    fn error(&mut self, error: Spanning<Error>) { self.errors.push(error); }
}

impl ast::SpanningExpr {
    fn typed(self, typer: &mut Typer, env: EnvRef) -> fast::TypedExpr {
        match self.expr {
            ast::Expr::App(..) => todo!(),

            ast::Expr::Do(stmts, body) => {
                let mut typed_stmts = Vec::new();
                let env = stmts.into_iter().fold(env, |env, stmt| {
                    let (stmt, env) = stmt.typed(typer, env);
                    typed_stmts.push(stmt);
                    env
                });

                let body = body.typed(typer, env);

                let r#type = body.r#type.clone();
                fast::Expr::Do(typed_stmts, Box::new(body)).typed(r#type, self.span)
            },

            ast::Expr::Id(name) => {
                let (id, r#type) = match env.borrow().get(name.as_str()) {
                    Some(binding) => binding,
                    None => {
                        typer.error(Error::Unbound(name.clone()).spanning(self.span.clone()));
                        (Id::src_fresh(typer.cmp, name), /* HACK: */ typer.int())
                    }
                };

                fast::Expr::Use(id).typed(r#type, self.span)
            },

            ast::Expr::Int(n) => fast::Expr::Int(n).typed(typer.int(), self.span),
        }
    }
}

impl ast::SpanningStmt {
    fn typed(self, typer: &mut Typer, env: EnvRef) -> (fast::SpanningStmt, EnvRef) {
        match self.stmt {
            ast::Stmt::Def(pat, expr) =>
                match pat.annotation() {
                    Some(_) => todo!(),

                    None => {
                        let expr = expr.typed(typer, env.clone());
                        let env = Rc::new(RefCell::new(env.borrow().with_values_scope()));
                        let pat = pat.checked(typer, env.clone(), expr.r#type.clone());
                        (fast::Stmt::Def(pat, expr).spanning(self.span), env)
                    }
                },

            ast::Stmt::Expr(expr) => (fast::Stmt::Expr(expr.typed(typer, env.clone())).spanning(self.span), env)
        }
    }
}

impl ast::SpanningPat {
    fn annotation(&self) -> Option<TypeRef> {
        use ast::Pat::*;

        match self.pat {
            Id(_) | Int(_) => None
        }
    }

    // TODO: Enable `self` to have a supertype of `type`:
    fn checked(self, typer: &mut Typer, env: EnvRef, r#type: TypeRef) -> fast::TypedPat {
        use ast::Pat::*;

        match self.pat {
            Id(name) => {
                let id = env.borrow_mut().declare(typer, &name, r#type.clone());

                fast::Pat::Id(id).typed(r#type, self.span)
            },

            Int(n) => {
                r#type.unify(typer.int());

                fast::Pat::Int(n).typed(r#type, self.span)
            }
        }
    }
}
