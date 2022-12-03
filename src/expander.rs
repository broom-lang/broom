use std::result;
use std::fmt::{self, Display, Formatter};

use crate::cst;
use crate::ast;
use crate::pos::{Span, Spanning};

pub enum Error {
    KeywordValue(String),

    Arg {
        callee: String,
        arg: cst::SpanningExpr
    }
}

impl Display for Error {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        use Error::*;

        match *self {
            KeywordValue(ref name) => write!(f, "Tried to take value of keyword {}", name),

            Arg {ref callee, ref arg} => write!(f, "Invalid argument for keyword {}: {}", callee, arg)
        }
    }
}

impl Error {
    fn spanning(self, span: Span) -> Spanning<Error> { Spanning {v: self, span} }
}

type Result<T> = result::Result<T, Spanning<Error>>;

pub fn expand(expr: cst::SpanningExpr) -> Result<ast::SpanningExpr> {
    Ok(match expr.expr {
        cst::Expr::App(callee, arg) =>
            match callee.expr {
                cst::Expr::Id(name) if name == "do" => expand_do(*arg, expr.span)?,

                _ => ast::Expr::App(Box::new(expand(*callee)?), Box::new(expand(*arg)?)).spanning(expr.span)
            },

        // HACK: Keywords are globally reserved and manually listed here:
        // TODO: Instead, enable e.g. `do {do = 5; do}` -> 5 : __int:
        cst::Expr::Id(name) if name == "do" => return Err(Error::KeywordValue(name).spanning(expr.span)),

        cst::Expr::Id(name) => ast::Expr::Id(name).spanning(expr.span),

        cst::Expr::Int(n) => ast::Expr::Int(n).spanning(expr.span),

        _ => todo!()
    })
}

fn expand_pat(pat: cst::SpanningExpr) -> Result<ast::SpanningPat> {
    Ok(match pat.expr {
        cst::Expr::App(..) => todo!(),

        cst::Expr::Record(..) => todo!(),

        cst::Expr::Id(name) => ast::Pat::Id(name).spanning(pat.span),

        cst::Expr::Int(n) => ast::Pat::Int(n).spanning(pat.span),
    })
}

fn expand_stmt(stmt: cst::SpanningStmt) -> Result<ast::SpanningStmt> {
    Ok(match stmt.stmt {
        cst::Stmt::Def(pat, expr) => ast::Stmt::Def(expand_pat(pat)?, expand(expr)?).spanning(stmt.span),

        cst::Stmt::Expr(expr) => ast::Stmt::Expr(expand(expr)?).spanning(stmt.span)
    })
}

fn expand_do(arg: cst::SpanningExpr, span: Span) -> Result<ast::SpanningExpr> {
    let fields = match arg.expr {
        cst::Expr::Record(fields) => fields,
        _ => {
            let arg_span = arg.span.clone();
            return Err(Error::Arg {callee: String::from("do"), arg}.spanning(arg_span));
        }
    };

    let mut stmts = fields.into_iter().map(expand_stmt).collect::<Result<Vec<_>>>()?;

    let body = match stmts.pop() {
        Some(stmt) =>
            match stmt.stmt {
                ast::Stmt::Def(..) => todo!("emit unit"),
                ast::Stmt::Expr(expr) => expr
            },

        None => todo!("emit unit")
    };

    Ok(ast::Expr::Do(stmts, Box::new(body)).spanning(span))
}
