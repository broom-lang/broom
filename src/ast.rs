use std::fmt::{self, Display, Formatter};
use std::iter;
use pretty::RcDoc;

use crate::pos::Span;

#[derive(Debug)]
pub enum Expr {
    App(Box<SpanningExpr>, Box<SpanningExpr>),

    Do(Vec<SpanningStmt>, Box<SpanningExpr>),

    Id(String),

    Int(isize)
}

#[derive(Debug)]
pub struct SpanningExpr {
    pub expr: Expr,
    pub span: Span
}

#[derive(Debug)]
pub enum Pat {
    Id(String),

    Int(isize)
}

#[derive(Debug)]
pub struct SpanningPat {
    pub pat: Pat,
    pub span: Span
}

#[derive(Debug)]
pub enum Stmt {
    Def(SpanningPat, SpanningExpr),
    Expr(SpanningExpr)
}

#[derive(Debug)]
pub struct SpanningStmt {
    pub stmt: Stmt,
    pub span: Span
}

impl Display for Expr {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result { self.to_doc().render_fmt(80, f) }
}

impl Expr {
    pub fn spanning(self, span: Span) -> SpanningExpr { SpanningExpr {expr: self, span} }

    fn to_doc(&self) -> RcDoc<()> {
        use Expr::*;

        match *self {
            App(ref callee, ref arg) =>
                callee.to_doc()
                    .append(RcDoc::line().append(arg.to_doc()).nest(2).group()),

            Do(ref stmts, ref body) =>
                RcDoc::text("do").append(RcDoc::line()).append(RcDoc::text("{")).group()
                    .append(RcDoc::intersperse(
                            stmts.iter().map(|stmt| stmt.to_doc())
                                .chain(iter::once(body.to_doc())),
                            RcDoc::text(";").append(RcDoc::line()))
                        .nest(1).group())
                    .append(RcDoc::text("}")),

            Id(ref name) => RcDoc::text(name),

            Int(n) => RcDoc::as_string(n)
        }
    }
}

impl Display for SpanningExpr {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result { self.expr.fmt(f) }
}

impl SpanningExpr {
    fn to_doc(&self) -> RcDoc<()> { self.expr.to_doc() }
}

impl Pat {
    pub fn spanning(self, span: Span) -> SpanningPat { SpanningPat {pat: self, span} }

    fn to_doc(&self) -> RcDoc<()> {
        use Pat::*;

        match *self {
            Id(ref name) => RcDoc::text(name),

            Int(n) => RcDoc::as_string(n)
        }
    }
}

impl SpanningPat {
    fn to_doc(&self) -> RcDoc<()> { self.pat.to_doc() }
}

impl Stmt {
    pub fn spanning(self, span: Span) -> SpanningStmt { SpanningStmt {stmt: self, span} }

    fn to_doc(&self) -> RcDoc<()> {
        use Stmt::*;

        match *self {
            Def(ref pat, ref expr) =>
                pat.to_doc()
                    .append(RcDoc::line().append(RcDoc::text("=")))
                    .append(RcDoc::line().append(expr.to_doc().nest(2).group())),

            Expr(ref expr) => expr.to_doc()
        }
    }
}

impl SpanningStmt {
    fn to_doc(&self) -> RcDoc<()> { self.stmt.to_doc() }
}
