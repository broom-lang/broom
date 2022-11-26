use std::fmt::{self, Display, Formatter};
use pretty::RcDoc;

use crate::pos::{Pos, Span};

#[derive(Debug)]
pub enum Stmt {
    Def(SpanningExpr, SpanningExpr),
    Expr(SpanningExpr)
}

#[derive(Debug)]
pub struct SpanningStmt {
    pub stmt: Stmt,
    pub span: Span
}

#[derive(Debug)]
pub enum Expr {
    Record(Vec<SpanningStmt>),

    Id(String),

    Int(isize)
}

#[derive(Debug)]
pub struct SpanningExpr {
    pub expr: Expr,
    pub span: Span
}

impl Display for Expr {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result { self.to_doc().render_fmt(80, f) }
}

impl Display for SpanningExpr {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result { self.expr.fmt(f) }
}

impl Stmt {
    pub fn spanning(self, start: Pos, end: Pos) -> SpanningStmt { SpanningStmt {stmt: self, span: Span {start, end}} }

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

impl Expr {
    pub fn spanning(self, start: Pos, end: Pos) -> SpanningExpr { SpanningExpr {expr: self, span: Span {start, end}} }

    fn to_doc(&self) -> RcDoc<()> {
        use Expr::*;

        match *self {
            Record(ref stmts) =>
                RcDoc::text("{")
                    .append(RcDoc::intersperse(
                            stmts.iter().map(|stmt| stmt.to_doc()), RcDoc::text(";").append(RcDoc::line()))
                        .nest(1).group())
                    .append(RcDoc::text("}")),

            Id(ref name) => RcDoc::text(name),

            Int(n) => RcDoc::as_string(n)
        }
    }
}

impl SpanningExpr {
    fn to_doc(&self) -> RcDoc<()> { self.expr.to_doc() }
}
