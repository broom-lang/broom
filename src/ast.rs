use std::fmt::{self, Display, Formatter};
use pretty::RcDoc;

use crate::pos::{Pos, Span};

#[derive(Debug)]
pub enum Expr {
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

impl Expr {
    pub fn spanning(self, start: Pos, end: Pos) -> SpanningExpr { SpanningExpr {expr: self, span: Span {start, end}} }

    fn to_doc(&self) -> RcDoc<()> {
        use Expr::*;

        match *self {
            Id(ref name) => RcDoc::text(name),

            Int(n) => RcDoc::as_string(n)
        }
    }
}
