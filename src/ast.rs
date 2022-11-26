use crate::pos::{Pos, Span};

#[derive(Debug)]
pub enum Expr {
    Id(String)
}

#[derive(Debug)]
pub struct SpanningExpr {
    pub expr: Expr,
    pub span: Span
}

impl Expr {
    pub fn spanning(self, start: Pos, end: Pos) -> SpanningExpr { SpanningExpr {expr: self, span: Span {start, end}} }
}
