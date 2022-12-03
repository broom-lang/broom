use std::iter;
use pretty::RcDoc;

use crate::pos::Span;
use crate::compiler::{Compiler, Id};
use crate::ftype::TypeRef;

pub enum Stmt {
    Def(TypedPat, TypedExpr),
    Expr(TypedExpr)
}

pub struct SpanningStmt {
    pub stmt: Stmt,
    pub span: Span
}

pub enum Expr {
    Do(Vec<SpanningStmt>, Box<TypedExpr>),

    Use(Id),

    Int(isize)
}

pub struct TypedExpr {
    pub expr: Expr,
    pub r#type: TypeRef,
    pub span: Span
}

pub enum Pat {
    Id(Id),

    Int(isize)
}

pub struct TypedPat {
    pub pat: Pat,
    pub r#type: TypeRef,
    pub span: Span
}

impl Stmt {
    pub fn spanning(self, span: Span) -> SpanningStmt { SpanningStmt {stmt: self, span} }

    fn to_doc(&self, cmp: &Compiler) -> RcDoc<()> {
        use Stmt::*;

        match *self {
            Def(ref pat, ref expr) =>
                pat.to_doc(cmp)
                    .append(RcDoc::line().append(RcDoc::text("=")))
                    .append(RcDoc::line().append(expr.to_doc(cmp).nest(2).group())),

            Expr(ref expr) => expr.to_doc(cmp)
        }
    }
}

impl SpanningStmt {
    fn to_doc(&self, cmp: &Compiler) -> RcDoc<()> { self.stmt.to_doc(cmp) }
}

impl Expr {
    pub fn typed(self, r#type: TypeRef, span: Span) -> TypedExpr { TypedExpr {expr: self, r#type, span} }

    fn to_doc(&self, cmp: &Compiler) -> RcDoc<()> {
        use Expr::*;

        match *self {
            Do(ref stmts, ref body) =>
                RcDoc::text("do").append(RcDoc::line()).append(RcDoc::text("{")).group()
                    .append(RcDoc::intersperse(
                            stmts.iter().map(|stmt| stmt.to_doc(cmp))
                                .chain(iter::once(body.to_doc(cmp))),
                            RcDoc::text(";").append(RcDoc::line()))
                        .nest(1).group())
                    .append(RcDoc::text("}")),

            Use(id) => id.to_doc(cmp),

            Int(n) => RcDoc::as_string(n)
        }
    }
}

impl TypedExpr {
    pub fn to_doc(&self, cmp: &Compiler) -> RcDoc<()> { self.expr.to_doc(cmp) }
}

impl Pat {
    pub fn typed(self, r#type: TypeRef, span: Span) -> TypedPat { TypedPat {pat: self, r#type, span} }

    fn to_doc(&self, cmp: &Compiler) -> RcDoc<()> {
        use Pat::*;

        match *self {
            Id(id) => id.to_doc(cmp),

            Int(n) => RcDoc::as_string(n)
        }
    }
}

impl TypedPat {
    pub fn to_doc(&self, cmp: &Compiler) -> RcDoc<()> { self.pat.to_doc(cmp) }
}
