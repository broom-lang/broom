use std::rc::Rc;
use std::fmt::{self, Display, Formatter};
use pretty::RcDoc;

use crate::pos::Span;

pub enum Type {
    Int
}

pub enum Expr {
    Int(isize)
}

pub struct TypedExpr {
    pub expr: Expr,
    pub r#type: Rc<Type>,
    pub span: Span
}

impl Display for Type {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result { self.to_doc().render_fmt(80, f) }
}

impl Display for Expr {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result { self.to_doc().render_fmt(80, f) }
}

impl Display for TypedExpr {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result { self.expr.fmt(f) }
}

impl Type {
    fn to_doc(&self) -> RcDoc<()> {
        use Type::*;

        match *self {
            Int => RcDoc::text("__int")
        }
    }
}

impl Expr {
    pub fn typed(self, r#type: Rc<Type>, span: Span) -> TypedExpr { TypedExpr {expr: self, r#type, span} }

    fn to_doc(&self) -> RcDoc<()> {
        use Expr::*;

        match *self {
            Int(n) => RcDoc::as_string(n)
        }
    }
}
