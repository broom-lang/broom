use std::rc::Rc;
use std::fmt::{self, Display, Formatter};
use pretty::RcDoc;

pub enum Type {
    Int
}

pub type TypeRef = Rc<Type>;

impl Display for Type {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result { self.to_doc().render_fmt(80, f) }
}

impl Type {
    fn to_doc(&self) -> RcDoc<()> {
        use Type::*;

        match *self {
            Int => RcDoc::text("__int")
        }
    }

    pub fn unify(&self, other: TypeRef) {
        use Type::*;

        match *self {
            Int => match *other {
                Int => {}
            }
        }
    }
}