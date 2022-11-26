use std::rc::Rc;
use std::fmt::{self, Display, Formatter};

use crate::ast;
use crate::fast::{self, Type};

pub fn convert(expr: ast::SpanningExpr) -> Result<fast::TypedExpr, Vec<Error>> {
    let mut typer = Typer::new();
    
    let expr = typer.type_of(expr);

    if typer.errors.len() == 0 {
        Ok(expr)
    } else {
        Err(typer.errors)
    }
}

pub enum Error {}

impl Display for Error {
    fn fmt(&self, _: &mut Formatter) -> fmt::Result {
        match *self {

        }
    }
}

struct Typer {
    int: Rc<Type>,

    errors: Vec<Error>
}

impl Typer {
    fn new() -> Self {
        Typer {
            int: Rc::new(Type::Int),

            errors: Vec::new()
        }
    }

    fn int(&self) -> Rc<Type> { self.int.clone() }

    fn type_of(&mut self, expr: ast::SpanningExpr) -> fast::TypedExpr {
        match expr.expr {
            ast::Expr::Int(n) => fast::Expr::Int(n).typed(self.int(), expr.span),

            _ => todo!()
        }
    }
}
