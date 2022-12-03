use std::rc::Rc;
use std::cell::{RefCell, RefMut};
use std::collections::HashMap;

use crate::ftype::TypeRef;
use crate::compiler::Id;
use crate::typer::Typer;

enum List<T> {
    Cons(Rc<Node<T>>),
    Nil
}

struct Node<T> {
    item: T,
    next: List<T>,
}

impl<T> List<T> {
    fn prepend(&self, item: T) -> List<T> {
        match *self {
            List::Cons(ref node) => Self::Cons(Rc::new(Node {item, next: List::Cons(node.clone())})),
            List::Nil => Self::Cons(Rc::new(Node {item, next: List::Nil}))
        }
    }

    fn first(&self) -> Option<&T> {
        match *self {
            List::Cons(ref node) => Some(&node.item),
            List::Nil => None
        }
    }

    fn iter<'a>(&'a self) -> ListIter<'a, T> { ListIter(self) }
}

struct ListIter<'a, T>(&'a List<T>);

impl<'a, T> Iterator for ListIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        match *self.0 {
            List::Cons(ref node) => {
                self.0 = &node.next;
                Some(&node.item)
            },

            List::Nil => None
        }
    }
}

pub struct Env {
    scopes: List<RefCell<Scope>>,
    hoisting_scope: TypesScopeRef
}

pub type EnvRef = Rc<RefCell<Env>>;

impl Env {
    pub fn new() -> Self {
        Self {
            scopes: List::Nil,
            hoisting_scope: Rc::new(RefCell::new(TypesScope::new()))
        }
    }

    pub fn with_values_scope(&self) -> Self {
        Self {
            scopes: self.scopes.prepend(RefCell::new(Scope::values())),
            hoisting_scope: self.hoisting_scope.clone()
        }
    }

    pub fn declare(&mut self, typer: &mut Typer, name: &str, r#type: TypeRef) -> Id {
        self.innermost_scope_mut().declare(typer, name, r#type)
    }

    fn innermost_scope_mut(&mut self) -> RefMut<Scope> { self.scopes.first().unwrap().borrow_mut() }

    pub fn get(&self, name: &str) -> Option<Binding> {
        for scope in self.scopes.iter() {
            match scope.borrow().get(name) {
                Some(binding) => return Some(binding),
                None => {}
            }
        }

        None
    }
}

type Binding = (Id, TypeRef);

enum Scope {
    Values(HashMap<String, Binding>),

    Types(TypesScopeRef)
}

struct TypesScope {}

type TypesScopeRef = Rc<RefCell<TypesScope>>;

impl Scope {
    fn values() -> Self { Self::Values(HashMap::new()) }

    fn declare(&mut self, typer: &mut Typer, name: &str, r#type: TypeRef) -> Id {
        match self {
            Scope::Values(ref mut values) => {
                // FIXME: Check non-preexistence
                let id = Id::src_fresh(typer.cmp, String::from(name));
                values.insert(String::from(name), (id, r#type));
                id
            },

            Scope::Types(_) => unreachable!()
        }
    }

    fn get(&self, name: &str) -> Option<Binding> {
        match *self {
            Scope::Values(ref values) => values.get(name).cloned(),

            Scope::Types(_) => None
        }
    }
}

impl TypesScope {
    fn new() -> Self { Self {} }
}
