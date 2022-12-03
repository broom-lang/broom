use pretty::RcDoc;

use std::collections::HashMap;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Id(usize);

impl Id {
    pub fn src_fresh(cmp: &mut Compiler, name: String) -> Self {
        let id = Self::fresh(cmp);
        cmp.id_names.insert(id, name);
        id
    }

    pub fn fresh(cmp: &mut Compiler) -> Self {
        let i = cmp.id_counter;
        cmp.id_counter = i + 1;
        Self(i)
    }

    pub fn to_doc<'a>(self, cmp: &Compiler) -> RcDoc<'a, ()> {
        RcDoc::text(match cmp.id_names.get(&self) {
            Some(name) => format!("{}${}", name, self.0),
            None => format!("${}", self.0)
        })
    }
}

pub struct Compiler {
    id_counter: usize,
    id_names: HashMap<Id, String>
}

impl Compiler {
    pub fn new() -> Self { Compiler {id_counter: 0, id_names: HashMap::new()} }
}
