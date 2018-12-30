use super::ConstId;

use std::collections::HashMap;
use std::rc::Rc;
use std::cell::RefCell;

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Module<'s> {
    name: String,
    names: HashMap<ConstId, String>,
    ids: HashMap<&'s str, ConstId>,
    parent: Option< Rc<RefCell< Module<'s> >> >,
    children: HashMap< &'s str, Rc<RefCell< Module<'s> >> >,
}
impl<'s> Module<'s> {
    pub fn top() -> Self {
        Module {
            name: "toplevel".into(),
            names: HashMap::new(),
            ids: HashMap::new(),
            parent: None,
            children: HashMap::new(),
        }
    }

    pub fn add_const(&mut self, id: ConstId, name: String) {
        self.names.insert(id.clone(), name);
        self.ids.insert(&name, id);
    }

    pub fn search_module<I>(&self, path: I) -> Option< &Module<'s> >
        where I: IntoIterator<Item=&'s str>
    {
        let mut path = path.into_iter();
        let next = path.next();
        match next {
            Some("super") => self.parent.and_then(|x| x.borrow().search_module(path)),
            Some(x) => self.children.get(x).and_then(|x| x.borrow().search_module(path)),
            None => Some( self )
        }
    }

    pub fn search_const<I>(&self, module: I, name: &str) -> Option<ConstId>
        where I: IntoIterator<Item=&'s str>
    {
        self.search_module(module).and_then(|x| x.ids.get(name)).cloned()
    }
}

pub fn add_child<'s>(parent: Rc<RefCell< Module<'s> >>, name: String) -> Rc<RefCell< Module<'s> >> {
    let m = Rc::new(RefCell::new(
        Module {
            name,
            names: HashMap::new(),
            ids: HashMap::new(),
            parent: Some(parent),
            children: HashMap::new(),
        }
    ));

    parent.borrow_mut().children.insert(&name, m.clone());

    m
}

pub fn search_module<'s, I>(this: &Rc<RefCell< Module<'s> >>, path: I) -> Option< Rc<RefCell< Module<'s> >> >
    where I: IntoIterator<Item=&'s str>
{
    let mut path = path.into_iter();
    let next = path.next();
    match next {
        Some("super") => this.borrow().parent.and_then(|x| search_module(&x, path)),
        Some(x) => this.borrow().children.get(x).and_then(|x| search_module(&x, path)),
        None => Some( this.clone() )
    }
}