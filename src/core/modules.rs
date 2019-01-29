use super::ConstId;

use std::collections::HashMap;
use std::rc::{Rc, Weak};
use std::cell::RefCell;

#[derive(Clone, Debug)]
pub struct Scope {
    module: Rc<RefCell<Module>>,
    names: Vec<Name>,
    holes: Vec<String>,
    parent: Option< Rc<Scope> >,
    base_cid: ConstId,
}
impl Scope {
    pub fn top() -> Self {
        Scope {
            module: Rc::new(RefCell::new(Module::anonymous_top())),
            names: Vec::new(),
            holes: Vec::new(),
            parent: None,
            base_cid: 0,
        }
    }

    pub fn new(module: Rc<RefCell<Module>>, parent: Rc<Scope>) -> Self {
        Scope {
            module,
            names: Vec::new(),
            holes: Vec::new(),
            base_cid: parent.base_cid + parent.names.len(),
            parent: Some(parent),
        }
    }

    pub fn resolve<'b, Q: IntoIterator<Item=&'b str> + Clone>(&self, qualifier: Q, identifier: &str) -> Option<ConstId>
    {
        search_const(&self.module, qualifier.clone(), identifier).map(|offset| self.base_cid + offset)
            .or_else(|| self.parent.clone().and_then(|parent| parent.resolve(qualifier, identifier)))
    }

    pub fn resolve_from_ident(&self, ident: &::syntax::ast::Ident) -> Option<ConstId> {
        self.resolve(ident.domain.iter().map(|s| s.as_str()), &ident.name)
    }

    pub fn module(&self) -> Rc<RefCell<Module>> { self.module.clone() }

    pub fn register_const<Q: IntoIterator<Item=String> + Clone>(&mut self, qualifier: Q, identifier: String) 
        -> Option< ConstId >
    {
        let cid = self.next_cid();

        let qualifier: Vec<String> = qualifier.into_iter().collect();
        let module = search_module(&self.module, qualifier.iter().map(|s| s.as_str()))?;

        module.borrow_mut().register(cid, identifier.clone());
        self.names.push(Name{qualifier, identifier});

        Some(cid)
    }

    pub fn base_cid(&self) -> ConstId { self.base_cid }
    pub fn next_cid(&self) -> ConstId { self.base_cid + self.names.len() }

    pub fn names(&self) -> &[Name] { &self.names }
}

#[derive(Clone, Debug)]
pub struct Name {
    pub qualifier: Vec<String>,
    pub identifier: String,
}
impl Name {
    pub fn simple(identifier: String) -> Self {
        Name{qualifier: Vec::new(), identifier}
    }
}

#[derive(Clone, Debug)]
pub struct Module {
    name: String,
    ids: HashMap<String, ConstId>,
    parent: Weak<RefCell<Module>>,
    children: HashMap< String, Rc<RefCell<Module>> >,
}
impl<'s> Module {
    pub fn anonymous_top() -> Self {
        Module {
            name: String::new(),
            ids: HashMap::new(),
            parent: Weak::new(),
            children: HashMap::new(),
        }
    }

    pub fn register(&mut self, id: ConstId, name: String) {
        self.ids.insert(name, id);
    }

    pub fn name(&self) -> &str { &self.name }
}

pub fn add_child<'s>(parent: &Rc<RefCell<Module>>, name: String) -> Rc<RefCell<Module>> {
    let m = Rc::new( RefCell::new(
        Module {
            name: name.clone(),
            ids: HashMap::new(),
            parent: Rc::downgrade(parent),
            children: HashMap::new(),
        }
    ) );

    parent.borrow_mut().children.insert(name, m.clone());

    m
}

const PARENT_MODULE : &str = "super";

pub fn search_module<'a, I>(this: &Rc<RefCell<Module>>, qualifier: I) -> Option< Rc<RefCell<Module>> >
    where I: IntoIterator<Item=&'a str>
{
    let mut path = qualifier.into_iter();
    let next = path.next();
    match next {
        Some(x) if x == PARENT_MODULE => this.borrow().parent.upgrade().and_then(|x| search_module(&x, path)),
        Some(x) => this.borrow().children.get(x).and_then(|x| search_module(&x, path)),
        None => Some( this.clone() )
    }
}

pub fn search_const<'a, Q: IntoIterator<Item=&'a str>>(this: &Rc<RefCell<Module>>, qualifier: Q, identifier: &str)
    -> Option<ConstId>
{
    search_module(this, qualifier).and_then(|x| x.borrow().ids.get(identifier).cloned())
}