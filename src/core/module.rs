use super::ConstId;

use std::collections::HashMap;
use std::rc::{Rc, Weak};
use std::cell::RefCell;

#[derive(Clone, Debug)]
pub struct Module<'s> {
    name: String,
    ids: HashMap<&'s str, ConstId>,
    parent: Weak<RefCell< Module<'s> >>,
    children: HashMap< String, Rc<RefCell< Module<'s> >> >,
}
impl<'s> Module<'s> {
    pub fn top() -> Self {
        Module {
            name: "toplevel".into(),
            ids: HashMap::new(),
            parent: Weak::new(),
            children: HashMap::new(),
        }
    }

    pub fn register(&mut self, id: ConstId, name: &'s str) {
        self.ids.insert(name, id);
    }
}

pub fn add_child<'s>(parent: Rc<RefCell< Module<'s> >>, name: String) -> Rc<RefCell< Module<'s> >> {
    let m = Rc::new(RefCell::new(
        Module {
            name: name.clone(),
            ids: HashMap::new(),
            parent: Rc::downgrade(&parent),
            children: HashMap::new(),
        }
    ));

    parent.borrow_mut().children.insert(name, m.clone());

    m
}

pub fn search_module<'s, I>(this: &Rc<RefCell< Module<'s> >>, path: I) -> Option< Rc<RefCell< Module<'s> >> >
    where I: IntoIterator<Item=&'s str>
{
    let mut path = path.into_iter();
    let next = path.next();
    match next {
        Some("super") => this.borrow().parent.upgrade().and_then(|x| search_module(&x, path)),
        Some(x) => this.borrow().children.get(x).and_then(|x| search_module(x, path)),
        None => Some( this.clone() )
    }
}

pub fn search_const<'s, I>(this: &Rc<RefCell< Module<'s> >>, module: I, name: &str) -> Option<ConstId>
    where I: IntoIterator<Item=&'s str>
{
    search_module(this, module).and_then(|x| x.borrow().ids.get(name).cloned())
}