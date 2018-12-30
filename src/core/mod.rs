mod module;
mod term;
mod idgen;
mod translator;

use syntax::ast;
use self::term::Term;
use self::module::Module;
use self::idgen::Generator;

use std::rc::Rc;

pub type ConstId = usize;
pub type CtorId = usize;

#[derive(Clone, Debug)]
pub struct TopLevel<'s> {
    pub env: Env,
    pub top_module: Module<'s>,
}
impl<'s> TopLevel<'s> {
    pub fn with_builtin() -> Self {
        let mut tl = TopLevel {
            env: Env::new(),
            top_module: Module::top(),
        };

        tl
    }

    pub fn add_typing(&mut self, term: Rc<Term>, type_: Rc<Term>) {
        self.env.push_typing(term, type_);
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Env {
    pub consts: Vec<Const>,
    pub typings: Vec<(Rc<Term>, Rc<Term>)>,
    pub idgen: idgen::Inc<ConstId>,
}
impl Env {
    pub fn new() -> Self {
        Env {
            consts: Vec::new(),
            typings: Vec::new(),
            idgen: idgen::Inc::new(),
        }
    }

    pub fn push_const(&mut self, c: Const) -> ConstId {
        self.consts.push(c);
        self.idgen.gen()
    }

    pub fn push_typing(&mut self, term: Rc<Term>, type_: Rc<Term>) {
        self.typings.push((term, type_));
    }

    pub fn extend(&mut self, other: Env) {
        let n_of_consts = other.consts.len();
        self.consts.extend(other.consts.into_iter());
        self.typings.extend(other.typings.into_iter());
        self.idgen.advance(n_of_consts);
    }
}
impl Default for Env {
    fn default() -> Self { Env::new() }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Const {
    Def(Rc<Term>),
    DataType(DataType),
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Ctx {
    pub global: Env,
    pub local: Vec<Rc<Term>>,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct DataType {
    pub param_types: Vec<Rc<Term>>,
    pub ctor_types: Vec<Rc<Term>>,
}
impl<'s> From<NamedDataType<'s>> for DataType {
    fn from(named: NamedDataType) -> Self {
        DataType {
            param_types: named.param_types.into_iter().map(|(name, param_type)| param_type).collect(),
            ctor_types: named.ctor_types.into_iter().map(|(name, ctor_type)| ctor_type).collect(),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct NamedDataType<'s> {
    pub param_types: Vec<(&'s str, Rc<Term>)>,
    pub ctor_types: Vec<(&'s str, Rc<Term>)>,
}