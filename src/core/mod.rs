mod modules;
mod translator;
mod typechk;

pub use self::typechk::HoledTerm;

use std::rc::Rc;

pub type ConstId = usize;
pub type CtorId = usize;

#[derive(Clone, Debug)]
pub struct Env {
    pub consts: Vec<typechk::HoledConst>,
    pub typings: Vec<(Rc<HoledTerm>, Rc<HoledTerm>)>,
}
impl Env {
    pub fn extend(&mut self, other: Env) {
        self.consts.extend(other.consts);
        self.typings.extend(other.typings);
    }

    fn new() -> Self {
        Env {
            consts: Vec::new(),
            typings: Vec::new(),
        }
    }
}

impl From<Env> for typechk::HoledEnv {
    fn from(env: Env) -> Self {
        typechk::HoledEnv {
            consts: env.consts,
            typings: env.typings,
        }
    }
}