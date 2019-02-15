mod modules;
pub mod translator;
pub mod typechk;
pub mod formatter;

pub use self::typechk::HoledTerm;

use std::rc::Rc;

pub type ConstId = usize;
pub type CtorId = usize;
pub type HoleId = usize;

#[derive(Clone, Debug)]
pub struct Env {
    pub consts: Vec<Option<typechk::HoledConst>>,
    pub typings: Vec<Option<(Rc<HoledTerm>, Rc<HoledTerm>)>>,
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
            consts: env.consts.into_iter().map(|c| c.unwrap()).collect(),
            typings: env.typings.into_iter().map(|t| t.unwrap()).collect(),
            nof_named_hole: 0,
        }
    }
}

enum SpecialType {
    Nat,
    Int,
    Unicode,
}