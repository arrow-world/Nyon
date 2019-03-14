mod modules;
pub mod translator;
pub mod typechk;
pub mod formatter;
pub mod explicit_subst;
pub mod unification;
pub mod serialize;
pub mod errors;

pub(crate) use self::typechk::HoledTerm;

use syntax::{Loc, loc};
use std::rc::Rc;

pub type ConstId = usize;
pub type CtorId = usize;
pub type HoleId = usize;

#[derive(Clone, Debug)]
pub struct Env {
    pub consts: Vec<Option<(typechk::HoledConst, Loc)>>,
    pub typings: Vec<Option<((Rc<HoledTerm>, Loc), (Rc<HoledTerm>, Loc))>>,
    pub nof_namedhole: usize,
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
            nof_namedhole: 0,
        }
    }
}

impl From<Env> for typechk::HoledEnv {
    fn from(env: Env) -> Self {
        typechk::HoledEnv {
            consts: env.consts.into_iter().map(|c| c.unwrap()).collect(),
            typings: env.typings.into_iter().map(|t| t.unwrap()).collect(),
            nof_named_hole: env.nof_namedhole,
        }
    }
}

enum SpecialType {
    Nat,
    Int,
    Unicode,
}