use super::{ConstId, HoleId};

use std::rc::Rc;

#[derive(Clone, Debug)]
pub enum HoledTerm {
    Const(ConstId),
    DBI(u64),
    Universe,
    App{s: Rc<HoledTerm>, t: Rc<HoledTerm>},
    Lam(HoledAbs),
    Pi(HoledAbs),
    Let{env: HoledEnv, t: Rc<HoledTerm>},
    Case{t: Rc<HoledTerm>, cases: Vec<Rc<HoledTerm>>, datatype: Option<ConstId>},
    Hole(Option<HoleId>),
    Value(Value),
}

#[derive(Clone, Debug)]
pub struct HoledAbs {
    pub A: Rc<HoledTerm>,
    pub t: Rc<HoledTerm>,
}

#[derive(Clone, Debug)]
pub struct HoledEnv {
    pub consts: Vec<HoledConst>,
    pub typings: Vec<(Rc<HoledTerm>, Rc<HoledTerm>)>,
}

#[derive(Clone, Debug)]
pub enum HoledConst {
    Def(Rc<HoledTerm>),
    DataType{param_types: Vec<Rc<HoledTerm>>},
    Ctor{datatype: ConstId, type_: Rc<HoledTerm>},
}

/* #[derive(Clone, Debug)]
pub struct HoledDataType {
    pub param_types: Vec<Rc<HoledTerm>>,
    pub ctor_types: Vec<Rc<HoledTerm>>,
} */

pub struct HoledCtx {
    pub global: HoledEnv,
    pub local: Vec<Rc<HoledTerm>>,
    pub typings: Vec<(Rc<HoledTerm>, Rc<HoledTerm>)>,
}

#[derive(Clone, Debug)]
pub enum Term {
    Const(ConstId),
    DBI(u64),
    Universe,
    App{s: TypedTerm, t: TypedTerm},
    Lam(Abs),
    Pi(Abs),
    Let{env: Env, t: TypedTerm},
    Case{t: TypedTerm, cases: Vec<Rc<Term>>},
    Value(Value),
}

#[derive(Clone, Debug)]
pub struct Abs {
    pub A: TypedTerm,
    pub t: TypedTerm,
}

#[derive(Clone, Debug)]
pub struct TypedTerm {
    term: Rc<Term>,
    type_: Rc<Term>,
}

#[derive(Clone, Debug)]
pub struct Env {
    pub consts: Vec<TypedTerm>,
}

#[derive(Clone, Debug)]
pub struct Ctx {
    pub global: Env,
    pub local: Vec<TypedTerm>,
}

#[derive(Clone, Debug)]
pub enum Value {
    Nat(::num::BigInt),
    Int(::num::BigInt),
    Str(String),
}

pub fn typechk(ctx: HoledCtx) -> Result<Ctx, TypeChkErr> {
    let mut infer_ctx = InferCtx{global: InferEnv{consts: Vec::new()}, local: Vec::new(), typings: Vec::new()};
    let mut next_infertype_id = 0;
    for c in ctx.global.consts {
    }
    unimplemented!()
}

pub enum TypeChkErr {
}

fn assign_infertype_id(ctx: HoledCtx) -> InferCtx {
    let mut infertype_id = 0;

    InferCtx {
        global: InferEnv {
            consts: ctx.global.consts.into_iter().map(|c| assign_const(c, &mut infertype_id)).collect(),
        },
        local: unimplemented!(),
        typings: unimplemented!(),
    }
}

fn assign_const(c: HoledConst, infertype_id: &mut u64) -> InferTypedConst {
    /* match c {
        HoledConst::Def(t) => InferTypedConst{c: InferConst::Def(assign_term(t, infertype_id)), type_: },
    } */

    unimplemented!()
}

fn assign_term(term: Rc<HoledTerm>, infertype_id: &mut u64) -> InferTypedTerm {
    let itt = InferTypedTerm {
        term: Rc::new( match *term {
            HoledTerm::Const(ref id) => InferTerm::Const(*id),
            HoledTerm::DBI(ref i) => InferTerm::DBI(*i),
            HoledTerm::Universe => InferTerm::Universe,
            HoledTerm::App{ref s, ref t} =>
                InferTerm::App{s: assign_term(s.clone(), infertype_id), t: assign_term(t.clone(), infertype_id)},
            HoledTerm::Lam(ref abs) => InferTerm::Lam(assign_abs(abs.clone(), infertype_id)),
            HoledTerm::Pi(ref abs) => InferTerm::Pi(assign_abs(abs.clone(), infertype_id)),
            HoledTerm::Let{ref env, ref t} =>
                InferTerm::Let{env: assign_env(env.clone(), infertype_id), t: assign_term(t.clone(), infertype_id)},
            HoledTerm::Case{ref t, ref cases, ref datatype} =>
                InferTerm::Case{
                    t: assign_term(t.clone(), infertype_id),
                    cases: cases.iter().map(|case| assign_term(case.clone(), infertype_id)).collect(),
                    datatype: *datatype,
                },
            HoledTerm::Value(ref val) => InferTerm::Value(val.clone()),
            HoledTerm::Hole(ref hole_id) =>
                if let Some(hole_id) = *hole_id {
                    InferTerm::Hole(hole_id)
                }
                else {
                    let it = InferTerm::Infer{id: *infertype_id};
                    *infertype_id += 1;
                    it
                },
        } ),
        type_: Rc::new(InferTerm::Infer{id: *infertype_id}),
    };
    *infertype_id += 1;
    itt
}

fn assign_abs(abs: HoledAbs, infertype_id: &mut u64) -> InferAbs {
    InferAbs{A: assign_term(abs.A, infertype_id), t: assign_term(abs.t, infertype_id)}
}

fn assign_env(env: HoledEnv, infertype_id: &mut u64) -> InferEnv {
    InferEnv{consts: env.consts.into_iter().map(|c| assign_const(c, infertype_id)).collect()}
}

#[derive(Clone, Debug)]
pub enum InferTerm {
    Const(ConstId),
    DBI(u64),
    Universe,
    App{s: InferTypedTerm, t: InferTypedTerm},
    Lam(InferAbs),
    Pi(InferAbs),
    Let{env: InferEnv, t: InferTypedTerm},
    Case{t: InferTypedTerm, cases: Vec<InferTypedTerm>, datatype: Option<ConstId>},
    Value(Value),
    Infer{id: u64},
    Hole(HoleId),
}

#[derive(Clone, Debug)]
pub struct InferAbs {
    pub A: InferTypedTerm,
    pub t: InferTypedTerm,
}

#[derive(Clone, Debug)]
pub struct InferEnv {
    pub consts: Vec<InferTypedConst>,
}

#[derive(Clone, Debug)]
pub struct InferTypedConst {
    c: Rc<InferConst>,
    type_: Rc<InferConst>,
}

#[derive(Clone, Debug)]
pub enum InferConst {
    Def(InferTypedTerm),
    DataType{param_types: Vec<InferTypedTerm>},
    Ctor{datatype: ConstId, arg_types: Vec<InferTypedTerm>},
}

#[derive(Clone, Debug)]
pub struct InferCtx {
    pub global: InferEnv,
    pub local: Vec<InferTypedTerm>,
    pub typings: Vec<InferTypedTerm>,
}

#[derive(Clone, Debug)]
pub struct InferTypedTerm {
    term: Rc<InferTerm>,
    type_: Rc<InferTerm>,
}

/*
 * Unify two terms of types, `a` and `b`, in a context `ctx`.
 * Note that these types need to be normalized enough.
 */
pub fn unify(a: Rc<HoledTerm>, b: Rc<HoledTerm>, ctx: &Ctx) -> Result<Rc<HoledTerm>, UnifyErr> {
    if let HoledTerm::Hole(..) = *b { return unify(b, a, ctx); }

    match *a.clone() {
        HoledTerm::Const(id_a) => match *b {
            HoledTerm::Const(id_b) if id_a == id_b => Ok(a),
            _ => Err(UnifyErr::TermsMismatched),
        }
        _ => unimplemented!(),
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum UnifyErr {
    TermsMismatched,
}