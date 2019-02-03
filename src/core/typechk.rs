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

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Value {
    Nat(::num::BigInt),
    Int(::num::BigInt),
    Str(String),
}

pub fn typechk_env(env: HoledEnv) -> Result<Ctx, TypeChkErr> {
    let mut infer_ctx = InferCtx{global: InferEnv{consts: Vec::new()}, local: Vec::new(), typings: Vec::new()};
    let mut next_inferterm_id = 0;

    for c in env.consts {
        infer_ctx.global.consts.push(assign_const(c, &mut next_inferterm_id));
    }
    for t in env.typings {
        infer_ctx.global.typings.push(assign_typing(t, &mut next_inferterm_id));
    }
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

fn assign_const(c: HoledConst, inferterm_id: &mut InferTermId) -> InferTypedConst {
    /* match c {
        HoledConst::Def(t) => InferTypedConst{c: InferConst::Def(assign_term(t, infertype_id)), type_: },
    } */

    unimplemented!()
}

fn assign_term(term: Rc<HoledTerm>, inferterm_id: &mut InferTermId) -> InferTypedTerm {
    let itt = InferTypedTerm {
        term: Rc::new( match *term {
            HoledTerm::Const(ref id) => InferTerm::Const(*id),
            HoledTerm::DBI(ref i) => InferTerm::DBI(*i),
            HoledTerm::Universe => InferTerm::Universe,
            HoledTerm::App{ref s, ref t} =>
                InferTerm::App{s: assign_term(s.clone(), inferterm_id), t: assign_term(t.clone(), inferterm_id)},
            HoledTerm::Lam(ref abs) => InferTerm::Lam(assign_abs(abs.clone(), inferterm_id)),
            HoledTerm::Pi(ref abs) => InferTerm::Pi(assign_abs(abs.clone(), inferterm_id)),
            HoledTerm::Let{ref env, ref t} =>
                InferTerm::Let{env: assign_env(env.clone(), inferterm_id), t: assign_term(t.clone(), inferterm_id)},
            HoledTerm::Case{ref t, ref cases, ref datatype} =>
                InferTerm::Case{
                    t: assign_term(t.clone(), inferterm_id),
                    cases: cases.iter().map(|case| assign_term(case.clone(), inferterm_id)).collect(),
                    datatype: *datatype,
                },
            HoledTerm::Value(ref val) => InferTerm::Value(val.clone()),
            HoledTerm::Hole(ref hole_id) =>
                if let Some(id) = *hole_id {
                    InferTerm::Infer{id: id}
                }
                else {
                    let it = InferTerm::Infer{id: *inferterm_id};
                    *inferterm_id += 1;
                    it
                },
        } ),
        type_: Rc::new( InferTerm::Infer{id: *inferterm_id} ),
    };
    *inferterm_id += 1;
    itt
}

fn assign_abs(abs: HoledAbs, inferterm_id: &mut InferTermId) -> InferAbs {
    InferAbs{A: assign_term(abs.A, inferterm_id), t: assign_term(abs.t, inferterm_id)}
}

fn assign_env(env: HoledEnv, inferterm_id: &mut InferTermId) -> InferEnv {
    InferEnv{consts: env.consts.into_iter().map(|c| assign_const(c, inferterm_id)).collect()}
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
    Infer{id: InferTermId},
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
    type_: Rc<InferTypedTerm>,
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

type Subst = Vec<(InferTermId, Rc<InferTerm>)>;
type InferTermId = usize;

/*
 * Unify two terms, `a` and `b`, in a context `ctx`.
 * Note that these terms need to be normalized enough.
 */
pub fn unify(a: Rc<InferTerm>, b: Rc<InferTerm>, ctx: &InferCtx, subst: &mut Subst) -> Result<Rc<InferTerm>, UnifyErr> {
    if let InferTerm::Infer{..} = *b {
        if let InferTerm::Infer{..} = *a {}
        else { return unify(b, a, ctx, subst); }
    }

    match *a.clone() {
        InferTerm::Infer{id: id_a} => match *b {
            InferTerm::Infer{id: id_b} if id_a == id_b => Ok(a),
            _ => {
                subst.push((id_a, b.clone()));
                Ok(b)
            },
        },
        InferTerm::Const(id_a) => /*match *b {
            InferTerm::Const(id_b) if id_a == id_b => Ok(a),
            _ => Err(UnifyErr::TermStructureMismatched),
        }*/ unimplemented!(),
        InferTerm::DBI(i) => match *b {
            InferTerm::DBI(j) if i == j => Ok(a),
            _ => Err(UnifyErr::TermStructureMismatched),
        },
        InferTerm::Universe => match *b {
            InferTerm::Universe => Ok(a),
            _ => Err(UnifyErr::TermStructureMismatched),
        },
        InferTerm::App{s: ref s_a, t: ref t_a} => match *b {
            InferTerm::App{s: ref s_b, t: ref t_b} => Ok(Rc::new( InferTerm::App {
                s: unify_typed(s_a.clone(), s_b.clone(), ctx, subst)?,
                t: unify_typed(t_a.clone(), t_b.clone(), ctx, subst)?,
            } )),
            _ => Err(UnifyErr::TermStructureMismatched),
        },
        InferTerm::Lam(InferAbs{A: ref A_a, t: ref t_a}) => match *b {
            InferTerm::Lam(InferAbs{A: ref A_b, t: ref t_b}) => Ok(Rc::new( InferTerm::Lam( InferAbs {
                A: unify_typed(A_a.clone(), A_b.clone(), ctx, subst)?,
                t: unify_typed(t_a.clone(), t_b.clone(), ctx, subst)?
            } ) )),
            _ => Err(UnifyErr::TermStructureMismatched),
        }
        InferTerm::Pi(InferAbs{A: ref A_a, t: ref t_a}) => match *b {
            InferTerm::Pi(InferAbs{A: ref A_b, t: ref t_b}) => Ok(Rc::new( InferTerm::Pi( InferAbs {
                A: unify_typed(A_a.clone(), A_b.clone(), ctx, subst)?,
                t: unify_typed(t_a.clone(), t_b.clone(), ctx, subst)?,
            } ) )),
            _ => Err(UnifyErr::TermStructureMismatched),
        },
        InferTerm::Let{..} => unimplemented!(),
        InferTerm::Case{..} => unimplemented!(),
        InferTerm::Value(ref v_a) => match *b {
            InferTerm::Value(ref v_b) =>
                if v_a == v_b { Ok(a) }
                else { Err(UnifyErr::ValueMismatched(v_a.clone(), v_b.clone())) },
            _ => Err(UnifyErr::TermStructureMismatched),
        },
    }
}

fn unify_typed(a: InferTypedTerm, b: InferTypedTerm, ctx: &InferCtx, subst: &mut Subst)
    -> Result<InferTypedTerm, UnifyErr>
{
    Ok( InferTypedTerm{term: unify(a.term, b.term, ctx, subst)?, type_: unify(a.type_, b.type_, ctx, subst)?} )
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum UnifyErr {
    TermStructureMismatched,
    ValueMismatched(Value, Value),
}