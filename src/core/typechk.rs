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
    pub nof_named_hole: usize,
}

#[derive(Clone, Debug)]
pub enum HoledConst {
    Def(Rc<HoledTerm>),
    DataType{param_types: Vec<Rc<HoledTerm>>},
    Ctor{datatype: ConstId, type_: Rc<HoledTerm>},
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
    tower: Vec<Rc<Term>>,
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

/*
    - Typing rules -

    W-Empty
        => WF([])[]
    
    W-Local-Assum
        E[G] |- T:type => WF(E)[G :: T]

    W-Global-Def
        E[G] |- t:T => WF(E :: (x := t:T))[G]
    
    W-Global-Assum
        E[] |- T,U:type , E[] |- t:U => WF(E :: t:T)[]

    Ax-Type
        WF(E)[G] => E[G] |- type_i : type_(i+1)
    
    Const
        WF(E)[G] , (c := t:T) in E
            => E[G] |- c : T
    
    Prod-Type
        E[G] |- T : type_i , E[G :: T] |- U : type_i
            => E[G] |- (|:T| U) : type_i
    
    Lam
        E[G] |- (|:T| U) : type , E[G :: T] |- t : U
            => E[G] |- (\:T -> t) : |:T| U
    
    App
        E[G] |- t : |:U| T , E[G] |- u : U
            E[G] |- (t u) : T[0/u]

    Case
        E[G] |- t:T , (datatype D .. { ... C<i> : (... |:T<i>| ... D') ... }) in E
            => case t of { ... u<i> ... } : T
*/

pub fn typechk(env: HoledEnv) -> Result<Env, TypeChkErr> {
    // let mut infer_ctx = InferCtx{global: InferEnv{consts: Vec::new()}, local: Vec::new(), typings: Vec::new()};
    let mut next_inferterm_id = 0;
    let mut consts = assign_env(env, &mut next_inferterm_id);
    let mut substs = consts.iter().map( |c| unimplemented!() );

    unimplemented!()
}

fn typechk_ctx(ctx: &InferCtx, substs: &mut Vec<Subst>) -> Result<(), TypeChkErr> {
    // checks W-Local-Assum
    for T in &ctx.local {
        unify(T.tower[1].clone(), Rc::new(InferTerm::Universe), ctx, substs)?;
    }

    // checks W-Global_Assum
    for (t,T) in &ctx.typings {
        unify(T.tower[1].clone(), Rc::new(InferTerm::Universe), ctx, substs)?;
    }

    Ok(())
}

fn typechk_const(ctx: &InferCtx, c: InferTypedConst, substs: &mut Vec<Subst>, next_inferterm_id: &mut InferTermId)
    -> Result<(), TypeChkErr>
{
    unimplemented!()
}

fn typechk_term(ctx: &InferCtx, term: InferTypedTerm, substs: &mut Vec<Subst>, next_inferterm_id: &mut InferTermId)
    -> Result<(), TypeChkErr>
{
    fn new_inferterm(next_inferterm_id: &mut InferTermId) -> Rc<InferTerm> {
        let id = *next_inferterm_id;
        *next_inferterm_id += 1;
        Rc::new(InferTerm::Infer{id})
    }

    match *term.tower[0] {
        InferTerm::Const(const_id) =>
            unify(term.tower[1].clone(), ctx.consts[const_id].type_.tower[0].clone(), ctx, substs)?,
        InferTerm::DBI(i) =>
            unify(term.tower[1].clone(), ctx.local(i).tower[0].clone(), ctx, substs)?,
        InferTerm::Universe =>
            unify(term.tower[1].clone(), term.tower[0].clone(), ctx, substs)?,
        InferTerm::App{ref s, ref t} => {
            typechk_term(ctx, s.clone(), substs, next_inferterm_id)?;
            typechk_term(ctx, t.clone(), substs, next_inferterm_id)?;
            
            let T = new_inferterm(next_inferterm_id);

            unify( s.tower[1].clone(),
                Rc::new( InferTerm::Pi( InferAbs {
                    A: InferTypedTerm{tower: vec![ t.tower[1].clone(), Rc::new(InferTerm::Universe) ]},
                    t: InferTypedTerm{tower: vec![ T.clone(), Rc::new(InferTerm::Universe) ]},
                } ) ),
                ctx, substs )?;

            unify( term.tower[1].clone(),
                Rc::new( InferTerm::App {
                    s: InferTypedTerm{tower: vec![T, Rc::new(InferTerm::Universe)]},
                    t: InferTypedTerm{tower: vec![t.tower[0].clone(), Rc::new(InferTerm::Universe)]},
                } ),
                ctx, substs )?;
        },
        InferTerm::Lam(InferAbs{A: ref T, ref t}) => {
            typechk_term(ctx, T.clone(), substs, next_inferterm_id)?;
            typechk_term(ctx, t.clone(), substs, next_inferterm_id)?;

            let universe = Rc::new(InferTerm::Universe);
            let U = new_inferterm(next_inferterm_id);

            unify(term.tower[1].clone(), universe, ctx, substs)?;
            unify(t.tower[1].clone(), U, ctx, substs)?;
        },
        InferTerm::Pi(InferAbs{A: ref T, t: ref U}) => {
            typechk_term(ctx, T.clone(), substs, next_inferterm_id)?;
            typechk_term(ctx, U.clone(), substs, next_inferterm_id)?;

            let universe = Rc::new(InferTerm::Universe);

            unify(T.tower[1].clone(), universe.clone(), ctx, substs)?;
            {
                let mut local_ctx = ctx.clone();
                local_ctx.local.push(T.clone());
                unify(U.tower[1].clone(), universe.clone(), &local_ctx, substs)?;
            }
            unify(term.tower[1].clone(), universe, ctx, substs)?;
        },
        InferTerm::Let{ref env, ref t} => {
            for c in env {
                typechk_const(ctx, c.clone(), substs, next_inferterm_id)?;
            }

            let mut local_ctx = ctx.clone();
            local_ctx.consts.extend(env.iter().cloned());
            typechk_term(&local_ctx, t.clone(), substs, next_inferterm_id)?;
        },
        InferTerm::Case{ref t, ref cases, ref datatype} => unimplemented!(),
        InferTerm::Value(ref v) => unimplemented!(),
        InferTerm::Infer{..} => (),
    }

    Ok(())
}

fn typechk_typing(ctx: &InferCtx, t: InferTypedTerm, T: InferTypedTerm, substs: &mut Vec<Subst>)
    -> Result<(), TypeChkErr>
{
    unify(t.tower[1].clone(), T.tower[0].clone(), ctx, substs)?;
    unify(T.tower[1].clone(), Rc::new(InferTerm::Universe), ctx, substs)?;
    Ok(())
}

pub enum TypeChkErr {
    UnifyErr(UnifyErr),
}
impl From<UnifyErr> for TypeChkErr {
    fn from(e: UnifyErr) -> Self {
        TypeChkErr::UnifyErr(e)
    }
}

fn assign_const(c: HoledConst, inferterm_id: &mut InferTermId) -> InferTypedConst {
    let itc = InferTypedConst {
        c: match c {
            HoledConst::Def(t) => InferConst::Def(assign_term(t, inferterm_id)),
            HoledConst::DataType{param_types} => InferConst::DataType {
                param_types: param_types.into_iter().map(|t| assign_term(t, inferterm_id)).collect(),
            },
            HoledConst::Ctor{datatype, type_} => InferConst::Ctor{datatype, type_: assign_term(type_, inferterm_id)},
        },
        type_: InferTypedTerm{tower: (0..1).map(|i| Rc::new(InferTerm::Infer{id: *inferterm_id + i})).collect()},
    };
    *inferterm_id += 2;

    itc
}

fn assign_term(term: Rc<HoledTerm>, inferterm_id: &mut InferTermId) -> InferTypedTerm {
    let itt = InferTypedTerm {
        tower: vec![
            Rc::new( match *term {
                HoledTerm::Const(ref id) => InferTerm::Const(*id),
                HoledTerm::DBI(ref i) => InferTerm::DBI(*i as usize),
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
            Rc::new(InferTerm::Infer{id: *inferterm_id}),
        ],
    };
    *inferterm_id += 1;

    itt
}

fn assign_abs(abs: HoledAbs, inferterm_id: &mut InferTermId) -> InferAbs {
    InferAbs{A: assign_term(abs.A, inferterm_id), t: assign_term(abs.t, inferterm_id)}
}

fn assign_env(env: HoledEnv, inferterm_id: &mut InferTermId) -> InferEnv {
    env.consts.into_iter().map(|c| assign_const(c, inferterm_id)).collect()
}

#[derive(Clone, Debug)]
pub enum InferTerm {
    Const(ConstId),
    DBI(usize),
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
pub struct InferTypedConst {
    c: InferConst,
    type_: InferTypedTerm, // Filled before a type checking.
}

#[derive(Clone, Debug)]
pub enum InferConst {
    Def(InferTypedTerm),
    DataType{param_types: Vec<InferTypedTerm>},
    Ctor{datatype: ConstId, type_: InferTypedTerm},
}

type InferEnv = Vec<InferTypedConst>;

#[derive(Clone, Debug)]
pub struct InferCtx {
    pub consts: InferEnv,
    pub local: Vec<InferTypedTerm>,
    pub typings: Vec<(InferTypedTerm, InferTypedTerm)>,
}
impl InferCtx {
    fn local(&self, dbi: usize) -> &InferTypedTerm {
        &self.local[self.local.len() - dbi]
    }
}

#[derive(Clone, Debug)]
pub struct InferTypedTerm {
    tower: Vec<Rc<InferTerm>>,
}

type InferTermId = usize;

#[derive(Clone, Debug)]
pub enum Subst {
    Eq(InferTermId, InferTermId),
    Concrete(InferTermId, Rc<InferTerm>),
}
impl Subst {
    fn new(lhs: InferTermId, rhs: Rc<InferTerm>) -> Self {
        if let InferTerm::Infer{id} = *rhs { Subst::Eq(lhs, id) }
        else { Subst::Concrete(lhs, rhs) }
    }
}

/*
 * Unify two terms, `a` and `b`, in a context `ctx`.
 * Note that these terms need to be normalized enough.
 */
pub fn unify(a: Rc<InferTerm>, b: Rc<InferTerm>, ctx: &InferCtx, substs: &mut Vec<Subst>) -> Result<(), UnifyErr> {
    if let InferTerm::Infer{..} = *b {
        if let InferTerm::Infer{..} = *a {}
        else { return unify(b, a, ctx, substs); }
    }

    match *a.clone() {
        InferTerm::Infer{id: id_a} => match *b {
            InferTerm::Infer{id: id_b} if id_a == id_b => (),
            _ => substs.push( Subst::new(id_a, b.clone()) ),
        },
        InferTerm::Const(id_a) => match *b {
            InferTerm::Const(id_b) if id_a == id_b => (),
            _ => return Err(UnifyErr::TermStructureMismatched),
        },
        InferTerm::DBI(i) => match *b {
            InferTerm::DBI(j) if i == j => (),
            _ => return Err(UnifyErr::TermStructureMismatched),
        },
        InferTerm::Universe => match *b {
            InferTerm::Universe => (),
            _ => return Err(UnifyErr::TermStructureMismatched),
        },
        InferTerm::App{s: ref s_a, t: ref t_a} => match *b {
            InferTerm::App{s: ref s_b, t: ref t_b} => {
                unify_typed(s_a.clone(), s_b.clone(), ctx, substs)?;
                unify_typed(t_a.clone(), t_b.clone(), ctx, substs)?;
            },
            _ => return Err(UnifyErr::TermStructureMismatched),
        },
        InferTerm::Lam(InferAbs{A: ref A_a, t: ref t_a}) => match *b {
            InferTerm::Lam(InferAbs{A: ref A_b, t: ref t_b}) => {
                unify_typed(A_a.clone(), A_b.clone(), ctx, substs)?;
                unify_typed(t_a.clone(), t_b.clone(), ctx, substs)?;
            },
            _ => return Err(UnifyErr::TermStructureMismatched),
        }
        InferTerm::Pi(InferAbs{A: ref A_a, t: ref t_a}) => match *b {
            InferTerm::Pi(InferAbs{A: ref A_b, t: ref t_b}) => {
                unify_typed(A_a.clone(), A_b.clone(), ctx, substs)?;
                unify_typed(t_a.clone(), t_b.clone(), ctx, substs)?;
            }
            _ => return Err(UnifyErr::TermStructureMismatched),
        },
        InferTerm::Let{..} => return Err(UnifyErr::TermStructureMismatched),
        InferTerm::Case{..} => return Err(UnifyErr::TermStructureMismatched),
        InferTerm::Value(ref v_a) => match *b {
            InferTerm::Value(ref v_b) =>
                if v_a == v_b {}
                else { return Err(UnifyErr::ValueMismatched(v_a.clone(), v_b.clone())) },
            _ => return Err(UnifyErr::TermStructureMismatched),
        },
    };

    Ok(())
}

fn unify_typed(a: InferTypedTerm, b: InferTypedTerm, ctx: &InferCtx, substs: &mut Vec<Subst>)
    -> Result<(), UnifyErr>
{
    Ok( 
        a.tower.into_iter().zip(b.tower).try_for_each(|(a,b)| unify(a, b, ctx, substs))?
    )
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum UnifyErr {
    TermStructureMismatched,
    ValueMismatched(Value, Value),
}