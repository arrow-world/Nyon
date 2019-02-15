use std::cell::Cell;
use std::collections::HashMap;
use super::{ConstId, HoleId, SpecialType};

use std::rc::Rc;

#[derive(Clone, Debug, PartialEq, Eq)]
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HoledAbs {
    pub A: Rc<HoledTerm>,
    pub t: Rc<HoledTerm>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HoledEnv {
    pub consts: Vec<HoledConst>,
    pub typings: Vec<(Rc<HoledTerm>, Rc<HoledTerm>)>,
    pub nof_named_hole: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HoledConst {
    Def(Rc<HoledTerm>),
    DataType{param_types: Vec<Rc<HoledTerm>>, ctors: Vec<ConstId>},
    Ctor{datatype: ConstId, param_types: Vec<Rc<HoledTerm>>},
}

#[derive(Clone, Debug)]
pub enum Term {
    Const(ConstId),
    DBI(usize),
    Universe,
    App{s: TypedTerm, t: TypedTerm},
    Lam(Abs),
    Pi(Abs),
    Let{env: Env, t: TypedTerm},
    Case{t: TypedTerm, cases: Vec<TypedTerm>},
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

type Env = Vec<TypedConst>;

#[derive(Clone, Debug)]
pub enum Const {
    Def(TypedTerm),
    DataType{param_types: Vec<TypedTerm>},
    Ctor{datatype: ConstId, param_types: Vec<TypedTerm>},
}

#[derive(Clone, Debug)]
pub struct TypedConst {
    c: Const,
    type_: TypedTerm,
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
    debug!("starting type checking...");
    debug!("target:\n{}", env);

    let mut next_inferterm_id = 0;
    let mut ctx = InferCtx {
        consts: assign_consts(env.consts, &mut next_inferterm_id),
        local: vec![],
        typings: env.typings.into_iter().map( |(t,T)|
            (assign_term(t, &mut next_inferterm_id), assign_term(T, &mut next_inferterm_id))
        ).collect(),
    };

    debug!("initial context:\n{}", ctx);

    let mut substs: Vec<Subst> = vec![];
    let mut substs_map: HashMap<InferTermId, Rc<InferTerm>> = HashMap::new();
    for count in 0.. {
        debug!("iteration {}.", count);
        debug!("current context: {}", ctx);

        typechk_ctx(&ctx, &mut substs, &mut next_inferterm_id)?;

        debug!("collected substitutions:");
        for subst in &substs {
            debug!("\t{}", subst);
        }

        while !substs.is_empty() {
            for subst in substs.split_off(0) {
                match subst {
                    Subst::Eq(mut lhs, mut rhs) => {
                        if rhs > lhs { ::std::mem::swap(&mut lhs, &mut rhs); }
                        if rhs == lhs { continue; }
                        assert!(lhs > rhs);

                        if let Some(instance) = substs_map.remove(&lhs.get()) {
                            if let Some(other) = substs_map.get(&rhs.get()) {
                                unify(instance.clone(), other.clone(), &ctx, &mut substs)?;
                            }
                            substs_map.insert(rhs.get(), instance);
                        }
                        lhs.set(rhs.get());
                    },
                    Subst::Instantiate(id, instance) => {
                        if let Some(other) = substs_map.get(&id.get()).cloned() {
                            unify(instance, other, &ctx, &mut substs)?;
                        }
                        else {
                            substs_map.insert(id.get(), instance);
                        }
                    }
                }
            }
        }

        debug!("substitutions:");
        for (k,v) in &substs_map {
            debug!("\t?{} / {}", k, v);
        }
        debug!("current context:");
        debug!("{}\n", ctx);

        let subst_result = subst_infers(&mut ctx, &mut substs_map);

        debug!("substitution result:");
        debug!("found_infer?: {}", subst_result.found_infer);
        debug!("has_substed?: {}", subst_result.has_substed);
        debug!("{}\n", ctx);

        if !subst_result.found_infer {
            break;
        }
        else if !subst_result.has_substed {
            return Err(TypeChkErr::InferFailure);
        }
    }

    debug!("finished type checking.");
    debug!("current context:\n{}", ctx);

    Ok( cast_no_infer(ctx) )
}

fn subst_infers(ctx: &mut InferCtx, substs_map: &mut HashMap<InferTermId, Rc<InferTerm>>) -> SubstResult {
    assert!(ctx.local.is_empty());

    let mut result = SubstResult{has_substed: false, found_infer: false};

    subst_infers_env(&mut ctx.consts, substs_map, &mut result);

    for (t,T) in &mut ctx.typings {
        subst_infers_typed_term(t, substs_map, &mut result);
        subst_infers_typed_term(T, substs_map, &mut result);
    }

    return result;

    fn subst_infers_env(env: &mut InferEnv, substs: &mut Substs, result: &mut SubstResult) {
        for c in env {
            match c.c {
                InferConst::Def(ref mut t) =>
                    subst_infers_typed_term(t, substs, result),
                InferConst::DataType{ref mut param_types, ref ctors} =>
                    for param_type in param_types {
                        subst_infers_typed_term(param_type, substs, result);
                    },
                InferConst::Ctor{datatype: _datatype, ref mut param_types} =>
                    param_types.iter_mut().for_each(
                        |param_type| subst_infers_typed_term(param_type, substs, result)
                    ),
            }
            subst_infers_typed_term(&mut c.type_, substs, result);
        }
    }

    fn subst_infers_typed_term(t: &mut InferTypedTerm, substs: &mut Substs, result: &mut SubstResult) {
        for term in &mut t.tower {
            subst_infers_term(term, substs, result);
        }
    }

    fn subst_infers_term(t: &mut Rc<InferTerm>, substs: &mut Substs, result: &mut SubstResult) {
        if let InferTerm::Infer{ref id} = *t.clone() {
            if let Some(instance) = substs.get(&id.get()) {
                *Rc::make_mut(t) = (**instance).clone();
                result.has_substed = true;
            }
            result.found_infer = true;
        }
        else {
            match *Rc::make_mut(t) {
                InferTerm::App{ref mut s, ref mut t} => {
                    subst_infers_typed_term(s, substs, result);
                    subst_infers_typed_term(t, substs, result);
                },
                InferTerm::Lam(ref mut abs) => subst_infers_abs(abs, substs, result),
                InferTerm::Pi(ref mut abs) => subst_infers_abs(abs, substs, result),
                InferTerm::Let{ref mut env, ref mut t} => {
                    subst_infers_env(env, substs, result);
                    subst_infers_typed_term(t, substs, result);
                },
                InferTerm::Case{ref mut t, ref mut cases, ..} => {
                    subst_infers_typed_term(t, substs, result);
                    for case in cases {
                        subst_infers_typed_term(case, substs, result);
                    }
                },
                _ => (),
            }
        }
    }

    fn subst_infers_abs(abs: &mut InferAbs, substs: &mut Substs, result: &mut SubstResult) {
        subst_infers_typed_term(&mut abs.A, substs, result);
        subst_infers_typed_term(&mut abs.t, substs, result);
    }
    
    type Substs = HashMap<InferTermId, Rc<InferTerm>>;
}
pub struct SubstResult {
    has_substed: bool,
    found_infer: bool,
}

fn cast_no_infer(ctx: InferCtx) -> Env {
    assert!(ctx.local.is_empty());

    ctx.typings.into_iter().for_each( |(t,T)| {
        cast_no_infer_typed_term(t);
        cast_no_infer_typed_term(T);
    } );

    return cast_no_infer_env(ctx.consts);

    fn cast_no_infer_env(env: InferEnv) -> Env {
        env.into_iter().map( |c| TypedConst {
            c: match c.c {
                InferConst::Def(t) => Const::Def(cast_no_infer_typed_term(t)),
                InferConst::DataType{param_types, ctors} => Const::DataType {
                    param_types: param_types.into_iter().map(|T| cast_no_infer_typed_term(T)).collect(),
                },
                InferConst::Ctor{datatype, param_types} => Const::Ctor {
                    datatype,
                    param_types: param_types.into_iter()
                        .map(|param_type| cast_no_infer_typed_term(param_type)).collect(),
                },
            },
            type_: cast_no_infer_typed_term(c.type_),
        } ).collect()
    }

    fn cast_no_infer_typed_term(term: InferTypedTerm) -> TypedTerm {
        TypedTerm{tower: term.tower.into_iter().map(|t| cast_no_infer_term(t)).collect()}
    }

    fn cast_no_infer_term(term: Rc<InferTerm>) -> Rc<Term> {
        Rc::new( match *term {
            InferTerm::Const(const_id) => Term::Const(const_id),
            InferTerm::DBI(i) => Term::DBI(i),
            InferTerm::Universe => Term::Universe,
            InferTerm::App{ref s, ref t} => Term::App {
                s: cast_no_infer_typed_term(s.clone()),
                t: cast_no_infer_typed_term(t.clone()),
            },
            InferTerm::Lam(ref abs) => Term::Lam(cast_no_infer_abs(abs.clone())),
            InferTerm::Pi(ref abs) => Term::Pi(cast_no_infer_abs(abs.clone())),
            InferTerm::Let{ref env, ref t} => Term::Let {
                env: cast_no_infer_env(env.clone()),
                t: cast_no_infer_typed_term(t.clone()),
            },
            InferTerm::Case{ref t, ref cases, ref datatype} => Term::Case {
                t: cast_no_infer_typed_term(t.clone()),
                cases: cases.iter().map(|t| cast_no_infer_typed_term(t.clone())).collect(),
            },
            InferTerm::Value(ref v) => Term::Value(v.clone()),
            InferTerm::Infer{..} => unreachable!(),
            InferTerm::Subst{..} => unreachable!(),
        } )
    }

    fn cast_no_infer_abs(abs: InferAbs) -> Abs {
        Abs{A: cast_no_infer_typed_term(abs.A), t: cast_no_infer_typed_term(abs.t)}
    }
}

fn typechk_ctx(ctx: &InferCtx, substs: &mut Vec<Subst>, next_inferterm_id: &mut InferTermId)
    -> Result<(), TypeChkErr>
{
    // checks W-Global-Def
    for (const_id, c) in ctx.consts.iter().enumerate() {
        typechk_const(ctx, c, const_id, substs, next_inferterm_id)?;
    }

    // checks W-Local-Assum
    for T in &ctx.local {
        typechk_term(ctx, T, substs, next_inferterm_id)?;

        unify(T.tower[1].clone(), Rc::new(InferTerm::Universe), ctx, substs)?;
    }

    // checks W-Global-Assum
    for (t,T) in &ctx.typings {
        typechk_term(ctx, t, substs, next_inferterm_id)?;
        typechk_term(ctx, T, substs, next_inferterm_id)?;

        unify(t.tower[1].clone(), T.tower[0].clone(), ctx, substs)?;
        unify(T.tower[1].clone(), Rc::new(InferTerm::Universe), ctx, substs)?;
    }

    Ok(())
}

fn typechk_const (
    ctx: &InferCtx,
    c: &InferTypedConst, id: ConstId,
    substs: &mut Vec<Subst>,
    next_inferterm_id: &mut InferTermId
)
    -> Result<(), TypeChkErr>
{
    match c.c {
        InferConst::Def(ref t) => {
            typechk_term(ctx, t, substs, next_inferterm_id)?;
            unify(c.type_.tower[0].clone(), t.tower[1].clone(), ctx, substs)?;
        },
        InferConst::DataType{ref param_types, ref ctors} => {
            for param_type in param_types {
                typechk_term(ctx, param_type, substs, next_inferterm_id)?;
            }

            let universe = Rc::new(InferTerm::Universe);
            let type_ = param_types.iter().fold( universe.clone(),
                |U, param_type| Rc::new( InferTerm::Pi( InferAbs {
                    A: param_type.clone(),
                    t: InferTypedTerm{tower: vec![U, universe.clone()]},
                } ) )
            );
            unify(c.type_.tower[0].clone(), type_, ctx, substs)?;
        },
        InferConst::Ctor{datatype, ref param_types} => {
            for param_type in param_types {
                typechk_term(ctx, param_type, substs, next_inferterm_id)?;
            }

            let datatype_param_types =
                if let InferConst::DataType{ref param_types, ..} = ctx.consts[datatype].c { param_types }
                else { unreachable!() };

            let universe = Rc::new(InferTerm::Universe);
            
            let type_ =
                datatype_param_types.iter().chain(param_types).rev().fold(
                    (0..datatype_param_types.len()).rev().fold( Rc::new(InferTerm::Const(datatype)),
                        |f, dbi_offset| Rc::new( InferTerm::App {
                            s: InferTypedTerm{tower: vec![f, Rc::new(new_inferterm(next_inferterm_id))]}, 
                            t: InferTypedTerm { tower: vec![
                                Rc::new(InferTerm::DBI(param_types.len() + dbi_offset)),
                                Rc::new(new_inferterm(next_inferterm_id)),
                            ] },
                        })
                    ),
                    |tail, param_type| Rc::new( InferTerm::Pi( InferAbs {
                        A: param_type.clone(),
                        t: InferTypedTerm{tower: vec![tail, universe.clone()]},
                    } ) )
                );
            
            unify(c.type_.tower[0].clone(), type_, ctx, substs)?;
        },
    }

    Ok(())
}

fn typechk_term(ctx: &InferCtx, term: &InferTypedTerm, substs: &mut Vec<Subst>, next_inferterm_id: &mut InferTermId)
    -> Result<(), TypeChkErr>
{
    debug!("Checks {} ...", term);
    // debug!("{}", ctx);

    match *term.tower[0] {
        InferTerm::Const(const_id) =>
            unify(term.tower[1].clone(), ctx.consts[const_id].type_.tower[0].clone(), ctx, substs)?,
        InferTerm::DBI(i) => unify(term.tower[1].clone(), ctx.local(i).tower[0].clone(), ctx, substs)?,
        InferTerm::Universe =>
            unify(term.tower[1].clone(), term.tower[0].clone(), ctx, substs)?,
        InferTerm::App{s: ref t, t: ref u} => {
            typechk_term(ctx, t, substs, next_inferterm_id)?;
            typechk_term(ctx, u, substs, next_inferterm_id)?;
            
            let T = Rc::new(new_inferterm(next_inferterm_id));

            unify( t.tower[1].clone(),
                Rc::new( InferTerm::Pi( InferAbs {
                    A: InferTypedTerm{tower: vec![ u.tower[1].clone(), Rc::new(InferTerm::Universe) ]},
                    t: InferTypedTerm{tower: vec![ T.clone(), Rc::new(InferTerm::Universe) ]},
                } ) ),
                ctx, substs )?;

            unify( term.tower[1].clone(),
                Rc::new( InferTerm::Subst {
                    t: T,
                    dbi: 0,
                    u: u.tower[0].clone(),
                } ),
                ctx, substs )?;
        },
        InferTerm::Lam(InferAbs{A: ref T, ref t}) => {
            let mut local_ctx = ctx.clone();
            local_ctx.local.push(T.clone());

            typechk_term(ctx, T, substs, next_inferterm_id)?;
            typechk_term(&local_ctx, t, substs, next_inferterm_id)?;

            let U = Rc::new(new_inferterm(next_inferterm_id));

            unify(t.tower[1].clone(), U.clone(), &local_ctx, substs)?;

            let type_ = Rc::new( InferTerm::Pi( InferAbs {
                A: T.clone(),
                t: InferTypedTerm{tower: vec![U, Rc::new(InferTerm::Universe)]},
            } ) );
            unify(term.tower[1].clone(), type_, ctx, substs)?;
        },
        InferTerm::Pi(InferAbs{A: ref T, t: ref U}) => {
            let mut local_ctx = ctx.clone();
            local_ctx.local.push(T.clone());

            typechk_term(ctx, T, substs, next_inferterm_id)?;
            typechk_term(&local_ctx, U, substs, next_inferterm_id)?;

            let universe = Rc::new(InferTerm::Universe);

            unify(T.tower[1].clone(), universe.clone(), ctx, substs)?;
            unify(U.tower[1].clone(), universe.clone(), &local_ctx, substs)?;
            unify(term.tower[1].clone(), universe, ctx, substs)?;
        },
        InferTerm::Let{ref env, ref t} => {
            let mut local_ctx = ctx.clone();
            local_ctx.consts.extend(env.iter().cloned());

            let base_const_id = ctx.consts.len();
            for (offset, c) in env.iter().enumerate() {
                typechk_const(ctx, c, base_const_id + offset, substs, next_inferterm_id)?;
            }

            typechk_term(&local_ctx, t, substs, next_inferterm_id)?;

            unify(term.tower[1].clone(), t.tower[1].clone(), ctx, substs)?;
        },
        InferTerm::Case{ref t, ref cases, ref datatype} => {
            typechk_term(ctx, t, substs, next_inferterm_id)?;
            for case in cases {
                typechk_term(ctx, case, substs, next_inferterm_id)?;
            }

            if let Some(datatype) = datatype {
                unify(t.tower[1].clone(), Rc::new(InferTerm::Const(*datatype)), ctx, substs)?;

                let types_of_cases: Vec<Rc<InferTerm>> = cases.iter().enumerate().map( |(ctor_no, case)| {
                    let type_ = Rc::new(new_inferterm(next_inferterm_id));

                    let ctors =
                        if let InferConst::DataType{ref ctors, ..} = ctx.consts[*datatype].c { ctors }
                        else { unreachable!() };
                    
                    let type_of_ctor = ctx.consts[ctors[ctor_no]].type_.tower[0].clone();
                    unify(case.tower[1].clone(), type_of_ctor, ctx, substs)?;

                    Ok(type_)
                } ).collect::<Result<_, UnifyErr>>()?;

                let universe = Rc::new(InferTerm::Universe);

                let type_ = Rc::new( InferTerm::Case {
                    t: t.clone(),
                    cases:
                        types_of_cases.into_iter()
                            .map( |T| InferTypedTerm{tower: vec![T, universe.clone()]} ).collect(),
                    datatype: Some(*datatype),
                } );

                unify(term.tower[1].clone(), type_, ctx, substs)?;
            }
        },
        InferTerm::Value(ref v) =>
            unify(term.tower[1].clone(), match *v {
                Value::Nat(..) => unimplemented!(),
                Value::Int(..) => unimplemented!(),
                Value::Str(..) => unimplemented!(),
            }, ctx, substs)?,
        InferTerm::Infer{..} => (),
        InferTerm::Subst{..} => (),
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

#[derive(Clone, Debug)]
pub enum TypeChkErr {
    UnifyErr(UnifyErr),
    InferFailure,
}
impl From<UnifyErr> for TypeChkErr {
    fn from(e: UnifyErr) -> Self {
        TypeChkErr::UnifyErr(e)
    }
}

fn assign_consts(consts: Vec<HoledConst>, inferterm_id: &mut InferTermId) -> InferEnv {
    consts.into_iter().map(|c| assign_const(c, inferterm_id)).collect()
}

fn assign_const(c: HoledConst, inferterm_id: &mut InferTermId) -> InferTypedConst {
    let itc = InferTypedConst {
        c: match c {
            HoledConst::Def(t) => InferConst::Def(assign_term(t, inferterm_id)),
            HoledConst::DataType{param_types, ctors} => InferConst::DataType {
                param_types: param_types.into_iter().map(|t| assign_term(t, inferterm_id)).collect(),
                ctors,
            },
            HoledConst::Ctor{datatype, param_types} => InferConst::Ctor {
                datatype,
                param_types: param_types.into_iter().map(|T| assign_term(T, inferterm_id)).collect(),
            },
        },
        type_: InferTypedTerm{tower: vec![Rc::new(new_inferterm(inferterm_id)), Rc::new(InferTerm::Universe)]},
    };

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
                HoledTerm::Let{ref env, ref t} => {
                    assert!(env.typings.is_empty());
                    assert_eq!(env.nof_named_hole, 0);

                    InferTerm::Let {
                        env: assign_consts(env.consts.clone(), inferterm_id),
                        t: assign_term(t.clone(), inferterm_id)
                    }
                }
                HoledTerm::Case{ref t, ref cases, ref datatype} =>
                    InferTerm::Case{
                        t: assign_term(t.clone(), inferterm_id),
                        cases: cases.iter().map(|case| assign_term(case.clone(), inferterm_id)).collect(),
                        datatype: *datatype,
                    },
                HoledTerm::Value(ref val) => InferTerm::Value(val.clone()),
                HoledTerm::Hole(ref hole_id) =>
                    if let Some(id) = *hole_id {
                        InferTerm::Infer{id: Rc::new(Cell::new(id))}
                    }
                    else {
                        new_inferterm(inferterm_id)
                    },
            } ),
            Rc::new(new_inferterm(inferterm_id)),
        ],
    };

    itt
}

fn new_inferterm(next_inferterm_id: &mut InferTermId) -> InferTerm {
    let id = Rc::new(Cell::new(*next_inferterm_id));
    *next_inferterm_id += 1;
    InferTerm::Infer{id}
}

fn assign_abs(abs: HoledAbs, inferterm_id: &mut InferTermId) -> InferAbs {
    InferAbs{A: assign_term(abs.A, inferterm_id), t: assign_term(abs.t, inferterm_id)}
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
    Infer{id: Rc<Cell<InferTermId>>},
    Subst{t: Rc<InferTerm>, dbi: usize, u: Rc<InferTerm>},
}

#[derive(Clone, Debug)]
pub struct InferAbs {
    pub A: InferTypedTerm,
    pub t: InferTypedTerm,
}

#[derive(Clone, Debug)]
pub struct InferTypedConst {
    pub(super) c: InferConst,
    pub(super) type_: InferTypedTerm,
}

#[derive(Clone, Debug)]
pub enum InferConst {
    Def(InferTypedTerm),
    DataType{param_types: Vec<InferTypedTerm>, ctors: Vec<ConstId>},
    Ctor{datatype: ConstId, param_types: Vec<InferTypedTerm>},
}

pub(super) type InferEnv = Vec<InferTypedConst>;

#[derive(Clone, Debug)]
pub struct InferCtx {
    pub consts: InferEnv,
    pub local: Vec<InferTypedTerm>,
    pub typings: Vec<(InferTypedTerm, InferTypedTerm)>,
}
impl InferCtx {
    fn local(&self, dbi: usize) -> &InferTypedTerm {
        &self.local[self.local.len() - dbi - 1]
    }
}

#[derive(Clone, Debug)]
pub struct InferTypedTerm {
    pub(super) tower: Vec<Rc<InferTerm>>,
}

type InferTermId = usize;

#[derive(Clone, Debug)]
pub enum Subst {
    Eq(Rc<Cell<InferTermId>>, Rc<Cell<InferTermId>>),
    Instantiate(Rc<Cell<InferTermId>>, Rc<InferTerm>),
}
impl Subst {
    fn new(lhs: Rc<Cell<InferTermId>>, rhs: Rc<InferTerm>) -> Self {
        if let InferTerm::Infer{ref id} = *rhs.clone() { Subst::Eq(lhs, id.clone()) }
        else { Subst::Instantiate(lhs, rhs) }
    }
}

/*
 * Unify two terms, `a` and `b`, in a context `ctx`.
 */
pub fn unify(a: Rc<InferTerm>, b: Rc<InferTerm>, ctx: &InferCtx, substs: &mut Vec<Subst>) -> Result<(), UnifyErr> {
    debug!("Unification in progress... ({} & {})", a, b);
    // debug!("{}", ctx);

    let mut a = a;
    if let InferTerm::Subst{ref t, dbi, ref u} = *a.clone() {
        a = (*t).clone();
        subst_no_termination_chk(&mut a, dbi, u.clone());
        debug!("Substituted into {}.", a);
    }
    let a = a;

    let mut b = b;
    if let InferTerm::Subst{ref t, dbi, ref u} = *b.clone() {
        b = (*t).clone();
        subst_no_termination_chk(&mut b, dbi, u.clone());
        debug!("Substituted into {}.", b);
    }
    let b = b;

    if let InferTerm::Infer{..} = *b {
        if let InferTerm::Infer{..} = *a {}
        else { return unify(b, a, ctx, substs); }
    }

    match *a.clone() {
        InferTerm::Infer{id: ref id_a} => match *b {
            InferTerm::Infer{id: ref id_b} if id_a.get() == id_b.get() => (),
            _ => substs.push( Subst::new(id_a.clone(), b.clone()) ),
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
                unify_typed(s_a.clone(), s_b.clone(), ctx, substs).map_err( |e| UnifyErr::InApp(Box::new(e)) )?;
                unify_typed(t_a.clone(), t_b.clone(), ctx, substs).map_err( |e| UnifyErr::InApp(Box::new(e)) )?;
            },
            _ => return Err( UnifyErr::InApp(Box::new(UnifyErr::TermStructureMismatched)) ),
        }
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
        InferTerm::Let{..} => unimplemented!(),
        InferTerm::Case{..} => unimplemented!(),
        InferTerm::Value(ref v_a) => match *b {
            InferTerm::Value(ref v_b) =>
                if v_a == v_b {}
                else { return Err(UnifyErr::ValueMismatched(v_a.clone(), v_b.clone())) },
            _ => return Err(UnifyErr::TermStructureMismatched),
        },
        InferTerm::Subst{ref t, dbi, ref u} => unreachable!(),
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
    InApp(Box<UnifyErr>),
}

fn subst_no_termination_chk(t: &mut Rc<InferTerm>, dbi: usize, u: Rc<InferTerm>) {
    if let InferTerm::DBI(i) = *t.clone() {
        if i == dbi { *Rc::make_mut(t) = (*u).clone(); }
    }
    else if let InferTerm::Subst{t: ref m, dbi: dbi_, u: ref n} = *t.clone() {
        *Rc::make_mut(t) = (**m).clone();
        subst_no_termination_chk(t, dbi_, n.clone());
        subst_no_termination_chk(t, dbi, u);
    }
    else {
        match *Rc::make_mut(t) {
            InferTerm::App{s: ref mut m, t: ref mut n} => {
                subst_no_termination_chk(&mut m.tower[0], dbi, u.clone());
                subst_no_termination_chk(&mut n.tower[0], dbi, u);
            },
            InferTerm::Lam(ref mut abs) => subst_abs(abs, dbi, u),
            InferTerm::Pi(ref mut abs) => subst_abs(abs, dbi, u),
            InferTerm::Let{..} => unimplemented!(),
            InferTerm::Case{..} => unimplemented!(),
            _ => (),
        }
    }

    return;

    fn subst_abs(abs: &mut InferAbs, dbi: usize, u: Rc<InferTerm>) {
        subst_no_termination_chk(&mut abs.A.tower[0], dbi, u.clone());
        subst_no_termination_chk(&mut abs.t.tower[0], dbi+1, u);
    }
}

fn shift(t: &mut InferTerm, n: usize) {
    match t {
        InferTerm::DBI(ref mut i) => *i += n,
        InferTerm::App{ref mut s, ref mut t} => {
            shift_typed(s, n);
            shift_typed(t, n);
        },
        InferTerm::Lam(abs) => shift_abs(abs, n),
        InferTerm::Pi(abs) => shift_abs(abs, n),
        InferTerm::Let{..} => unimplemented!(),
        InferTerm::Case{..} => unimplemented!(),
        InferTerm::Subst{..} => unimplemented!(),
        _ => (),
    }

    return;

    fn shift_abs(abs: &mut InferAbs, n: usize) {
        shift_typed(&mut abs.A, n);
        shift_typed(&mut abs.t, n);
    }
}

fn shift_typed(t: &mut InferTypedTerm, n: usize) {
    shift(Rc::make_mut(&mut t.tower[0]), n);
    shift(Rc::make_mut(&mut t.tower[1]), n);
}