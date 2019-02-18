use super::{ConstId, HoleId, SpecialType};
use super::unification::*;
use super::explicit_subst::*;

use std::cell::Cell;
use std::collections::HashMap;
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

    let mut substs: Vec<Equal> = vec![];
    let mut defers: Vec<(Rc<Expr>, Rc<Expr>, InferCtx)> = vec![];
    let mut substs_map: HashMap<InferTermId, Rc<Expr>> = HashMap::new();
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
                    Equal::ToId(mut lhs, mut rhs) => {
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
                    Equal::Instantiate(id, instance) => {
                        if let Some(other) = substs_map.get(&id.get()).cloned() {
                            unify(instance, other, &ctx, &mut substs)?;
                        }
                        else {
                            substs_map.insert(id.get(), instance);
                        }
                    }
                    Equal::Defer(e0, e1, ctx) => defers.push((e0, e1, ctx)),
                }
            }
        }

        debug!("substitutions:");
        for (k,v) in &substs_map {
            debug!("\t?{} / {}", k, v);
        }
        debug!("deferred unifications:");
        for (e0,e1,ctx) in &defers {
            debug!("\t{} = {}", e0, e1);
        }
        debug!("current context:");
        debug!("{}\n", ctx);

        let subst_result = subst_infers(&mut ctx, &mut defers, &mut substs_map);

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

        for (e0, e1, ctx) in defers.split_off(0) {
            unify(e0, e1, &ctx, &mut substs)?;
        }
    }

    debug!("finished type checking.");
    debug!("current context:\n{}", ctx);

    Ok( cast_no_infer(ctx) )
}

fn subst_infers(
    ctx: &mut InferCtx,
    defers: &mut Vec<(Rc<Expr>, Rc<Expr>, InferCtx)>,
    substs_map: &mut HashMap<InferTermId, Rc<Expr>>
)
    -> SubstResult
{
    assert!(ctx.local.is_empty());

    let mut result = SubstResult{has_substed: false, found_infer: false};

    subst_infers_ctx(ctx, substs_map, &mut result);

    let found_infer = result.found_infer;

    for (e1, e2, ctx) in defers {
        subst_infers_term(e1, substs_map, &mut result);
        subst_infers_term(e2, substs_map, &mut result);
        subst_infers_ctx(ctx, substs_map, &mut result);
    }

    return SubstResult{found_infer, ..result};

    fn subst_infers_ctx(ctx: &mut InferCtx, substs: &mut Substs, result: &mut SubstResult) {
        for t in &mut ctx.local {
            subst_infers_typed_term(t, substs, result);
        }

        subst_infers_env(&mut ctx.consts, substs, result);

        for (t,T) in &mut ctx.typings {
            subst_infers_typed_term(t, substs, result);
            subst_infers_typed_term(T, substs, result);
        }
    }

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

    fn subst_infers_term(t: &mut Rc<Expr>, substs: &mut Substs, result: &mut SubstResult) {
        if let Expr::Infer{ref id} = *t.clone() {
            if let Some(instance) = substs.get(&id.get()) {
                *Rc::make_mut(t) = (**instance).clone();
                result.has_substed = true;
            }
            result.found_infer = true;
        }
        else {
            match *Rc::make_mut(t) {
                Expr::App{ref mut s, ref mut t} => {
                    subst_infers_typed_term(s, substs, result);
                    subst_infers_typed_term(t, substs, result);
                },
                Expr::Lam(ref mut abs) => subst_infers_abs(abs, substs, result),
                Expr::Pi(ref mut abs) => subst_infers_abs(abs, substs, result),
                Expr::Let{ref mut env, ref mut t} => {
                    subst_infers_env(env, substs, result);
                    subst_infers_typed_term(t, substs, result);
                },
                Expr::Case{ref mut t, ref mut cases, ..} => {
                    subst_infers_typed_term(t, substs, result);
                    for case in cases {
                        subst_infers_typed_term(case, substs, result);
                    }
                },
                Expr::Subst(ref mut s, ref mut e) => {
                    subst_infers_subst(s, substs, result);
                    subst_infers_term(e, substs, result);
                },
                _ => (),
            }
        }
    }

    fn subst_infers_abs(abs: &mut InferAbs, substs: &mut Substs, result: &mut SubstResult) {
        subst_infers_typed_term(&mut abs.A, substs, result);
        subst_infers_typed_term(&mut abs.t, substs, result);
    }

    fn subst_infers_subst(s: &mut Subst, substs: &mut Substs, result: &mut SubstResult) {
        match s {
            Subst::Dot(ref mut e, ref mut s) => {
                subst_infers_term(e, substs, result);
                subst_infers_subst(Rc::make_mut(s), substs, result);
            },
            Subst::Shift(..) => (),
        }
    }
    
    type Substs = HashMap<InferTermId, Rc<Expr>>;
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

    fn cast_no_infer_term(term: Rc<Expr>) -> Rc<Term> {
        Rc::new( match *term {
            Expr::Const(const_id) => Term::Const(const_id),
            Expr::DBI(i) => Term::DBI(i),
            Expr::Universe => Term::Universe,
            Expr::App{ref s, ref t} => Term::App {
                s: cast_no_infer_typed_term(s.clone()),
                t: cast_no_infer_typed_term(t.clone()),
            },
            Expr::Lam(ref abs) => Term::Lam(cast_no_infer_abs(abs.clone())),
            Expr::Pi(ref abs) => Term::Pi(cast_no_infer_abs(abs.clone())),
            Expr::Let{ref env, ref t} => Term::Let {
                env: cast_no_infer_env(env.clone()),
                t: cast_no_infer_typed_term(t.clone()),
            },
            Expr::Case{ref t, ref cases, ref datatype} => Term::Case {
                t: cast_no_infer_typed_term(t.clone()),
                cases: cases.iter().map(|t| cast_no_infer_typed_term(t.clone())).collect(),
            },
            Expr::Value(ref v) => Term::Value(v.clone()),
            Expr::Subst(ref s, ref e) => {
                let f = subst(s.clone(), e.clone());
                if let Expr::Subst(..) = *f {
                    unreachable!();
                }
                (*cast_no_infer_term(f)).clone()
            },
            Expr::Infer{..} => unreachable!(),
        } )
    }

    fn cast_no_infer_abs(abs: InferAbs) -> Abs {
        Abs{A: cast_no_infer_typed_term(abs.A), t: cast_no_infer_typed_term(abs.t)}
    }
}

fn typechk_ctx(ctx: &InferCtx, substs: &mut Vec<Equal>, next_inferterm_id: &mut InferTermId)
    -> Result<(), TypeChkErr>
{
    // checks W-Global-Def
    for (const_id, c) in ctx.consts.iter().enumerate() {
        typechk_const(ctx, c, const_id, substs, next_inferterm_id)?;
    }

    // checks W-Local-Assum
    for T in &ctx.local {
        unify(T.tower[1].clone(), Rc::new(Expr::Universe), ctx, substs)?;
        typechk_term(ctx, T, substs, next_inferterm_id)?;
    }

    // checks W-Global-Assum
    for (t,T) in &ctx.typings {
        typechk_term(ctx, t, substs, next_inferterm_id)?;
        typechk_term(ctx, T, substs, next_inferterm_id)?;

        unify(t.tower[1].clone(), T.tower[0].clone(), ctx, substs)?;
        unify(T.tower[1].clone(), Rc::new(Expr::Universe), ctx, substs)?;
    }

    Ok(())
}

fn typechk_const (
    ctx: &InferCtx,
    c: &InferTypedConst, id: ConstId,
    substs: &mut Vec<Equal>,
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

            let universe = Rc::new(Expr::Universe);
            let type_ = param_types.iter().rev().fold( universe.clone(),
                |U, param_type| Rc::new( Expr::Pi( InferAbs {
                    A: param_type.clone(),
                    t: InferTypedTerm{tower: vec![U, universe.clone()]},
                } ) )
            );
            unify(c.type_.tower[0].clone(), type_, ctx, substs)?;
        },
        InferConst::Ctor{datatype, ref param_types} => { 
            let datatype_param_types =
                if let InferConst::DataType{ref param_types, ..} = ctx.consts[datatype].c { param_types }
                else { unreachable!() };

            /* let mut local_ctx = ctx.clone();
            local_ctx.local.extend(datatype_param_types.iter().rev().cloned());

            for param_type in param_types {
                typechk_term(&local_ctx, param_type, substs, next_inferterm_id)?;
            } */

            let universe = Rc::new(Expr::Universe);
            
            let type_ =
                datatype_param_types.iter().chain(param_types).rev().fold(
                    (0..datatype_param_types.len()).rev().fold( Rc::new(Expr::Const(datatype)),
                        |f, dbi_offset| Rc::new( Expr::App {
                            s: InferTypedTerm{tower: vec![f, Rc::new(new_inferterm(next_inferterm_id))]}, 
                            t: InferTypedTerm { tower: vec![
                                Rc::new(Expr::DBI(param_types.len() + dbi_offset)),
                                Rc::new(new_inferterm(next_inferterm_id)),
                            ] },
                        })
                    ),
                    |tail, param_type| Rc::new( Expr::Pi( InferAbs {
                        A: param_type.clone(),
                        t: InferTypedTerm{tower: vec![tail, universe.clone()]},
                    } ) )
                );
            
            unify(c.type_.tower[0].clone(), type_, ctx, substs)?;
        },
    }

    typechk_term(ctx, &c.type_, substs, next_inferterm_id)?;

    Ok(())
}

fn typechk_term(ctx: &InferCtx, term: &InferTypedTerm, substs: &mut Vec<Equal>, next_inferterm_id: &mut InferTermId)
    -> Result<(), TypeChkErr>
{
    debug!("Checks {} ...", term);
    // debug!("{}", ctx);

    match *term.tower[0] {
        Expr::Const(const_id) =>
            unify(term.tower[1].clone(), ctx.consts[const_id].type_.tower[0].clone(), ctx, substs)?,
        Expr::DBI(i) => unify(term.tower[1].clone(), ctx.local(i).tower[0].clone(), ctx, substs)?,
        Expr::Universe =>
            unify(term.tower[1].clone(), term.tower[0].clone(), ctx, substs)?,
        Expr::App{s: ref t, t: ref u} => {
            typechk_term(ctx, t, substs, next_inferterm_id)?;
            typechk_term(ctx, u, substs, next_inferterm_id)?;
            
            let T = Rc::new(new_inferterm(next_inferterm_id));

            unify( t.tower[1].clone(),
                Rc::new( Expr::Pi( InferAbs {
                    A: InferTypedTerm{tower: vec![ u.tower[1].clone(), Rc::new(Expr::Universe) ]},
                    t: InferTypedTerm{tower: vec![ T.clone(), Rc::new(Expr::Universe) ]},
                } ) ),
                ctx, substs )?;
            
            let type_ = Rc::new( Expr::Subst(
                Subst::from_expr(u.tower[0].clone()),
                T.clone(),
            ) );
            unify(term.tower[1].clone(), type_, ctx, substs)?;
        },
        Expr::Lam(InferAbs{A: ref T, ref t}) => {
            let mut local_ctx = ctx.clone();
            local_ctx.local.push( subst_typed_lazily(Subst::Shift(1), T.clone()) );

            typechk_term(ctx, T, substs, next_inferterm_id)?;
            typechk_term(&local_ctx, t, substs, next_inferterm_id)?;

            let U = Rc::new(new_inferterm(next_inferterm_id));

            unify(t.tower[1].clone(), U.clone(), &local_ctx, substs)?;

            let type_ = Rc::new( Expr::Pi( InferAbs {
                A: T.clone(),
                t: InferTypedTerm{tower: vec![U, Rc::new(Expr::Universe)]},
            } ) );
            unify(term.tower[1].clone(), type_, ctx, substs)?;
        },
        Expr::Pi(InferAbs{A: ref T, t: ref U}) => {
            let mut local_ctx = ctx.clone();
            local_ctx.local.push( subst_typed_lazily(Subst::Shift(1), T.clone()) );

            typechk_term(ctx, T, substs, next_inferterm_id)?;
            typechk_term(&local_ctx, U, substs, next_inferterm_id)?;

            let universe = Rc::new(Expr::Universe);

            unify(T.tower[1].clone(), universe.clone(), ctx, substs)?;
            unify(U.tower[1].clone(), universe.clone(), &local_ctx, substs)?;
            unify(term.tower[1].clone(), universe, ctx, substs)?;
        },
        Expr::Let{ref env, ref t} => {
            let mut local_ctx = ctx.clone();
            local_ctx.consts.extend(env.iter().cloned());

            let base_const_id = ctx.consts.len();
            for (offset, c) in env.iter().enumerate() {
                typechk_const(ctx, c, base_const_id + offset, substs, next_inferterm_id)?;
            }

            typechk_term(&local_ctx, t, substs, next_inferterm_id)?;

            unify(term.tower[1].clone(), t.tower[1].clone(), ctx, substs)?;
        },
        Expr::Case{ref t, ref cases, ref datatype} => {
            typechk_term(ctx, t, substs, next_inferterm_id)?;
            for case in cases {
                typechk_term(ctx, case, substs, next_inferterm_id)?;
            }

            if let Some(datatype) = datatype {
                unify(t.tower[1].clone(), Rc::new(Expr::Const(*datatype)), ctx, substs)?;

                let types_of_cases: Vec<Rc<Expr>> = cases.iter().enumerate().map( |(ctor_no, case)| {
                    let type_ = Rc::new(new_inferterm(next_inferterm_id));

                    let ctors =
                        if let InferConst::DataType{ref ctors, ..} = ctx.consts[*datatype].c { ctors }
                        else { unreachable!() };
                    
                    let type_of_ctor = ctx.consts[ctors[ctor_no]].type_.tower[0].clone();
                    unify(case.tower[1].clone(), type_of_ctor, ctx, substs)?;

                    Ok(type_)
                } ).collect::<Result<_, UnifyErr>>()?;

                let universe = Rc::new(Expr::Universe);

                let type_ = Rc::new( Expr::Case {
                    t: t.clone(),
                    cases:
                        types_of_cases.into_iter()
                            .map( |T| InferTypedTerm{tower: vec![T, universe.clone()]} ).collect(),
                    datatype: Some(*datatype),
                } );

                unify(term.tower[1].clone(), type_, ctx, substs)?;
            }
        },
        Expr::Value(ref v) =>
            unify(term.tower[1].clone(), match *v {
                Value::Nat(..) => unimplemented!(),
                Value::Int(..) => unimplemented!(),
                Value::Str(..) => unimplemented!(),
            }, ctx, substs)?,
        Expr::Infer{..} => (),
        Expr::Subst(..) => unreachable!(),
    }

    Ok(())
}

fn typechk_typing(ctx: &InferCtx, t: InferTypedTerm, T: InferTypedTerm, substs: &mut Vec<Equal>)
    -> Result<(), TypeChkErr>
{
    unify(t.tower[1].clone(), T.tower[0].clone(), ctx, substs)?;
    unify(T.tower[1].clone(), Rc::new(Expr::Universe), ctx, substs)?;
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
        type_: InferTypedTerm{tower: vec![Rc::new(new_inferterm(inferterm_id)), Rc::new(Expr::Universe)]},
    };

    itc
}

fn assign_term(term: Rc<HoledTerm>, inferterm_id: &mut InferTermId) -> InferTypedTerm {
    let itt = InferTypedTerm {
        tower: vec![
            Rc::new( match *term {
                HoledTerm::Const(ref id) => Expr::Const(*id),
                HoledTerm::DBI(ref i) => Expr::DBI(*i as usize),
                HoledTerm::Universe => Expr::Universe,
                HoledTerm::App{ref s, ref t} =>
                    Expr::App{s: assign_term(s.clone(), inferterm_id), t: assign_term(t.clone(), inferterm_id)},
                HoledTerm::Lam(ref abs) => Expr::Lam(assign_abs(abs.clone(), inferterm_id)),
                HoledTerm::Pi(ref abs) => Expr::Pi(assign_abs(abs.clone(), inferterm_id)),
                HoledTerm::Let{ref env, ref t} => {
                    assert!(env.typings.is_empty());
                    assert_eq!(env.nof_named_hole, 0);

                    Expr::Let {
                        env: assign_consts(env.consts.clone(), inferterm_id),
                        t: assign_term(t.clone(), inferterm_id)
                    }
                }
                HoledTerm::Case{ref t, ref cases, ref datatype} =>
                    Expr::Case{
                        t: assign_term(t.clone(), inferterm_id),
                        cases: cases.iter().map(|case| assign_term(case.clone(), inferterm_id)).collect(),
                        datatype: *datatype,
                    },
                HoledTerm::Value(ref val) => Expr::Value(val.clone()),
                HoledTerm::Hole(ref hole_id) =>
                    if let Some(id) = *hole_id {
                        Expr::Infer{id: Rc::new(Cell::new(id))}
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

fn new_inferterm(next_inferterm_id: &mut InferTermId) -> Expr {
    let id = Rc::new(Cell::new(*next_inferterm_id));
    *next_inferterm_id += 1;
    Expr::Infer{id}
}

fn assign_abs(abs: HoledAbs, inferterm_id: &mut InferTermId) -> InferAbs {
    InferAbs{A: assign_term(abs.A, inferterm_id), t: assign_term(abs.t, inferterm_id)}
}

#[derive(Clone, Debug)]
pub(super) enum Expr {
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
    Subst(Subst, Rc<Expr>),
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
    pub(super) tower: Vec<Rc<Expr>>,
}

type InferTermId = usize;

#[derive(Clone, Debug)]
pub(super) enum Equal {
    ToId(Rc<Cell<InferTermId>>, Rc<Cell<InferTermId>>),
    Instantiate(Rc<Cell<InferTermId>>, Rc<Expr>),
    Defer(Rc<Expr>, Rc<Expr>, InferCtx),
}
impl Equal {
    pub(super) fn sort(lhs: Rc<Cell<InferTermId>>, rhs: Rc<Expr>) -> Self {
        if let Expr::Infer{ref id} = *rhs.clone() { Equal::ToId(lhs, id.clone()) }
        else { Equal::Instantiate(lhs, rhs) }
    }
}