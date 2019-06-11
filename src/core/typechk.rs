use super::{ConstId, HoleId};
use super::unification::*;
use super::explicit_subst::*;

use syntax::Loc;

use std::cell::Cell;
use std::collections::HashMap;
use std::rc::Rc;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HoledTerm {
    Const(ConstId),
    DBI(u64),
    Universe,
    App{s: (Rc<HoledTerm>, Loc), t: (Rc<HoledTerm>, Loc), implicity: u8},
    Lam(HoledAbs, u8),
    Pi(HoledAbs, u8),
    Let{env: HoledEnv, t: (Rc<HoledTerm>, Loc)},
    Case{t: (Rc<HoledTerm>, Loc), cases: Vec<(Rc<HoledTerm>, Loc)>, datatype: Option<ConstId>},
    Hole(Option<HoleId>),
    Value(Value),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HoledAbs {
    pub A: (Rc<HoledTerm>, Loc),
    pub t: (Rc<HoledTerm>, Loc),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HoledEnv {
    pub consts: Vec<(HoledConst, Loc)>,
    pub typings: Vec<((Rc<HoledTerm>, Loc), (Rc<HoledTerm>, Loc))>,
    pub nof_named_hole: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HoledConst {
    Def{rhs: (Rc<HoledTerm>, Loc), type_: (Rc<HoledTerm>, Loc)},
    DataType{param_types: Vec<((Rc<HoledTerm>, Loc), u8)>, type_: (Rc<HoledTerm>, Loc), ctors: Vec<ConstId>},
    Ctor{datatype: ConstId, type_: (Rc<HoledTerm>, Loc)},
}

#[derive(Serialize, Deserialize, Clone, Debug)]
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

#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct Abs {
    pub A: TypedTerm,
    pub t: TypedTerm,
}

#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct TypedTerm {
    tower: Vec<(Rc<Term>, Loc)>,
}

type Env = Vec<TypedConst>;

#[derive(Serialize, Deserialize, Clone, Debug)]
pub enum Const {
    Def((Rc<Term>, Loc)),
    DataType{param_types: Vec<((Rc<Term>, Loc), u8)>, type_: (Rc<Term>, Loc)},
    Ctor{datatype: ConstId},
}

#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct TypedConst {
    c: Const,
    type_: (Rc<Term>, Loc),
    loc: Loc,
}

#[derive(Serialize, Deserialize, Clone, Debug)]
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
    let mut defers: Vec<((Rc<Expr>, Loc), (Rc<Expr>, Loc))> = vec![];
    let mut substs_map: HashMap<InferTermId, (Rc<Expr>, Loc)> = HashMap::new();
    for count in 0.. {
        debug!("iteration {}.", count);
        debug!("current context: {}", ctx);

        typechk_ctx(&mut ctx, &mut substs, &mut next_inferterm_id)?;

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

                        if let Some(mut instance) = substs_map.remove(&lhs.get()) {
                            if let Some(other) = substs_map.get(&rhs.get()).cloned() {
                                // unify(instance.clone(), other.clone(), &ctx, &mut next_inferterm_id, &mut substs)?;
                                instance = (Rc::new(Expr::Equal(instance, other)), None)
                            }
                            substs_map.insert(rhs.get(), instance);
                        }
                        lhs.set(rhs.get());
                    },
                    Equal::Instantiate(id, mut instance) => {
                        if let Some(other) = substs_map.get(&id.get()).cloned() {
                            // unify(instance, other, &ctx, &mut next_inferterm_id, &mut substs)?;
                            instance = (Rc::new(Expr::Equal(instance, other)), None);
                        }
                        substs_map.insert(id.get(), instance);
                    },
                    Equal::Defer(e0, e1) => defers.push((e0, e1)),
                }
            }
        }

        debug!("substitutions:");
        for (k,v) in &substs_map {
            debug!("\t?{} / {}", k, v.0);
        }
        debug!("deferred unifications:");
        for (e0,e1) in &defers {
            debug!("\t{} = {}", e0.0, e1.0);
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

        for (e0, e1) in defers.split_off(0) {
            unify(e0, e1, &mut next_inferterm_id, &mut substs)?;
        }
    }

    debug!("finished type checking.");
    debug!("current context:\n{}", ctx);

    Ok( cast_no_infer(ctx) )
}

fn subst_infers(
    ctx: &mut InferCtx,
    defers: &mut Vec<((Rc<Expr>, Loc), (Rc<Expr>, Loc))>,
    substs_map: &mut HashMap<InferTermId, (Rc<Expr>, Loc)>
)
    -> SubstResult
{
    assert!(ctx.local.is_empty());

    let mut result = SubstResult{has_substed: false, found_infer: false};

    subst_infers_ctx(ctx, substs_map, &mut result);

    let found_infer = result.found_infer;

    for (e1, e2) in defers {
        subst_infers_term(e1, substs_map, &mut result);
        subst_infers_term(e2, substs_map, &mut result);
    }

    return SubstResult{found_infer, ..result};

    fn subst_infers_ctx(ctx: &mut InferCtx, substs: &mut Substs, result: &mut SubstResult) {
        for t in &mut ctx.local {
            subst_infers_typed_term(t, substs, result);
        }

        subst_infers_env(&mut ctx.consts, substs, result);

        for (t, T) in &mut ctx.typings {
            subst_infers_typed_term(t, substs, result);
            subst_infers_typed_term(T, substs, result);
        }
    }

    fn subst_infers_env(env: &mut InferEnv, substs: &mut Substs, result: &mut SubstResult) {
        for c in env {
            match c.c {
                InferConst::Def(ref mut t) =>
                    subst_infers_term(t, substs, result),
                InferConst::DataType{ref mut param_types, ref mut type_, ctors: _} => {
                    for param_type in param_types {
                        subst_infers_term(&mut param_type.0, substs, result);
                    }
                    subst_infers_term(type_, substs, result);
                },
                InferConst::Ctor{..} => (),
            }
            subst_infers_term(&mut c.type_, substs, result);
        }
    }

    fn subst_infers_typed_term(t: &mut InferTypedTerm, substs: &mut Substs, result: &mut SubstResult) {
        for term in &mut t.tower {
            subst_infers_term(term, substs, result);
        }
    }

    fn subst_infers_term(t: &mut (Rc<Expr>, Loc), substs: &mut Substs, result: &mut SubstResult) {
        if let Expr::Infer{ref id} = *t.0.clone() {
            if let Some(instance) = substs.get(&id.get()) {
                *Rc::make_mut(&mut t.0) = (*(instance.0)).clone();
                t.1 = instance.1.clone();
                result.has_substed = true;
            }
            result.found_infer = true;
        }
        else {
            match *Rc::make_mut(&mut t.0) {
                Expr::App{ref mut s, ref mut t, ..} => {
                    subst_infers_typed_term(s, substs, result);
                    subst_infers_typed_term(t, substs, result);
                },
                Expr::Lam(ref mut abs, _implicity) => subst_infers_abs(abs, substs, result),
                Expr::Pi(ref mut abs, _implicity) => subst_infers_abs(abs, substs, result),
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
    
    type Substs = HashMap<InferTermId, (Rc<Expr>, Loc)>;
}
pub struct SubstResult {
    has_substed: bool,
    found_infer: bool,
}

fn cast_no_infer(ctx: InferCtx) -> Env {
    assert!(ctx.local.is_empty());

    ctx.typings.into_iter().for_each( |(t, T)| {
        cast_no_infer_typed_term(t);
        cast_no_infer_typed_term(T);
    } );

    return cast_no_infer_env(ctx.consts);

    fn cast_no_infer_env(env: InferEnv) -> Env {
        env.into_iter().map( |c| TypedConst {
            c: match c.c {
                InferConst::Def((t, loc)) => Const::Def((cast_no_infer_term(t), loc)),
                InferConst::DataType{param_types, type_, ..} => Const::DataType {
                    param_types:
                        param_types.into_iter().map(|(T,i)| ((cast_no_infer_term(T.0), T.1), i)).collect(),
                    type_:
                        (cast_no_infer_term(type_.0), type_.1),
                },
                InferConst::Ctor{datatype} => Const::Ctor{datatype},
            },
            type_: (cast_no_infer_term(c.type_.0), c.type_.1),
            loc: c.loc,
        } ).collect()
    }

    fn cast_no_infer_typed_term(term: InferTypedTerm) -> TypedTerm {
        TypedTerm{tower: term.tower.into_iter().map( |t| (cast_no_infer_term(t.0), t.1) ).collect()}
    }

    fn cast_no_infer_term(term: Rc<Expr>) -> Rc<Term> {
        Rc::new( match *term {
            Expr::Const(const_id) => Term::Const(const_id),
            Expr::DBI(i) => Term::DBI(i),
            Expr::Universe => Term::Universe,
            Expr::App{ref s, ref t, ..} => Term::App {
                s: cast_no_infer_typed_term(s.clone()),
                t: cast_no_infer_typed_term(t.clone()),
            },
            Expr::Lam(ref abs, _implicity) => Term::Lam(cast_no_infer_abs(abs.clone())),
            Expr::Pi(ref abs, _implicity) => Term::Pi(cast_no_infer_abs(abs.clone())),
            Expr::Let{ref env, ref t} => Term::Let {
                env: cast_no_infer_env(env.clone()),
                t: cast_no_infer_typed_term(t.clone()),
            },
            Expr::Case{ref t, ref cases, datatype: _} => Term::Case {
                t: cast_no_infer_typed_term(t.clone()),
                cases: cases.iter().map(|t| cast_no_infer_typed_term(t.clone())).collect(),
            },
            Expr::Value(ref v) => Term::Value(v.clone()),
            Expr::Subst(ref s, ref e) => {
                let f = subst(s.clone(), e.clone());
                if let Expr::Subst(..) = *f.0 {
                    unreachable!();
                }
                (*cast_no_infer_term(f.0)).clone()
            },
            Expr::Infer{..} => unreachable!(),
            Expr::Equal(..) => unreachable!(),
        } )
    }

    fn cast_no_infer_abs(abs: InferAbs) -> Abs {
        Abs{A: cast_no_infer_typed_term(abs.A), t: cast_no_infer_typed_term(abs.t)}
    }
}

fn typechk_ctx(ctx: &mut InferCtx, substs: &mut Vec<Equal>, next_inferterm_id: &mut InferTermId)
    -> Result<(), TypeChkErr>
{
    // checks W-Global-Def
    for i in 0..ctx.consts.len() {
        let new_const = typechk_const(ctx, &ctx.consts[i], substs, next_inferterm_id)?;
        if let Some(new_const) = new_const {
            ctx.consts[i] = new_const;
        }
    }

    // checks W-Local-Assum
    for i in 0..ctx.local.len() {
        let T = ctx.local[i].clone();
        let (term, type_) = (T.tower[0].clone(), T.tower[1].clone());
        unify(type_.clone(), (Rc::new(Expr::Universe), None), next_inferterm_id, substs)?;
        let (new_term, new_type) =
            typechk_term_supported_implicity(ctx, term, type_, substs, next_inferterm_id, true)?;
        if let Some(new_term) = new_term { ctx.local[i].tower[0] = new_term; }
        if let Some(new_type) = new_type { ctx.local[i].tower[1] = new_type; }
    }

    // checks W-Global-Assum
    for i in 0..ctx.typings.len() {
        let (mut t, mut T) = ctx.typings[i].clone();

        let (new_term, new_type) =
            typechk_term_supported_implicity(ctx, t.tower[0].clone(), t.tower[1].clone(),
                substs, next_inferterm_id, true)?;
        if let Some(new_term) = new_term { t.tower[0] = new_term; }
        if let Some(new_type) = new_type { t.tower[1] = new_type; }

        let (new_term, new_type) =
            typechk_term_supported_implicity(ctx, T.tower[0].clone(), T.tower[1].clone(),
                substs, next_inferterm_id, true)?;
        if let Some(new_term) = new_term { T.tower[0] = new_term; }
        if let Some(new_type) = new_type { T.tower[1] = new_type; }

        let (new_type, iparams) =
            unify_supported_implicity(T.tower[1].clone(), (Rc::new(Expr::Universe), None),
                next_inferterm_id, substs, true)?;
        if let Some(new_type) = new_type { T.tower[1] = new_type; }
        if !iparams.is_empty() {
            T.tower[0] = insert_implicit_args(T.tower[0].clone(), iparams.clone(), next_inferterm_id);
            t.tower[1] = insert_implicit_args(t.tower[1].clone(), iparams, next_inferterm_id);
        }

        let (new_type, iparams) =
            unify_supported_implicity(t.tower[1].clone(), T.tower[0].clone(), next_inferterm_id, substs, true)?;
        if let Some(new_type) = new_type {
            T.tower[0] = new_type.clone();
            t.tower[1] = new_type;
        }
        if !iparams.is_empty() {
            t.tower[0] = insert_implicit_args(t.tower[0].clone(), iparams, next_inferterm_id);
        }

        ctx.typings[i] = (t,T);
    }

    Ok(())
}

fn typechk_const (
    ctx: &InferCtx,
    c: &InferTypedConst,
    substs: &mut Vec<Equal>,
    next_inferterm_id: &mut InferTermId
)
    -> Result<Option<InferTypedConst>, TypeChkErr>
{
    match c.c {
        InferConst::Def(ref t) => {
            let (new_term, new_type) =
                typechk_term_supported_implicity(ctx, t.clone(), c.type_.clone(),
                    substs, next_inferterm_id, true)?;

            if new_term.is_some() || new_type.is_some() {
                Ok(Some( InferTypedConst {
                    c: InferConst::Def(new_term.unwrap_or(t.clone())),
                    type_: new_type.unwrap_or(c.type_.clone()),
                    ..c.clone()
                } ))
            }
            else { Ok(None) }
        },
        InferConst::DataType{ref param_types, ref type_, ref ctors} => {
            let univ1 = (Rc::new(Expr::Universe), None);

            for (idx, (param_type, i)) in param_types.iter().enumerate() {
                let (new_term, new_type) = typechk_term_supported_implicity(ctx, param_type.clone(), univ1.clone(),
                    substs, next_inferterm_id, true)?;

                assert!(new_type.is_none());
                
                if let Some(new) = new_term {
                    let mut new_param_types = param_types.clone();
                    new_param_types[idx] = (new, *i);

                    return Ok(Some( InferTypedConst {
                        c: InferConst::DataType {
                            param_types: new_param_types,
                            type_: type_.clone(),
                            ctors: ctors.clone(),
                        },
                        ..c.clone()
                    } ));
                }
            }

            let (new_term, new_type) = typechk_term_supported_implicity(ctx,
                type_.clone(), (Rc::new(Expr::Universe), None), substs, next_inferterm_id, true)?;

            assert!(new_type.is_none());

            Ok(new_term.map( |new|
                InferTypedConst {
                    c: InferConst::DataType {
                        type_: new,
                        param_types: param_types.clone(),
                        ctors: ctors.clone(),
                    },
                    ..c.clone()
                }
            ))
        },
        InferConst::Ctor{..} => {
            let (new_term, new_type) = typechk_term_supported_implicity(ctx,
                c.type_.clone(), (Rc::new(Expr::Universe), None), substs, next_inferterm_id, true)?;
            
            // assert!(new_type.is_none());
            if let Some(new_type) = new_type {
                debug!("new_type = {}", new_type.0);
            }

            Ok(new_term.map( |new| InferTypedConst{type_: new, ..c.clone()} ))
        },
    }
}

fn typechk_term(ctx: &InferCtx, term: &InferTypedTerm, substs: &mut Vec<Equal>, next_inferterm_id: &mut InferTermId)
    -> Result<(), TypeChkErr>
{
    let term_ = term.tower[0].clone();
    let type_ = term.tower[1].clone();
    let (new_term, new_type) = typechk_term_supported_implicity(ctx, term_, type_, substs, next_inferterm_id, false)?;
    assert!(new_term.is_none());
    assert!(new_type.is_none());
    Ok(())
}

fn typechk_term_supported_implicity(
    ctx: &InferCtx,
    term: (Rc<Expr>, Loc),
    type_: (Rc<Expr>, Loc),
    substs: &mut Vec<Equal>,
    next_inferterm_id: &mut InferTermId,
    enable_implicit: bool,
)
    -> Result<(Option<(Rc<Expr>, Loc)>, Option<(Rc<Expr>, Loc)>), TypeChkErr>
{
    let unify_supported_implicity_local =
        |   a: (Rc<Expr>, Loc), b: (Rc<Expr>, Loc), for_term: bool,
            term, next_inferterm_id: &mut InferTermId, substs: &mut Vec<Equal>  |
    {
        let (new_higher, iparams) = unify_supported_implicity(a, b, next_inferterm_id, substs, enable_implicit)?;

        let new_lower =
            if iparams.is_empty() { None }
            else { Some(insert_implicit_args(term, iparams, next_inferterm_id)) };

        if for_term {
            assert!(new_lower.is_none());
            Ok((new_higher, None))
        }
        else {
            Ok((new_lower, new_higher))
        }
    };

    debug!("Checks {} ...", InferTypedTerm{tower: vec![term.clone(), type_.clone()]});
    // debug!("{}", ctx);

    let univ = (Rc::new(Expr::Universe), None);

    /* if !ignore_type {
        let (new_type1, new_type2) =
            typechk_term_supported_implicity_body(ctx, type_.clone(), univ.clone(),
                substs, next_inferterm_id, enable_implicit, true)?;

        if let Some(new_type2) = new_type2 {
            debug!("new_type2 = {}", new_type2.0);
        }

        if let Some(new_type1) = new_type1 {
            return Ok( (Some(term), Some(new_type1)) );
        }
    } */

    {
        let (new_term, new_type) = unify_equals_typed(term.clone(), type_.clone(), next_inferterm_id, substs)?;

        if new_term.is_some() || new_type.is_some() {
            return Ok( (new_term, new_type) );
        }
    }

    match (*term.0).clone() {
        Expr::Const(const_id) =>
            return unify_supported_implicity_local(
                type_.clone(), ctx.consts[const_id].type_.clone(), false,
                term, next_inferterm_id, substs,
            ),
        Expr::DBI(i) =>
            return unify_supported_implicity_local(
                type_.clone(), ctx.local(i).tower[0].clone(), false,
                term, next_inferterm_id, substs,
            ),
        Expr::Universe =>
            return unify_supported_implicity_local(
                type_.clone(), (Rc::new(Expr::Universe), None), false,
                term, next_inferterm_id, substs,
            ),
        Expr::App{s: ref t, t: ref u, implicity} => {
            let new_tt_from_t = |tt, next_inferterm_id: &mut InferTermId| {
                new_tt(tt, next_inferterm_id, t,
                    |new_t_term, new_t_type|
                        Expr::App {
                            s: InferTypedTerm{tower: vec![ new_t_term, new_t_type ]},
                            t: u.clone(),
                            implicity,
                        },
                    &term,
                )
            };
            let new_tt_from_u = |tt, next_inferterm_id: &mut InferTermId| {
                new_tt(tt, next_inferterm_id, u,
                    |new_u_term, new_u_type|
                        Expr::App {
                            s: t.clone(),
                            t: InferTypedTerm{tower: vec![ new_u_term, new_u_type ]},
                            implicity,
                        },
                    &term,
                )
            };

            if let Some(tt) = new_tt_from_t(
                typechk_term_supported_implicity(ctx, t.tower[0].clone(), t.tower[1].clone(),
                    substs, next_inferterm_id, enable_implicit)?,
                next_inferterm_id,
            ) {
                return Ok(tt);
            }

            if let Some(tt) = new_tt_from_u(
                typechk_term_supported_implicity(ctx, u.tower[0].clone(), u.tower[1].clone(),
                    substs, next_inferterm_id, enable_implicit)?,
                next_inferterm_id,
            ) {
                return Ok(tt);
            }
            
            let T = (Rc::new(new_inferterm(next_inferterm_id)), None);

            if let Some(tt) = new_tt_from_t(
                unify_supported_implicity_local(
                    t.tower[1].clone(),
                    (Rc::new( Expr::Pi( InferAbs {
                        A: InferTypedTerm{tower: vec![ u.tower[1].clone(), univ.clone() ]},
                        t: InferTypedTerm{tower: vec![ T.clone(), univ ]},
                    }, implicity ) ), None),
                    false,
                    t.tower[0].clone(), next_inferterm_id, substs,
                )?,
                next_inferterm_id,
            ) {
                return Ok(tt);
            }

            let type__ = Rc::new( Expr::Subst(
                Subst::from_expr(u.tower[0].clone()),
                T.clone(),
            ) );

            return Ok( unify_supported_implicity_local(
                type_.clone(), (type__, None), false,
                term.clone(), next_inferterm_id, substs
            )? );
        },
        Expr::Lam(InferAbs{A: ref T, ref t}, implicity) => {
            let new_tt_from_T = |tt, next_inferterm_id: &mut InferTermId| {
                new_tt(tt, next_inferterm_id, T,
                    |new_T_term, new_T_type|
                        Expr::Lam( InferAbs {
                                A: InferTypedTerm{tower: vec![ new_T_term, new_T_type ]},
                                t: t.clone(),
                            },
                            implicity
                        ),
                    &term,
                )
            };
            let new_tt_from_t = |tt, next_inferterm_id: &mut InferTermId| {
                new_tt(tt, next_inferterm_id, t,
                    |new_t_term, new_t_type|
                        Expr::Lam( InferAbs {
                                A: T.clone(),
                                t: InferTypedTerm{tower: vec![ new_t_term, new_t_type ]},
                            },
                            implicity
                        ),
                    &term,
                )
            };

            let mut local_ctx = ctx.clone();
            local_ctx.local.push( subst_typed_lazily(Subst::Shift(1), T.clone()) );

            if let Some(tt) = new_tt_from_T(
                typechk_term_supported_implicity(
                    ctx, T.tower[0].clone(), T.tower[1].clone(),
                    substs, next_inferterm_id, enable_implicit,
                )?,
                next_inferterm_id,
            ) {
                return Ok(tt);
            }
            
            if let Some(tt) = new_tt_from_t(
                typechk_term_supported_implicity(
                    &local_ctx, t.tower[0].clone(), t.tower[1].clone(),
                    substs, next_inferterm_id, enable_implicit,
                )?,
                next_inferterm_id,
            ) {
                return Ok(tt);
            }

            let U = (Rc::new(new_inferterm(next_inferterm_id)), None);

            if let Some(tt) = new_tt_from_t(
                unify_supported_implicity_local(
                    t.tower[1].clone(), U.clone(), false,
                    t.tower[0].clone(), next_inferterm_id, substs,
                )?,
                next_inferterm_id,
            ) {
                return Ok(tt);
            }

            let type__ = Rc::new( Expr::Pi( InferAbs {
                A: T.clone(),
                t: InferTypedTerm{tower: vec![U, (Rc::new(Expr::Universe), None)]},
            }, implicity ) );

            return Ok( unify_supported_implicity_local(
                type_.clone(), (type__, None), false,
                term.clone(), next_inferterm_id, substs
            )? );
        },
        Expr::Pi(InferAbs{A: ref T, t: ref U}, implicity) => {
            let new_tt_from_T = |tt, next_inferterm_id: &mut InferTermId| {
                new_tt(tt, next_inferterm_id, T,
                    |new_T_term, new_T_type|
                        Expr::Pi( InferAbs {
                                A: InferTypedTerm{tower: vec![ new_T_term, new_T_type ]},
                                t: U.clone(),
                            },
                            implicity
                        ),
                    &term,
                )
            };
            let new_tt_from_U = |tt, next_inferterm_id: &mut InferTermId| {
                new_tt(tt, next_inferterm_id, U,
                    |new_U_term, new_U_type|
                        Expr::Pi( InferAbs {
                                A: T.clone(),
                                t: InferTypedTerm{tower: vec![ new_U_term, new_U_type ]},
                            },
                            implicity
                        ),
                    &term,
                )
            };

            let mut local_ctx = ctx.clone();
            local_ctx.local.push( subst_typed_lazily(Subst::Shift(1), T.clone()) );

            if let Some(tt) = new_tt_from_T(
                typechk_term_supported_implicity(
                    ctx, T.tower[0].clone(), T.tower[1].clone(),
                    substs, next_inferterm_id, enable_implicit,
                )?,
                next_inferterm_id,
            ) {
                return Ok(tt);
            }

            if let Some(tt) = new_tt_from_U(
                typechk_term_supported_implicity(
                    &local_ctx, U.tower[0].clone(), U.tower[1].clone(),
                    substs, next_inferterm_id, enable_implicit,
                )?,
                next_inferterm_id,
            ) {
                return Ok(tt);
            }

            if let Some(tt) = new_tt_from_T(
                unify_supported_implicity_local(
                    T.tower[1].clone(), univ.clone(), false,
                    T.tower[0].clone(), next_inferterm_id, substs,
                )?,
                next_inferterm_id,
            ) {
                return Ok(tt);
            }

            if let Some(tt) = new_tt_from_U(
                unify_supported_implicity_local(
                    U.tower[1].clone(), univ.clone(), false,
                    U.tower[0].clone(), next_inferterm_id, substs,
                )?,
                next_inferterm_id,
            ) {
                return Ok(tt);
            }

            return Ok( unify_supported_implicity_local(
                type_.clone(), univ, false,
                term.clone(), next_inferterm_id, substs,
            )? );
        },
        Expr::Let{ref env, ref t} => {
            let mut local_ctx = ctx.clone();
            local_ctx.consts.extend(env.iter().cloned());

            for (i, c) in env.iter().enumerate() {
                if let Some(itc) = typechk_const(ctx, c, substs, next_inferterm_id)? {
                    let mut new_env = env.clone();
                    new_env[i] = itc;

                    return Ok((
                        Some(( Rc::new(Expr::Let{env: new_env, t: t.clone()}), None )),
                        Some(( Rc::new(new_inferterm(next_inferterm_id)), None )),
                    ));
                }
            }

            if let Some(tt) = new_tt(
                typechk_term_supported_implicity(
                    &local_ctx, t.tower[0].clone(), t.tower[1].clone(),
                    substs, next_inferterm_id, enable_implicit,
                )?,
                next_inferterm_id, t,
                |new_t_term, new_t_type| Expr::Let {
                    env: env.clone(),
                    t: InferTypedTerm{tower: vec![new_t_term, new_t_type]},
                },
                &term,
            ) {
                return Ok(tt);
            }

            return Ok( unify_supported_implicity_local(
                type_.clone(), t.tower[1].clone(), false,
                term.clone(), next_inferterm_id, substs,
            )? );
        },
        Expr::Case{ref t, ref cases, ref datatype} => {
            let new_tt_from_t = |tt, next_inferterm_id: &mut InferTermId| {
                new_tt(tt, next_inferterm_id, t,
                    |new_t_term, new_t_type| Expr::Case {
                        t: InferTypedTerm{tower: vec![new_t_term, new_t_type]},
                        cases: cases.clone(),
                        datatype: datatype.clone(),
                    },
                    &term,
                )
            };
            let new_tt_from_case = |tt, next_inferterm_id: &mut InferTermId, case, ctor_no| {
                new_tt(
                    tt, next_inferterm_id, case,
                    |new_case_term, new_case_type| {
                        let mut new_cases = cases.clone();
                        new_cases[ctor_no] = InferTypedTerm{tower: vec![new_case_term, new_case_type]};

                        Expr::Case {
                            t: t.clone(),
                            cases: new_cases,
                            datatype: datatype.clone(),
                        }
                    },
                    &term,
                )
            };

            if let Some(tt) = new_tt_from_t(
                typechk_term_supported_implicity(
                    ctx, t.tower[0].clone(), t.tower[1].clone(),
                    substs, next_inferterm_id, enable_implicit
                )?, next_inferterm_id,
            ) {
                return Ok(tt);
            }

            if let Some(datatype) = datatype {
                if let Some(tt) = new_tt_from_t(
                    unify_supported_implicity_local(
                        t.tower[1].clone(), (Rc::new(Expr::Const(*datatype)), None), false,
                        t.tower[0].clone(), next_inferterm_id, substs,
                    )?, next_inferterm_id,
                ) {
                    return Ok(tt);
                }

                for (ctor_no, case) in cases.iter().enumerate() {
                    if let Some(tt) = new_tt_from_case(
                        typechk_term_supported_implicity(
                            ctx, case.tower[0].clone(), case.tower[1].clone(),
                            substs, next_inferterm_id, enable_implicit
                        )?,
                        next_inferterm_id, case, ctor_no,
                    ) {
                        return Ok(tt);
                    }

                    let ctors =
                        if let InferConst::DataType{ref ctors, ..} = ctx.consts[*datatype].c { ctors }
                        else { unreachable!() };
                    
                    let type_of_ctor = ctx.consts[ctors[ctor_no]].type_.clone();

                    if let Some(tt) = new_tt_from_case(
                        unify_supported_implicity_local(
                            case.tower[1].clone(), type_of_ctor, false,
                            case.tower[0].clone(), next_inferterm_id, substs,
                        )?,
                        next_inferterm_id, case, ctor_no,
                    ) {
                        return Ok(tt);
                    }
                }

                let types_of_cases : Vec<_> = (0..cases.len())
                    .map(|_| (Rc::new(new_inferterm(next_inferterm_id)), None)).collect();

                let type__ = Rc::new( Expr::Case {
                    t: t.clone(),
                    cases:
                        types_of_cases.into_iter()
                            .map( |T| InferTypedTerm{tower: vec![T, univ.clone()]} ).collect(),
                    datatype: Some(*datatype),
                } );

                return Ok( unify_supported_implicity_local(
                    type_.clone(), (type__, None), false,
                    term.clone(), next_inferterm_id, substs
                )? );
            }
        },
        Expr::Value(ref v) =>
            return unify_supported_implicity_local(
                type_.clone(), match *v {
                    Value::Nat(..) => unimplemented!(),
                    Value::Int(..) => unimplemented!(),
                    Value::Str(..) => unimplemented!(),
                }, false,
                term, next_inferterm_id, substs,
            ),
        Expr::Infer{..} => (),
        Expr::Subst(..) => unreachable!(),
        Expr::Equal(a, b) => {
            let (new_term, new_type) = unify_supported_implicity_local(
                a.clone(), b.clone(), true,
                term, next_inferterm_id, substs,
            )?;
            return Ok( (Some(new_term.unwrap_or(a.clone())), new_type) )
        }
    }

    Ok((None, None))
}

fn typechk_typing(ctx: &InferCtx, t: InferTypedTerm, T: InferTypedTerm,
    next_inferterm_id: &mut InferTermId, substs: &mut Vec<Equal>)
    -> Result<(), TypeChkErr>
{
    unify(t.tower[1].clone(), T.tower[0].clone(), next_inferterm_id, substs)?;
    unify(T.tower[1].clone(), (Rc::new(Expr::Universe), None), next_inferterm_id, substs)?;
    Ok(())
}

fn new_tt <F> (
    (new_orig_term, new_orig_type): (Option<(Rc<Expr>, Loc)>, Option<(Rc<Expr>, Loc)>),
    next_inferterm_id: &mut InferTermId,
    orig: &InferTypedTerm,
    new_term: F,
    term: &(Rc<Expr>, Loc)
) -> Option<(Option<(Rc<Expr>, Loc)>, Option<(Rc<Expr>, Loc)>)>
    where F: FnOnce((Rc<Expr>, Loc), (Rc<Expr>, Loc)) -> Expr
{
    if new_orig_term.is_some() || new_orig_type.is_some() {
        let new_orig_term = new_orig_term.unwrap_or(orig.tower[0].clone());
        let new_orig_type = new_orig_type.unwrap_or(orig.tower[1].clone());

        Some( (
            Some(( Rc::new(new_term(new_orig_term, new_orig_type)), term.1.clone() )),
            Some(( Rc::new(new_inferterm(next_inferterm_id)), None )),
        ) )
    }
    else { None }
}

fn unify_equals_env(env: &InferEnv, next_inferterm_id: &mut InferTermId, substs: &mut Vec<Equal>)
    -> Result<Option<InferEnv>, TypeChkErr>
{
    let mut new_env = None;

    let update_env = |new_env: &mut Option<InferEnv>, i, new_c| {
        if new_env.is_none() {
            *new_env = Some(env.clone());
        }

        new_env.as_mut().unwrap()[i] = new_c;
    };

    for (i, c) in env.iter().enumerate() {
        match c.c {
            InferConst::Def(ref t) => {
                let (new_term, new_type) =
                    unify_equals_typed(t.clone(), c.type_.clone(), next_inferterm_id, substs)?;
                
                if new_term.is_some() || new_type.is_some() {
                    update_env(&mut new_env, i, InferTypedConst {
                        c: InferConst::Def(new_term.unwrap_or(t.clone())),
                        type_: new_type.unwrap_or(c.type_.clone()),
                        ..c.clone()
                    });
                }
            },
            InferConst::DataType{ref param_types, ref type_, ref ctors} => {
                let mut new_param_types = None;

                for (idx, (param_type, i)) in param_types.iter().enumerate() {
                    let (new, _) = unify_equals(param_type.clone(), None, next_inferterm_id, substs)?;

                    if let Some(new) = new {
                        if new_param_types.is_none() {
                            new_param_types = Some(param_types.clone());
                        }

                        new_param_types.as_mut().unwrap()[idx] = (new, *i);
                    }
                }

                let (new_type, _) = unify_equals(type_.clone(), None, next_inferterm_id, substs)?;

                if new_param_types.is_some() || new_type.is_some() {
                    update_env(&mut new_env, i, InferTypedConst {
                        c: InferConst::DataType {
                            type_: new_type.unwrap_or(type_.clone()),
                            param_types: new_param_types.unwrap_or(param_types.clone()),
                            ctors: ctors.clone(),
                        },
                        ..c.clone()
                    });
                }
            },
            InferConst::Ctor{..} => {
                let (new_type, _) = unify_equals(c.type_.clone(), None, next_inferterm_id, substs)?;

                if let Some(new_type) = new_type {
                    update_env(&mut new_env, i, InferTypedConst {
                        type_: new_type,
                        ..c.clone()
                    });
                }
            },
        }
    }

    Ok(new_env)
}

fn unify_equals(
    term: (Rc<Expr>, Loc), lower: Option<(Rc<Expr>, Loc)>,
    next_inferterm_id: &mut InferTermId, substs: &mut Vec<Equal>,
)
    -> Result<(Option<(Rc<Expr>, Loc)>, Option<(Rc<Expr>, Loc)>), TypeChkErr>
{
    let enable_implicit = lower.is_some();

    let (term, loc) = term;

    match (*term).clone() {
        Expr::Equal(a, b) => {
            let a = unify_equals(a.clone(), None, next_inferterm_id, substs)?.0.unwrap_or(a);
            let b = unify_equals(b.clone(), None, next_inferterm_id, substs)?.0.unwrap_or(b);

            let (new_term, iparams) =
                unify_supported_implicity(a.clone(), b, next_inferterm_id, substs, enable_implicit)?;

            let new_lower =
                if iparams.is_empty() { None }
                else { Some(insert_implicit_args(lower.unwrap(), iparams, next_inferterm_id)) };

            return Ok(( Some(new_term.unwrap_or(a)), new_lower ));
        },
        Expr::App{s,t,implicity} => {
            let new_s = unify_equals_typed_wrap(s.clone(), next_inferterm_id, substs)?;
            let new_t = unify_equals_typed_wrap(t.clone(), next_inferterm_id, substs)?;

            if new_s.is_some() || new_t.is_some() {
                return Ok((
                    Some((Rc::new(Expr::App{s: new_s.unwrap_or(s), t: new_t.unwrap_or(t), implicity}), loc)),
                    None,
                ));
            }
        },
        Expr::Lam(InferAbs{A,t}, i) => {
            let new_A = unify_equals_typed_wrap(A.clone(), next_inferterm_id, substs)?;
            let new_t = unify_equals_typed_wrap(t.clone(), next_inferterm_id, substs)?;

            if new_A.is_some() || new_t.is_some() {
                return Ok((
                    Some((Rc::new(Expr::Lam(InferAbs{A: new_A.unwrap_or(A), t: new_t.unwrap_or(t)}, i)), loc)),
                    None,
                ));
            }
        },
        Expr::Pi(InferAbs{A,t}, i) => {
            let new_A = unify_equals_typed_wrap(A.clone(), next_inferterm_id, substs)?;
            let new_t = unify_equals_typed_wrap(t.clone(), next_inferterm_id, substs)?;

            if new_A.is_some() || new_t.is_some() {
                return Ok((
                    Some((Rc::new(Expr::Pi(InferAbs{A: new_A.unwrap_or(A), t: new_t.unwrap_or(t)}, i)), loc)),
                    None,
                ));
            }
        },
        Expr::Let{env, t} => {
            let new_env = unify_equals_env(&env, next_inferterm_id, substs)?;
            let new_t = unify_equals_typed_wrap(t.clone(), next_inferterm_id, substs)?;

            if new_env.is_some() || new_t.is_some() {
                return Ok((
                    Some((Rc::new(Expr::Let{env: new_env.unwrap_or(env), t: new_t.unwrap_or(t)}), None)),
                    None,
                ));
            }
        },
        Expr::Case{t, cases, datatype} => {
            let new_t = unify_equals_typed_wrap(t.clone(), next_inferterm_id, substs)?;

            let mut new_cases = None;
            for (i, case) in cases.iter().enumerate() {
                if let Some(new_case) = unify_equals_typed_wrap(case.clone(), next_inferterm_id, substs)? {
                    if new_cases.is_none() {
                        new_cases = Some(cases.clone());
                    }
                    new_cases.as_mut().unwrap()[i] = new_case;
                }
            }

            if new_t.is_some() || new_cases.is_some() {
                return Ok((
                    Some((Rc::new(Expr::Case {
                        t: new_t.unwrap_or(t),
                        cases: new_cases.unwrap_or(cases),
                        datatype
                    }), None)),
                    None,
                ))
            }
        },
        Expr::Subst(..) => unreachable!(),
        _ => (),
    }

    Ok((None, None))
}

fn unify_equals_typed(
    term: (Rc<Expr>, Loc), type_: (Rc<Expr>, Loc),
    next_inferterm_id: &mut InferTermId, substs: &mut Vec<Equal>
)
    -> Result<(Option<(Rc<Expr>, Loc)>, Option<(Rc<Expr>, Loc)>), TypeChkErr>
{
    let (new_term, _) = unify_equals(term.clone(), None, next_inferterm_id, substs)?;
    let (new_type, new_term2) =
        unify_equals(type_, Some(new_term.clone().unwrap_or(term)), next_inferterm_id, substs)?;
    
    Ok((new_term2.or(new_term), new_type))
}

fn unify_equals_typed_wrap(
    term: InferTypedTerm, next_inferterm_id: &mut InferTermId, substs: &mut Vec<Equal>
)
    -> Result<Option<InferTypedTerm>, TypeChkErr>
{
    let t = term.tower[0].clone();
    let T = term.tower[1].clone();

    let (new_t, new_T) = unify_equals_typed(t.clone(), T.clone(), next_inferterm_id, substs)?;

    Ok(
        if new_t.is_some() || new_T.is_some() {
            Some( InferTypedTerm{tower: vec![new_t.unwrap_or(t), new_T.unwrap_or(T)]} )
        }
        else { None }
    )
}

pub(super) fn insert_implicit_args(
    term: (Rc<Expr>, Loc),
    implicit_param_types: Vec<((Rc<Expr>, Loc), u8)>,
    next_inferterm_id: &mut InferTermId,
)
    -> (Rc<Expr>, Loc)
{
    implicit_param_types.into_iter().fold( term.clone(),
        |t, (param_type, implicity)| (Rc::new(Expr::App{
            s: InferTypedTerm{tower: vec![t, (Rc::new(new_inferterm(next_inferterm_id)), None)]},
            t: InferTypedTerm{tower: vec![(Rc::new(new_inferterm(next_inferterm_id)), None), param_type]},
            implicity,
        }), None)
    )
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

fn assign_const(c: (HoledConst, Loc), inferterm_id: &mut InferTermId) -> InferTypedConst {
    let (c, loc) = c;

    let (ic, type_) = match c {
        HoledConst::Def{rhs, type_} => 
            (
                InferConst::Def(assign_term_nontyped(rhs, inferterm_id)),
                assign_term_nontyped(type_, inferterm_id),
            ),
        HoledConst::DataType{param_types, type_, ctors} => {
            let assigned_param_types: Vec<_> =
                param_types.into_iter().map(|t| (assign_term_nontyped(t.0, inferterm_id), t.1)).collect();
            let assigned_type = assign_term_nontyped(type_, inferterm_id);

            (
                InferConst::DataType {
                    param_types: assigned_param_types.clone(),
                    type_: assigned_type.clone(),
                    ctors,
                },
                assigned_param_types.into_iter().fold( assigned_type,
                    |t, (p,pi)| (
                        Rc::new(Expr::Pi(InferAbs {
                            A: InferTypedTerm{tower: vec![(p.0, p.1.clone()), (Rc::new(Expr::Universe), None)]},
                            t: InferTypedTerm{tower: vec![t, (Rc::new(new_inferterm(inferterm_id)), None)]},
                        }, pi)),
                        p.1
                    ),
                ),
            )
        },
        HoledConst::Ctor{datatype, type_} =>
            (
                InferConst::Ctor { datatype },
                assign_term_nontyped(type_, inferterm_id),
            ),
    };

    InferTypedConst{c: ic, type_, loc}
}

fn assign_term(term: (Rc<HoledTerm>, Loc), inferterm_id: &mut InferTermId) -> InferTypedTerm {
    InferTypedTerm {
        tower: vec![
            assign_term_nontyped(term, inferterm_id),
            (Rc::new(new_inferterm(inferterm_id)), None),
        ],
    }
}

fn assign_term_nontyped(term: (Rc<HoledTerm>, Loc), inferterm_id: &mut InferTermId) -> (Rc<Expr>, Loc) {
    let (term, loc) = term;

    ( Rc::new( match *term {
        HoledTerm::Const(ref id) => Expr::Const(*id),
        HoledTerm::DBI(ref i) => Expr::DBI(*i as usize),
        HoledTerm::Universe => Expr::Universe,
        HoledTerm::App{ref s, ref t, implicity} =>
            Expr::App{s: assign_term(s.clone(), inferterm_id), t: assign_term(t.clone(), inferterm_id), implicity},
        HoledTerm::Lam(ref abs, implicity) => Expr::Lam(assign_abs(abs.clone(), inferterm_id), implicity),
        HoledTerm::Pi(ref abs, implicity) => Expr::Pi(assign_abs(abs.clone(), inferterm_id), implicity),
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
    } ), loc)
}

fn assign_consts(consts: Vec<(HoledConst, Loc)>, next_inferterm_id: &mut InferTermId) -> InferEnv {
    consts.into_iter().map(|c| assign_const(c, next_inferterm_id)).collect()
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
    App{s: InferTypedTerm, t: InferTypedTerm, implicity: u8},
    Lam(InferAbs, u8),
    Pi(InferAbs, u8),
    Let{env: InferEnv, t: InferTypedTerm},
    Case{t: InferTypedTerm, cases: Vec<InferTypedTerm>, datatype: Option<ConstId>},
    Value(Value),
    Infer{id: Rc<Cell<InferTermId>>},
    Subst(Subst, (Rc<Expr>, Loc)),
    Equal((Rc<Expr>, Loc), (Rc<Expr>, Loc)),
}

#[derive(Clone, Debug)]
pub struct InferAbs {
    pub A: InferTypedTerm,
    pub t: InferTypedTerm,
}

#[derive(Clone, Debug)]
pub struct InferTypedConst {
    pub(super) c: InferConst,
    pub(super) type_: (Rc<Expr>, Loc),
    pub(super) loc: Loc,
}

#[derive(Clone, Debug)]
pub(super) enum InferConst {
    Def((Rc<Expr>, Loc)),
    DataType{param_types: Vec<((Rc<Expr>, Loc), u8)>, type_: (Rc<Expr>, Loc), ctors: Vec<ConstId>},
    Ctor{datatype: ConstId},
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
    pub(super) tower: Vec<(Rc<Expr>, Loc)>,
}

pub(super) type InferTermId = usize;

#[derive(Clone, Debug)]
pub(super) enum Equal {
    ToId(Rc<Cell<InferTermId>>, Rc<Cell<InferTermId>>),
    Instantiate(Rc<Cell<InferTermId>>, (Rc<Expr>, Loc)),
    Defer((Rc<Expr>, Loc), (Rc<Expr>, Loc)),
}
impl Equal {
    pub(super) fn sort(lhs: Rc<Cell<InferTermId>>, rhs: (Rc<Expr>, Loc)) -> Self {
        if let Expr::Infer{ref id} = *rhs.0.clone() { Equal::ToId(lhs, id.clone()) }
        else { Equal::Instantiate(lhs, rhs) }
    }
}