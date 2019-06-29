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
    let mut before_ctx = ctx.clone();

    let mut substs: Vec<Equal> = vec![];
    let mut substs_map: HashMap<InferTermId, (Rc<Expr>, Loc)> = HashMap::new();
    'typechk : for typechk_it in 0.. {
        debug!("type-check iteration {}.", typechk_it);
        debug!("current context: {}", ctx);

        ctx = typechk_superposition_ctx(&ctx, &mut next_inferterm_id);

        debug!("type superposition ctx: {}", ctx);

        // let mut subst_results = vec![];
        for unify_it in 0.. {
            debug!("unification iteration {}.{}.", typechk_it, unify_it);

            debug!("starting unification");
            ctx = unify_equals_ctx(ctx, &mut next_inferterm_id, &mut substs)?;
            debug!("finished unification.");
            debug!("unificated ctx: {}", ctx);

            debug!("collected substitutions:");
            for subst in &substs {
                debug!("\t{}", subst);
            }

            convert_substs_map(&mut substs_map, &mut substs)?;

            debug!("substitutions:");
            for (k,v) in &substs_map {
                debug!("\t?{} / {}", k, v.0);
            }

            let subst_result = subst_infers(&mut ctx, &mut substs_map);
            // subst_results.push(subst_result.clone());

            debug!("substitution result:");
            debug!("found_infer?: {}", subst_result.found_infer);
            debug!("has_substed?: {}", subst_result.has_substed);

            debug!("current ctx: {}\n", ctx);

            if !subst_result.found_infer {
                break 'typechk;
            }
            if !subst_result.has_substed {
                break;
            }
        }
        
        // 条件が足りず無限ループしたときを検知して推論を失敗させる
        if ctx == before_ctx {
            return Err(TypeChkErr::InferFailure);
        }

        before_ctx = ctx.clone();
    }

    debug!("finished type checking.");
    debug!("current context:\n{}", ctx);

    Ok( cast_no_infer(ctx) )
}

fn convert_substs_map(substs_map: &mut HashMap<InferTermId, ExprL>, substs: &mut Vec<Equal>)
    -> Result<(), TypeChkErr>
{
    // 推論項への代入時の衝突によりunificationが発生し代入が増えることがあるため, 完全に代入がなくなるまでループ
    while !substs.is_empty() {
        for subst in substs.split_off(0) {
            match subst {
                Equal::ToId(mut lhs, mut rhs) => {
                    if rhs > lhs { ::std::mem::swap(&mut lhs, &mut rhs); }
                    if rhs == lhs { continue; }
                    assert!(lhs > rhs);

                    if let Some(mut instance) = substs_map.remove(&lhs.get()) {
                        if let Some(other) = substs_map.get(&rhs.get()).cloned() {
                            instance = superposition_loc(instance, other, None);
                        }
                        substs_map.insert(rhs.get(), instance);
                    }
                    lhs.set(rhs.get());
                },
                Equal::Instantiate(id, mut instance) => {
                    if let Some(other) = substs_map.get(&id.get()).cloned() {
                        instance = superposition_loc(instance, other, None);
                    }
                    substs_map.insert(id.get(), instance);
                },
            }
        }
    }
    Ok(())
}

fn subst_infers(
    ctx: &mut InferCtx,
    substs_map: &mut HashMap<InferTermId, (Rc<Expr>, Loc)>
)
    -> SubstResult
{
    assert!(ctx.local.is_empty());

    let mut result = SubstResult{has_substed: false, found_infer: false};

    subst_infers_ctx(ctx, substs_map, &mut result);

    let found_infer = result.found_infer;

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
                Expr::Equal(ref mut xs) =>
                    for x in xs {
                        subst_infers_term(x, substs, result);
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

#[derive(Clone, Debug)]
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

pub type ExprL = (Rc<Expr>, Loc);

fn typechk_superposition_ctx(ctx: &InferCtx, next_ii: &mut InferTermId) -> InferCtx {
    InferCtx {
        consts:
            ctx.consts.iter()
                .map(|c| typechk_superposition_const(&ctx, c, next_ii).unwrap_or(c.clone())).collect(),
        local:
            ctx.local.iter()
                .map(|tt| typechk_superposition_typedterm(&ctx, tt, next_ii).unwrap_or(tt.clone())).collect(),
        typings:
            ctx.typings.iter().map(|(term, type_)| {
                let new_term = typechk_superposition_typedterm(&ctx, term, next_ii).unwrap_or(term.clone());
                let new_type = typechk_superposition_typedterm(&ctx, type_, next_ii).unwrap_or(type_.clone());

                let t = new_term.tower[0].clone(); // ソースコード上で型付けられた項
                let a = new_term.tower[1].clone(); // その項の型
                let b = new_type.tower[0].clone(); // ソースコード上で型付けている型
                let u = new_type.tower[1].clone(); // その型の型

                (
                    InferTypedTerm{tower: vec![t, superposition(a.clone(), b.clone())]},
                    InferTypedTerm{tower: vec![superposition(b, a), u]},
                )
            }).collect(),
    }
}

fn typechk_superposition_const(ctx: &InferCtx, c: &InferTypedConst, next_ii: &mut InferTermId)
    -> Option<InferTypedConst>
{
    // 変数の種類ごとに場合分け
    match c.c {
        InferConst::Def(ref t) => {
            let (new_term, new_type) = typechk_superposition(ctx, t.clone(), c.type_.clone(), next_ii);

            // 変更があればSomeを返して変更を伝播
            if new_term.is_some() || new_type.is_some() {
                Some( InferTypedConst {
                    c: InferConst::Def(new_term.unwrap_or(t.clone())),
                    type_: new_type.unwrap_or(c.type_.clone()),
                    ..c.clone()
                } )
            }
            else { None }
        },
        InferConst::DataType{ref param_types, ref type_, ref ctors} => {
            // 1階型宇宙
            let univ1 = (Rc::new(Expr::Universe), None);

            // 新しいGADTパラメタ型リスト
            let mut new_param_types = param_types.clone();

            // GADTのパラメタ型を型検査
            for (idx, (param_type, i)) in param_types.iter().enumerate() {
                // GADTのパラメタ型`param_type`は1階の型である
                let (new_type1, new_type2) = typechk_superposition(ctx, param_type.clone(), univ1.clone(), next_ii);

                // GADTのパラメタ型の型は変更不可
                // `new_type2`は変更があったとしても`Some(<Type1=Type1>)`でなければならない
                if let Some(new_type2) = new_type2 {
                    if let Expr::Equal(ref xs) = *new_type2.0 {
                        assert!(xs.len() == 2);
                        let a = xs[0].clone();
                        let b = xs[1].clone();

                        if let Expr::Universe = *a.0 {}
                        else { assert!(false); }

                        if let Expr::Universe = *b.0 {}
                        else { assert!(false); }
                    }
                    else { assert!(false); }
                }

                if let Some(new_type1) = new_type1 {
                    new_param_types[idx] = (new_type1, *i);
                }
            }

            let new_param_types = new_param_types;

            let univk = (Rc::new(Expr::Universe), None);

            // GADT型の(パラメタを除く)型は常に型宇宙でなければならない
            // 常に`type_`が型宇宙との重ね合わせへ置き換わる
            Some( InferTypedConst {
                c: InferConst::DataType {
                    param_types: new_param_types,
                    type_: superposition(type_.clone(), univk),
                    ctors: ctors.clone(),
                },
                ..c.clone()
            } )

            // GADTの変数型`c.type_`は型検査開始時に適切に初期化されるため, ここで検査する必要はない
        },
        InferConst::Ctor{datatype: _} => {
            // 1階型宇宙
            let univ1 = (Rc::new(Expr::Universe), None);

            // コンストラクタの型`c.type_`は1階の型である
            let (new_type1, new_type2) = typechk_superposition(ctx, c.type_.clone(), univ1, next_ii);

            // コンストラクタの型の型は変更不可
            // `new_type2`は変更があったとしても`<Type1=Type1>`でなければならない
            if let Some(new_type2) = new_type2 {
                if let Expr::Equal(ref xs) = *new_type2.0 {
                    assert!(xs.len() == 2);
                    let a = xs[0].clone();
                    let b = xs[1].clone();

                    if let Expr::Universe = *a.0 {}
                    else { assert!(false); }

                    if let Expr::Universe = *b.0 {}
                    else { assert!(false); }
                }
                else { assert!(false); }
            }

            // コンストラクタの型が変更されればSomeで返して変更を伝播
            new_type1.map( |new_type1| InferTypedConst{type_: new_type1, ..c.clone()} )
        }
    }
}

fn flatten_equal(xs: Vec<ExprL>, ys: &mut Vec<ExprL>) {
    for x in xs {
        if let Expr::Equal(zs) = (*x.0).clone() {
            flatten_equal(zs.clone(), ys);
        }
        else {
            ys.push(x);
        }
    }
}

pub(super) fn superposition_many<I : IntoIterator<Item=ExprL>>(xs: I, loc: Loc) -> ExprL {
    let mut ys = vec![];
    for x in xs {
        if let Expr::Equal(zs) = (*x.0).clone() {
            flatten_equal(zs.clone(), &mut ys);
        }
        else {
            ys.push(x);
        }
    }
    (Rc::new(Expr::Equal(ys)), loc)
}

pub(super) fn superposition_loc(a: ExprL, b: ExprL, loc: Loc) -> ExprL {
    let mut ys = vec![];
    flatten_equal(vec![a, b], &mut ys);
    (Rc::new(Expr::Equal(ys)), loc)
}

// 重ね合わせ項を生成する関数
fn superposition(origin: ExprL, inferred: ExprL) -> ExprL {
    let loc = origin.1.clone();
    superposition_loc(origin, inferred, loc)
}

/*  項`term`の種類によって推論された項と実際の項`type_`の重ね合わせを含んだ項木を生成する関数
 *  `term` : チェックされる項
 *  `type_` : termの型
 *  戻り値 : 重ね合わせを含む新たな項と型のtuple, それぞれ変更がなければNone
 */
fn typechk_superposition(ctx: &InferCtx, term: (Rc<Expr>, Loc), type_: (Rc<Expr>, Loc), next_ii: &mut InferTermId)
    -> (Option<ExprL>, Option<ExprL>)
{
    let equal_type = |a| superposition(type_, a);

    let (_, loc_term) = term;

    // 型宇宙の項を作っておく
    let univ = (Rc::new(Expr::Universe), None);

    // 項の種類ごとに場合分け
    match *term.0 {
        Expr::Const(cid) => (None, Some( equal_type( ctx.consts[cid].type_.clone() ) )),
        Expr::DBI(i) => (None, Some( equal_type( ctx.local(i).tower[0].clone() ) )),
        Expr::Universe => (None, Some( equal_type(univ) )),
        Expr::App{ref s, ref t, implicity} => {
            // 部分項についても再帰的に重ね合わせ型推論
            let new_s = typechk_superposition_typedterm(ctx, s, next_ii).unwrap_or(s.clone());
            let new_t = typechk_superposition_typedterm(ctx, t, next_ii).unwrap_or(t.clone());

            // 適用する関数`s`の戻り値の型. この時点では不明なため新たな推論型とする.
            let typeof_s_ret = (Rc::new(new_inferterm(next_ii)), None);

            // 適用する関数`s`の型
            let inferred_typeof_s = (Rc::new( Expr::Pi(InferAbs{
                A: InferTypedTerm{tower: vec![ new_t.tower[1].clone(), univ.clone() ]},
                t: InferTypedTerm{tower: vec![ typeof_s_ret.clone(), univ ]},
            }, implicity) ), None);

            // 適用する関数`s`の型について重ね合わせられた新たな項
            let new_term = (Rc::new( Expr::App {
                s: InferTypedTerm{ tower: vec![
                    new_s.tower[0].clone(),
                    superposition(new_s.tower[1].clone(), inferred_typeof_s)
                ] },
                t: new_t,
                implicity,
            } ), loc_term);

            // この関数適用項の型. 適用する関数`s`は依存関数でありうるため、戻り値の型は引数`t`に依存する.
            // `s`の戻り値の型`typeof_s_ret`への引数`t`の明示的代入(explicit substitution)として項全体の型を表現する.
            let inferred_type = (Rc::new( Expr::Subst(
                Subst::from_expr(t.tower[0].clone()),
                typeof_s_ret,
            ) ), None);

            (Some(new_term), Some(equal_type(inferred_type)))
        },
        Expr::Lam(InferAbs{ref A, ref t}, implicity) => {
            // 戻り値`t`の型検査をするために, 関数抽象の引数型`A`の変数がローカル変数に追加された局所文脈を作る
            let mut local_ctx = ctx.clone();
            local_ctx.local.push( subst_typed_lazily(Subst::Shift(1), A.clone()) );
            let local_ctx = local_ctx;

            // 部分項についても再帰的に重ね合わせ型推論
            // `t`については局所文脈で型検査する
            let new_A = typechk_superposition_typedterm(ctx, A, next_ii).unwrap_or(A.clone());
            let new_t = typechk_superposition_typedterm(&local_ctx, t, next_ii).unwrap_or(t.clone());

            let arg_type = new_A.tower[0].clone(); // 引数の型
            let arg_type2 = new_A.tower[1].clone(); // 引数の型の型

            // 戻り値の型
            let ret_type = new_t.tower[1].clone();

            let inferred_type = (Rc::new( Expr::Pi( InferAbs {
                A: InferTypedTerm{tower: vec![arg_type, superposition(arg_type2, univ.clone())]},
                t: InferTypedTerm{tower: vec![ret_type, univ]},
            }, implicity ) ), None);

            (None, Some(equal_type(inferred_type)))
        },
        Expr::Pi(InferAbs{ref A, ref t}, implicity) => {
            // 戻り値`t`の型検査をするために, 関数抽象の引数型`A`の変数がローカル変数に追加された局所文脈を作る
            let mut local_ctx = ctx.clone();
            local_ctx.local.push( subst_typed_lazily(Subst::Shift(1), A.clone()) );
            let local_ctx = local_ctx;

            // 部分項についても再帰的に重ね合わせ型推論
            // `t`については局所文脈で型検査する
            let new_A = typechk_superposition_typedterm(ctx, A, next_ii).unwrap_or(A.clone());
            let new_t = typechk_superposition_typedterm(&local_ctx, t, next_ii).unwrap_or(t.clone());

            // `A`と`t`それぞれの型を型宇宙と重ね合わせる
            let new_term = (Rc::new( Expr::Pi( InferAbs {
                A: InferTypedTerm{tower: vec![ new_A.tower[0].clone(),
                    superposition(new_A.tower[1].clone(), univ.clone()) ]},
                t: InferTypedTerm{tower: vec![ new_t.tower[0].clone(),
                    superposition(new_t.tower[1].clone(), univ.clone()) ]},
            }, implicity ) ), loc_term);

            (Some(new_term), Some(equal_type(univ)))
        },
        Expr::Let{ref env, ref t} => {
            // 局所変数 : let ... in ... 構文において、内部で使用可能な新たな変数のこと. 一般に複数.

            // 新しい局所変数リスト
            let mut new_env = env.clone();

            // すべての局所変数について型検査
            for (idx, c) in env.iter().enumerate() {
                // ※: 型検査における文脈はletの内側ではなく外側の文脈である.
                // TODO:    let ... in ... で複数変数を定義する際, 変数の相互参照を可能にするべきだろうか?
                //          let ... in let ... in ... と並べることで循環のない相互参照は実質的に可能だが.
                if let Some(new_c) = typechk_superposition_const(ctx/*※*/, c, next_ii) {
                    new_env[idx] = new_c;
                }
            }

            let new_env = new_env;

            // 局所文脈`local_ctx`は現在の文脈`ctx`に局所変数`new_env`を追加したもの
            let mut local_ctx = ctx.clone();
            local_ctx.consts.extend(new_env.iter().cloned());
            let local_ctx = local_ctx;

            // let値`t`を局所文脈で型検査する
            let new_t = typechk_superposition_typedterm(&local_ctx, t, next_ii).unwrap_or(t.clone());

            // 全体の型`type_`はlet値`t`の型に等しい
            let inferred_type = new_t.tower[1].clone();

            let new_term = (Rc::new( Expr::Let {
                env: new_env,
                t: new_t,
            } ), loc_term);

            (Some(new_term), Some(equal_type(inferred_type)))
        },
        Expr::Case{ref t, ref cases, ref datatype} => unimplemented!(),
        Expr::Value(ref v) => (None, Some( equal_type( match *v {
            Value::Nat(..) => unimplemented!(),
            Value::Int(..) => unimplemented!(),
            Value::Str(..) => unimplemented!(),
        } ) )),
        Expr::Infer{..} => (None, None),
        Expr::Subst(..) => unreachable!(),
        Expr::Equal(..) => unreachable!(),
    }
}

// 重ね合わせ型推論関数を型付き項`InferTypedTerm`用にラップした関数
fn typechk_superposition_typedterm(ctx: &InferCtx, tt: &InferTypedTerm, next_ii: &mut InferTermId)
    -> Option<InferTypedTerm>
{
    let term = tt.tower[0].clone();
    let type_ = tt.tower[1].clone();

    let (new_term, new_type) = typechk_superposition(ctx, term.clone(), type_.clone(), next_ii);

    // 項か型どちらかが変更されていたら, 型付き項全体が変更されたものとしてSomeで返す
    if new_term.is_some() || new_type.is_some() {
        Some( InferTypedTerm{ tower: vec![new_term.unwrap_or(term), new_type.unwrap_or(type_)] } )
    }
    else { None }
}

fn unify_equals_ctx(ctx: InferCtx, next_ii: &mut InferTermId, substs: &mut Vec<Equal>)
    -> Result<InferCtx, TypeChkErr>
{
    let new_ctx = InferCtx {
        consts:
            unify_equals_env(ctx.consts, next_ii, substs)?,
        local:
            ctx.local.into_iter()
                .map( |t| unify_equals_typed_wrap(t, next_ii, substs) )
                .collect::<Result<_,TypeChkErr>>()?,
        typings:
            ctx.typings.into_iter().map( |(term, type_)| Ok((
                unify_equals_typed_wrap(term, next_ii, substs)?,
                unify_equals_typed_wrap(type_, next_ii, substs)?,
            )) ).collect::<Result<_,TypeChkErr>>()?,
    };

    Ok(new_ctx)
}

fn unify_equals_env(env: InferEnv, next_inferterm_id: &mut InferTermId, substs: &mut Vec<Equal>)
    -> Result<InferEnv, TypeChkErr>
{
    env.into_iter().map( |c| Ok({
        match c.c {
            InferConst::Def(ref t) => {
                let (new_term, new_type) =
                    unify_equals_typed(t.clone(), c.type_.clone(), next_inferterm_id, substs)?;
                
                InferTypedConst {
                    c: InferConst::Def(new_term),
                    type_: new_type,
                    ..c.clone()
                }
            },
            InferConst::DataType{ref param_types, ref type_, ref ctors} => {
                let new_param_types = param_types.iter()
                    .map( |(param_type, i)|
                        Ok(( unify_equals(param_type.clone(), None, next_inferterm_id, substs)?.0, *i ))
                    )
                    .collect::<Result<Vec<_>,TypeChkErr>>()?;

                let (new_type, _) = unify_equals(type_.clone(), None, next_inferterm_id, substs)?;

                let (new_c_type, _) = unify_equals(c.type_.clone(), None, next_inferterm_id, substs)?;

                InferTypedConst {
                    c: InferConst::DataType {
                        type_: new_type,
                        param_types: new_param_types,
                        ctors: ctors.clone(),
                    },
                    type_: new_c_type,
                    ..c.clone()
                }
            },
            InferConst::Ctor{..} => {
                let (new_type, _) = unify_equals(c.type_.clone(), None, next_inferterm_id, substs)?;

                InferTypedConst {
                    type_: new_type,
                    ..c.clone()
                }
            },
        }
    }) ).collect()
}

fn unify_equals(
    mut term: (Rc<Expr>, Loc), mut lower: Option<(Rc<Expr>, Loc)>,
    next_inferterm_id: &mut InferTermId, substs: &mut Vec<Equal>,
)
    -> Result<((Rc<Expr>, Loc), Option<(Rc<Expr>, Loc)>), TypeChkErr>
{
    let enable_implicit = lower.is_some();

    let loc = term.1.clone();

    try_subst(&mut term);
    if let Some(ref mut lower) = lower {
        try_subst(lower);
    }

    match (*term.0).clone() {
        Expr::Equal(xs) => {
            let xs = xs.into_iter().map(|x| Ok(unify_equals(x, None, next_inferterm_id, substs)?.0))
                .collect::<Result<Vec<ExprL>, TypeChkErr>>()?;

            let (new_term, iparams) =
                unify_combination(&xs, next_inferterm_id, substs, enable_implicit)?;

            let new_lower =
                if iparams.is_empty() { lower }
                else { Some(insert_implicit_args(lower.unwrap(), iparams, next_inferterm_id)) };

            Ok(( new_term.unwrap_or(xs[0].clone()), new_lower ))
        },
        Expr::App{s,t,implicity} => {
            let new_s = unify_equals_typed_wrap(s.clone(), next_inferterm_id, substs)?;
            let new_t = unify_equals_typed_wrap(t.clone(), next_inferterm_id, substs)?;

            Ok((
                (Rc::new(Expr::App{s: new_s, t: new_t, implicity}), loc),
                lower,
            ))
        },
        Expr::Lam(InferAbs{A,t}, i) => {
            let new_A = unify_equals_typed_wrap(A.clone(), next_inferterm_id, substs)?;
            let new_t = unify_equals_typed_wrap(t.clone(), next_inferterm_id, substs)?;

            Ok((
                (Rc::new(Expr::Lam(InferAbs{A: new_A, t: new_t}, i)), loc),
                lower,
            ))
        },
        Expr::Pi(InferAbs{A,t}, i) => {
            let new_A = unify_equals_typed_wrap(A.clone(), next_inferterm_id, substs)?;
            let new_t = unify_equals_typed_wrap(t.clone(), next_inferterm_id, substs)?;

            Ok((
                (Rc::new(Expr::Pi(InferAbs{A: new_A, t: new_t}, i)), loc),
                lower,
            ))
        },
        Expr::Let{env, t} => {
            let new_env = unify_equals_env(env, next_inferterm_id, substs)?;
            let new_t = unify_equals_typed_wrap(t.clone(), next_inferterm_id, substs)?;

            Ok((
                (Rc::new(Expr::Let{env: new_env, t: new_t}), None),
                lower,
            ))
        },
        Expr::Case{t, cases, datatype} => {
            let new_t = unify_equals_typed_wrap(t.clone(), next_inferterm_id, substs)?;

            let new_cases = cases.into_iter()
                .map(|case| unify_equals_typed_wrap(case.clone(), next_inferterm_id, substs))
                .collect::<Result<_,TypeChkErr>>()?;

            Ok((
                (Rc::new(Expr::Case {
                    t: new_t,
                    cases: new_cases,
                    datatype
                }), None),
                lower,
            ))
        },
        Expr::Subst(s,e) => {
            let new_s = unify_equals_subst(s.clone(), next_inferterm_id, substs)?;
            let new_e = unify_equals(e.clone(), None, next_inferterm_id, substs)?;

            assert!(new_e.1.is_none());

            Ok((
                (Rc::new(Expr::Subst(new_s, new_e.0)), None),
                lower,
            ))
        },
        _ => Ok((term, lower)),
    }
}

fn unify_equals_subst(s: Subst, next_ii: &mut InferTermId, substs: &mut Vec<Equal>)
    -> Result<Subst, TypeChkErr>
{
    let new_s = match s {
        Subst::Shift(_) => s,
        Subst::Dot(e,s) => 
            Subst::Dot(
                unify_equals(e.clone(), None, next_ii, substs)?.0,
                Rc::new(unify_equals_subst((*s).clone(), next_ii, substs)?),
            ),
    };

    Ok(new_s)
}

fn unify_equals_typed(
    term: (Rc<Expr>, Loc), type_: (Rc<Expr>, Loc),
    next_inferterm_id: &mut InferTermId, substs: &mut Vec<Equal>
)
    -> Result<((Rc<Expr>, Loc), (Rc<Expr>, Loc)), TypeChkErr>
{
    let (new_term, _) = unify_equals(term.clone(), None, next_inferterm_id, substs)?;
    let (new_type, new_term2) =
        unify_equals(type_, Some(new_term.clone()), next_inferterm_id, substs)?;
    
    Ok((new_term2.unwrap(), new_type))
}

fn unify_equals_typed_wrap(
    term: InferTypedTerm, next_inferterm_id: &mut InferTermId, substs: &mut Vec<Equal>
)
    -> Result<InferTypedTerm, TypeChkErr>
{
    let t = term.tower[0].clone();
    let T = term.tower[1].clone();

    let (new_t, new_T) = unify_equals_typed(t.clone(), T.clone(), next_inferterm_id, substs)?;

    Ok( InferTypedTerm{ tower: vec![new_t, new_T] } )
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

#[derive(Clone, Debug, PartialEq)]
pub enum Expr {
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
    Equal(Vec<(Rc<Expr>, Loc)>),
}

#[derive(Clone, Debug, PartialEq)]
pub struct InferAbs {
    pub A: InferTypedTerm,
    pub t: InferTypedTerm,
}

#[derive(Clone, Debug, PartialEq)]
pub struct InferTypedConst {
    pub(super) c: InferConst,
    pub(super) type_: (Rc<Expr>, Loc),
    pub(super) loc: Loc,
}

#[derive(Clone, Debug, PartialEq)]
pub(super) enum InferConst {
    Def((Rc<Expr>, Loc)),
    DataType{param_types: Vec<((Rc<Expr>, Loc), u8)>, type_: (Rc<Expr>, Loc), ctors: Vec<ConstId>},
    Ctor{datatype: ConstId},
}

pub(super) type InferEnv = Vec<InferTypedConst>;

#[derive(Clone, Debug, PartialEq)]
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

#[derive(Clone, Debug, PartialEq)]
pub struct InferTypedTerm {
    pub(super) tower: Vec<(Rc<Expr>, Loc)>,
}

pub(super) type InferTermId = usize;

#[derive(Clone, Debug)]
pub(super) enum Equal {
    ToId(Rc<Cell<InferTermId>>, Rc<Cell<InferTermId>>),
    Instantiate(Rc<Cell<InferTermId>>, (Rc<Expr>, Loc)),
}
impl Equal {
    pub(super) fn sort(lhs: Rc<Cell<InferTermId>>, rhs: (Rc<Expr>, Loc)) -> Self {
        if let Expr::Infer{ref id} = *rhs.0.clone() { Equal::ToId(lhs, id.clone()) }
        else { Equal::Instantiate(lhs, rhs) }
    }
}













