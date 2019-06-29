use super::typechk::*;
use super::explicit_subst::*;
use syntax::Loc;

use std::rc::Rc;
use itertools::Itertools;

// 3個以上の重ね合わせを、全組み合わせでunificationする
// 暗黙引数推論により項の更新が発生したとき、もし項が衝突していたらエラーにする
pub(super) fn unify_combination(
    xs: &Vec<ExprL>,
    next_ii: &mut InferTermId,
    substs: &mut Vec<Equal>,
    enable_implicit: bool,
)
    -> Result<(Option<(Rc<Expr>, Loc)>, Vec<((Rc<Expr>, Loc), u8)>), UnifyErr>
{
    let mut new_term : Option<ExprL> = None;
    let mut iparams = vec![];

    for (a,b) in xs.iter().tuple_combinations() {
        let (new_term_, iparams_) =
            unify_supported_implicity(a.clone(), b.clone(), next_ii, substs, enable_implicit)?;
        
        if let Some(new_term_) = new_term_ {
            if let Some(ref new_term) = new_term {
                if new_term.0 != new_term_.0 {
                    return Err(UnifyErr::ConflictedTerms(new_term.clone(), new_term_));
                }
            }
            else {
                new_term = Some(new_term_);
            }
        }
        
        if !iparams_.is_empty() {
            if iparams.is_empty() {
                iparams.extend(iparams_);
            }
            else if ! iparams.iter().zip(&iparams_).all(|(x,y)| x.0 == y.0) {
                return Err(UnifyErr::ConflictedIParams(iparams, iparams_));
            }
        }
    }

    Ok((new_term, iparams))
}

/*
 * Unify two terms, `a` and `b`, in a context `ctx`.
 * Returns a list of implicit parameter types.
 */
pub(super) fn unify_supported_implicity(
    a: (Rc<Expr>, Loc), b: (Rc<Expr>, Loc),
    next_inferterm_id: &mut InferTermId,
    substs: &mut Vec<Equal>,
    enable_implicit: bool,
)
    -> Result<(Option<(Rc<Expr>, Loc)>, Vec<((Rc<Expr>, Loc), u8)>), UnifyErr>
{
    // todo: 新たな項を返す時は, 位置情報はaとb両方のものをマージして返す

    debug!("Unification in progress... ({} & {})", a.0, b.0);
    debug!("enable_implicit = {}", enable_implicit);
    // debug!("{}", ctx);

    let mut a = a;
    let mut b = b;

    try_subst(&mut a);
    try_subst(&mut b);
    
    if let Expr::App{..} = *b.0 {
        ::std::mem::swap(&mut a, &mut b);
    }
    if let Expr::Pi(..) = *b.0 {
        ::std::mem::swap(&mut a, &mut b);
    }
    if let Expr::Infer{..} = *b.0 {
        ::std::mem::swap(&mut a, &mut b);
    }
    if let Expr::Subst(..) = *b.0 {
        ::std::mem::swap(&mut a, &mut b);
    }
    if let Expr::Equal(..) = *b.0 {
        ::std::mem::swap(&mut a, &mut b);
    }

    let a = a;
    let b = b;

    match *a.0.clone() {
        Expr::Subst(..) => match *b.0 {
            /* Expr::Subst(ref s_b, ref e_b) => {
                unify_subst((*s_a).clone(), (*s_b).clone(), ctx, substs)?;
                unify(e_a.clone(), e_b.clone(), ctx, substs)?;
            }, */
            // _ => substs.push( Equal::Defer(a.clone(), b.clone()) ),
            _ => return Ok((Some(superposition_loc(a.clone(), b.clone(), None)), vec![])),
        },
        Expr::Infer{id: ref id_a} => match *b.0 {
            Expr::Infer{id: ref id_b} if id_a.get() == id_b.get() => (),
            _ => substs.push( Equal::sort(id_a.clone(), b.clone()) ),
        },
        Expr::Pi(InferAbs{A: ref A_a, t: ref t_a}, ia) =>
            match *b.0 {
                Expr::Pi(InferAbs{A: ref A_b, t: ref t_b}, ib) if ia == ib => {
                    unify_typed(A_a.clone(), A_b.clone(), next_inferterm_id, substs, enable_implicit)?;
                    unify_typed(t_a.clone(), t_b.clone(), next_inferterm_id, substs, enable_implicit)?;
                },
                _ => {
                    if !enable_implicit {
                        return Err(UnifyErr::TermStructureMismatched);
                    }

                    debug!("unification with implicity");

                    let ((Ai, ti, i), rest) =
                        if let Expr::Pi(InferAbs{A: ref A_b, t: ref t_b}, ib) = *b.0 {
                            if ia >= ib { ((A_a, t_a, ia), &b) }
                            else { ((A_b, t_b, ib), &a) }
                        }
                        else if ia != 0 {
                            ((A_a, t_a, ia), &b)
                        }
                        else {
                            return Err(UnifyErr::TermStructureMismatched);
                        };
                    
                    let (new_t, mut iparams) =
                        unify_supported_implicity(ti.tower[0].clone(), rest.clone(),
                            next_inferterm_id, substs, true)?;
                    
                    let new_t = new_t.map( |t|
                        InferTypedTerm{tower: vec![t, ti.tower[1].clone()]}
                    ).unwrap_or(ti.clone());
                    
                    iparams.insert(0, (Ai.tower[0].clone(), i));

                    debug!("new term: {}", Rc::new( Expr::Pi(InferAbs{A: Ai.clone(), t: new_t.clone()}, i) ));
                    debug!("iparams: {:#?}", iparams);
                    
                    return Ok((
                        Some((Rc::new( Expr::Pi(InferAbs{A: Ai.clone(), t: new_t}, i) ), None)),
                        iparams
                    ));
                }
            },
        Expr::Const(id_a) => match *b.0 {
            Expr::Const(id_b) if id_a == id_b => (),
            _ => return Err(UnifyErr::TermStructureMismatched),
        },
        Expr::DBI(i) => match *b.0 {
            Expr::DBI(j) if i == j => (),
            _ => return Err(UnifyErr::TermStructureMismatched),
        },
        Expr::Universe => match *b.0 {
            Expr::Universe => (),
            _ => return Err(UnifyErr::TermStructureMismatched),
        },
        Expr::App{s: ref s_a, t: ref t_a, implicity: ia} => match *b.0 {
            Expr::App{s: ref s_b, t: ref t_b, implicity: ib} if ia == ib => {
                unify_typed(s_a.clone(), s_b.clone(), next_inferterm_id, substs, enable_implicit)
                    .map_err( |e| UnifyErr::InApp(Box::new(e)) )?;
                unify_typed(t_a.clone(), t_b.clone(), next_inferterm_id, substs, enable_implicit)
                    .map_err( |e| UnifyErr::InApp(Box::new(e)) )?;
            },
            _ =>
                if ia == 0 {
                    return Err( UnifyErr::InApp(Box::new(UnifyErr::TermStructureMismatched)) );
                }
                else {
                    return unify_supported_implicity(
                        s_a.tower[0].clone(), b.clone(), next_inferterm_id, substs, enable_implicit
                    );
                },
        }
        Expr::Lam(InferAbs{A: ref A_a, t: ref t_a}, ia) => match *b.0 {
            Expr::Lam(InferAbs{A: ref A_b, t: ref t_b}, ib) if ia == ib => {
                unify_typed(A_a.clone(), A_b.clone(), next_inferterm_id, substs, enable_implicit)?;
                unify_typed(t_a.clone(), t_b.clone(), next_inferterm_id, substs, enable_implicit)?;
            },
            _ => return Err(UnifyErr::TermStructureMismatched),
        }
        Expr::Let{..} => unimplemented!(),
        Expr::Case{..} => unimplemented!(),
        Expr::Value(ref v_a) => match *b.0 {
            Expr::Value(ref v_b) =>
                if v_a == v_b {}
                else { return Err(UnifyErr::ValueMismatched(v_a.clone(), v_b.clone())) },
            _ => return Err(UnifyErr::TermStructureMismatched),
        },
        Expr::Equal(..) => (),
    };

    Ok((None, vec![]))
}

fn unify_typed(
    mut a: InferTypedTerm,
    mut b: InferTypedTerm,
    next_inferterm_id: &mut InferTermId,
    substs: &mut Vec<Equal>,
    enable_implicit: bool,
)
    -> Result<(Option<(Rc<Expr>, Loc)>, Option<(Rc<Expr>, Loc)>, Vec<((Rc<Expr>, Loc), u8)>), UnifyErr>
{
    let mut new_term_0 = None;

    let (new_type, iparams_type) =
        unify_supported_implicity(a.tower[1].clone(), b.tower[1].clone(),
            next_inferterm_id, substs, enable_implicit)?;
    if !iparams_type.is_empty() {
        a.tower[0] = insert_implicit_args(a.tower[0].clone(), iparams_type.clone(), next_inferterm_id);
        b.tower[0] = insert_implicit_args(b.tower[0].clone(), iparams_type.clone(), next_inferterm_id);
        new_term_0 = Some(a.tower[0].clone());
    }

    let (new_term_1, iparams_term) =
        unify_supported_implicity(a.tower[0].clone(), b.tower[0].clone(),
            next_inferterm_id, substs, enable_implicit)?;

    Ok((new_type, new_term_0.or(new_term_1), iparams_term))
}

/*
pub(super) fn unify_arity(t: (Rc<Expr>, Loc), s: (Rc<Expr>, Loc), substs: &mut Vec<Equal>)
    -> Result<(), UnifyErr>
{
    if let Expr::Universe = *s.0 {}
    else { unreachable!(); }

    if let Expr::Universe = *t.0 {}
}
*/

#[derive(Clone, PartialEq, Debug)]
pub enum UnifyErr {
    TermStructureMismatched,
    SubstStructureMismatched,
    ValueMismatched(Value, Value),
    InApp(Box<UnifyErr>),
    ConflictedTerms(ExprL, ExprL),
    ConflictedIParams(Vec<(ExprL, u8)>, Vec<(ExprL, u8)>),
}