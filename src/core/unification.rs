use super::typechk::*;
use super::explicit_subst::*;
use syntax::Loc;

use std::rc::Rc;

pub(super) fn unify(
    a: (Rc<Expr>, Loc),
    b: (Rc<Expr>, Loc),
    ctx: &InferCtx,
    next_inferterm_id: &mut InferTermId,
    substs: &mut Vec<Equal>,
)
    -> Result<(), UnifyErr>
{
    let (new, iparams) = unify_supported_implicity(a, b, ctx, next_inferterm_id, substs, false)?;
    assert!(new.is_none());
    assert!(iparams.is_empty());
    Ok(())
}

/*
 * Unify two terms, `a` and `b`, in a context `ctx`.
 * Returns a list of implicit parameter types.
 */
pub(super) fn unify_supported_implicity(
    a: (Rc<Expr>, Loc), b: (Rc<Expr>, Loc),
    ctx: &InferCtx,
    next_inferterm_id: &mut InferTermId,
    substs: &mut Vec<Equal>,
    enable_implicit: bool,
)
    -> Result<(Option<(Rc<Expr>, Loc)>, Vec<((Rc<Expr>, Loc), u8)>), UnifyErr>
{
    debug!("Unification in progress... ({} & {})", a.0, b.0);
    debug!("enable_implicit = {}", enable_implicit);
    // debug!("{}", ctx);

    let mut a = a;
    let mut b = b;

    try_subst(&mut a);
    try_subst(&mut b);
    
    if let Expr::Pi(..) = *b.0 {
        ::std::mem::swap(&mut a, &mut b);
    }
    if let Expr::App{..} = *b.0 {
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
        Expr::Subst(ref s_a, ref e_a) => match *b.0 {
            /* Expr::Subst(ref s_b, ref e_b) => {
                unify_subst((*s_a).clone(), (*s_b).clone(), ctx, substs)?;
                unify(e_a.clone(), e_b.clone(), ctx, substs)?;
            }, */
            _ => substs.push( Equal::Defer(a.clone(), b.clone(), ctx.clone()) ),
        },
        Expr::Infer{id: ref id_a} => match *b.0 {
            Expr::Infer{id: ref id_b} if id_a.get() == id_b.get() => (),
            _ => substs.push( Equal::sort(id_a.clone(), b.clone()) ),
        },
        Expr::Pi(InferAbs{A: ref A_a, t: ref t_a}, ia) =>
            match *b.0 {
                Expr::Pi(InferAbs{A: ref A_b, t: ref t_b}, ib) if ia == ib => {
                    unify_typed(A_a.clone(), A_b.clone(), ctx, next_inferterm_id, substs, enable_implicit)?;
                    unify_typed(t_a.clone(), t_b.clone(), ctx, next_inferterm_id, substs, enable_implicit)?;
                },
                _ =>
                    if enable_implicit {
                        unimplemented!();
                    }
                    else {
                        return Err(UnifyErr::TermStructureMismatched);
                    },
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
                unify_typed(s_a.clone(), s_b.clone(), ctx, next_inferterm_id, substs, enable_implicit)
                    .map_err( |e| UnifyErr::InApp(Box::new(e)) )?;
                unify_typed(t_a.clone(), t_b.clone(), ctx, next_inferterm_id, substs, enable_implicit)
                    .map_err( |e| UnifyErr::InApp(Box::new(e)) )?;
            },
            _ =>
                if ia == 0 {
                    return Err( UnifyErr::InApp(Box::new(UnifyErr::TermStructureMismatched)) );
                }
                else {
                    return unify_supported_implicity(
                        s_a.tower[0].clone(), b.clone(), ctx, next_inferterm_id, substs, enable_implicit
                    );
                },
        }
        Expr::Lam(InferAbs{A: ref A_a, t: ref t_a}, ia) => match *b.0 {
            Expr::Lam(InferAbs{A: ref A_b, t: ref t_b}, ib) if ia == ib => {
                unify_typed(A_a.clone(), A_b.clone(), ctx, next_inferterm_id, substs, enable_implicit)?;
                unify_typed(t_a.clone(), t_b.clone(), ctx, next_inferterm_id, substs, enable_implicit)?;
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
        Expr::Equal(..) => unreachable!(),
    };

    Ok((None, vec![]))
}

fn unify_typed(
    mut a: InferTypedTerm,
    mut b: InferTypedTerm,
    ctx: &InferCtx,
    next_inferterm_id: &mut InferTermId,
    substs: &mut Vec<Equal>,
    enable_implicit: bool,
)
    -> Result<(Option<(Rc<Expr>, Loc)>, Option<(Rc<Expr>, Loc)>, Vec<((Rc<Expr>, Loc), u8)>), UnifyErr>
{
    let mut new_term_0 = None;

    let (new_type, iparams_type) =
        unify_supported_implicity(a.tower[1].clone(), b.tower[1].clone(),
            ctx, next_inferterm_id, substs, enable_implicit)?;
    if !iparams_type.is_empty() {
        a.tower[0] = insert_implicit_args(a.tower[0].clone(), iparams_type.clone(), next_inferterm_id);
        b.tower[0] = insert_implicit_args(b.tower[0].clone(), iparams_type.clone(), next_inferterm_id);
        new_term_0 = Some(a.tower[0].clone());
    }

    let (new_term_1, iparams_term) =
        unify_supported_implicity(a.tower[0].clone(), b.tower[0].clone(),
            ctx, next_inferterm_id, substs, enable_implicit)?;

    Ok((new_type, new_term_0.or(new_term_1), iparams_term))
}

fn unify_subst(s: Subst, t: Subst,
    ctx: &InferCtx, next_inferterm_id: &mut InferTermId, equals: &mut Vec<Equal>) -> Result<(), UnifyErr>
{
    match (s, t) {
        (Subst::Shift(m), Subst::Shift(n)) if m == n => (),
        (Subst::Dot(e_a, s_a), Subst::Dot(e_b, s_b)) => {
            unify_subst((*s_a).clone(), (*s_b).clone(), ctx, next_inferterm_id, equals)?;
            unify(e_a, e_b, ctx, next_inferterm_id, equals)?;
        },
        _ => return Err(UnifyErr::SubstStructureMismatched),
    }
    Ok(())
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

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum UnifyErr {
    TermStructureMismatched,
    SubstStructureMismatched,
    ValueMismatched(Value, Value),
    InApp(Box<UnifyErr>),
}