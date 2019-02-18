use super::typechk::*;
use super::explicit_subst::*;

use std::rc::Rc;

/*
 * Unify two terms, `a` and `b`, in a context `ctx`.
 */
pub(super) fn unify(a: Rc<Expr>, b: Rc<Expr>, ctx: &InferCtx, substs: &mut Vec<Equal>) -> Result<(), UnifyErr> {
    debug!("Unification in progress... ({} & {})", a, b);
    // debug!("{}", ctx);

    let mut a = a;
    let mut b = b;

    try_subst(&mut a);
    try_subst(&mut b);

    if let Expr::Infer{..} = *b {
        ::std::mem::swap(&mut a, &mut b);
    }
    if let Expr::Subst(..) = *b {
        ::std::mem::swap(&mut a, &mut b);
    }

    let a = a;
    let b = b;

    match *a.clone() {
        Expr::Subst(ref s_a, ref e_a) => match *b {
            /* Expr::Subst(ref s_b, ref e_b) => {
                unify_subst((*s_a).clone(), (*s_b).clone(), ctx, substs)?;
                unify(e_a.clone(), e_b.clone(), ctx, substs)?;
            }, */
            _ => substs.push( Equal::Defer(a.clone(), b.clone(), ctx.clone()) ),
        },
        Expr::Infer{id: ref id_a} => match *b {
            Expr::Infer{id: ref id_b} if id_a.get() == id_b.get() => (),
            _ => substs.push( Equal::sort(id_a.clone(), b.clone()) ),
        },
        Expr::Const(id_a) => match *b {
            Expr::Const(id_b) if id_a == id_b => (),
            _ => return Err(UnifyErr::TermStructureMismatched),
        },
        Expr::DBI(i) => match *b {
            Expr::DBI(j) if i == j => (),
            _ => return Err(UnifyErr::TermStructureMismatched),
        },
        Expr::Universe => match *b {
            Expr::Universe => (),
            _ => return Err(UnifyErr::TermStructureMismatched),
        },
        Expr::App{s: ref s_a, t: ref t_a} => match *b {
            Expr::App{s: ref s_b, t: ref t_b} => {
                unify_typed(s_a.clone(), s_b.clone(), ctx, substs).map_err( |e| UnifyErr::InApp(Box::new(e)) )?;
                unify_typed(t_a.clone(), t_b.clone(), ctx, substs).map_err( |e| UnifyErr::InApp(Box::new(e)) )?;
            },
            _ => return Err( UnifyErr::InApp(Box::new(UnifyErr::TermStructureMismatched)) ),
        }
        Expr::Lam(InferAbs{A: ref A_a, t: ref t_a}) => match *b {
            Expr::Lam(InferAbs{A: ref A_b, t: ref t_b}) => {
                unify_typed(A_a.clone(), A_b.clone(), ctx, substs)?;
                unify_typed(t_a.clone(), t_b.clone(), ctx, substs)?;
            },
            _ => return Err(UnifyErr::TermStructureMismatched),
        }
        Expr::Pi(InferAbs{A: ref A_a, t: ref t_a}) => match *b {
            Expr::Pi(InferAbs{A: ref A_b, t: ref t_b}) => {
                unify_typed(A_a.clone(), A_b.clone(), ctx, substs)?;
                unify_typed(t_a.clone(), t_b.clone(), ctx, substs)?;
            }
            _ => return Err(UnifyErr::TermStructureMismatched),
        },
        Expr::Let{..} => unimplemented!(),
        Expr::Case{..} => unimplemented!(),
        Expr::Value(ref v_a) => match *b {
            Expr::Value(ref v_b) =>
                if v_a == v_b {}
                else { return Err(UnifyErr::ValueMismatched(v_a.clone(), v_b.clone())) },
            _ => return Err(UnifyErr::TermStructureMismatched),
        },
    };

    Ok(())
}

fn unify_typed(a: InferTypedTerm, b: InferTypedTerm, ctx: &InferCtx, substs: &mut Vec<Equal>)
    -> Result<(), UnifyErr>
{
    Ok( 
        a.tower.into_iter().zip(b.tower).try_for_each(|(a,b)| unify(a, b, ctx, substs))?
    )
}

fn unify_subst(s: Subst, t: Subst, ctx: &InferCtx, equals: &mut Vec<Equal>) -> Result<(), UnifyErr> {
    match (s, t) {
        (Subst::Shift(m), Subst::Shift(n)) if m == n => (),
        (Subst::Dot(e_a, s_a), Subst::Dot(e_b, s_b)) => {
            unify_subst((*s_a).clone(), (*s_b).clone(), ctx, equals)?;
            unify(e_a, e_b, ctx, equals)?;
        },
        _ => return Err(UnifyErr::SubstStructureMismatched),
    }
    Ok(())
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum UnifyErr {
    TermStructureMismatched,
    SubstStructureMismatched,
    ValueMismatched(Value, Value),
    InApp(Box<UnifyErr>),
}