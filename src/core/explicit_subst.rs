use super::typechk::*;

use std::rc::Rc;

#[derive(Clone, Debug)]
pub(super) enum Subst {
    Shift(usize),
    Dot(Rc<Expr>, Rc<Subst>),
}
impl Subst {
    pub(super) fn compose(self, other: Subst) -> Subst {
        match (self, other) {
            (s, Subst::Shift(0)) => s,
            (Subst::Dot(_e,s), Subst::Shift(m)) => (*s).clone().compose(Subst::Shift(m-1)),
            (Subst::Shift(m), Subst::Shift(n)) => Subst::Shift(m+n),
            (s, Subst::Dot(e,t)) =>
                Subst::Dot( Rc::new(Expr::Subst(s.clone(), e)), Rc::new(s.compose((*t).clone())) ),
        }
    }

    pub(super) fn from_expr(e: Rc<Expr>) -> Subst {
        Subst::Dot(e, Rc::new(Subst::identity()))
    }

    fn is_identity(&self) -> bool {
        if let Subst::Shift(0) = self {
            true
        }
        else { false }
    }

    fn identity() -> Subst {
        Subst::Shift(0)
    }
}

pub(super) fn try_subst(e: &mut Rc<Expr>) {
    debug!("try to substitute {} ...", e);

    if let Expr::Subst(ref s, ref f) = *e.clone() {
        *e = subst((*s).clone(), f.clone());
    }
}

pub(super) fn subst(s: Subst, e: Rc<Expr>) -> Rc<Expr> {
    match (s, (*e).clone()) {
        (Subst::Shift(0), _) => e,
        (Subst::Shift(m), Expr::DBI(k)) => Rc::new(Expr::DBI(k + m)),
        (Subst::Dot(e,s), Expr::DBI(0)) => subst(Subst::identity(), e),
        (Subst::Dot(e,s), Expr::DBI(k)) => subst((*s).clone(), Rc::new(Expr::DBI(k-1))),
        (s, Expr::Pi(a)) => Rc::new(Expr::Pi(subst_abs(s, &a))),
        (s, Expr::Lam(a)) => Rc::new(Expr::Pi(subst_abs(s, &a))),
        (s, Expr::App{s: t, t: u}) => Rc::new( Expr::App {
            s: subst_typed(s.clone(), &t),
            t: subst_typed(s, &u),
        } ),
        (s, Expr::Let{..}) => unimplemented!(),
        (s, Expr::Case{..}) => unimplemented!(),
        (s, Expr::Subst(t, e)) => subst(Subst::compose(s, t), e),
        (s, Expr::Infer{..}) => Rc::new(Expr::Subst(s, e)),
        (s, Expr::Const(..)) => e,
        (s, Expr::Universe) => e,
        (s, Expr::Value(..)) => e,
    }
}

fn subst_abs(s: Subst, a: &InferAbs) -> InferAbs {
    InferAbs {
        A: subst_typed(s.clone(), &a.A),
        t: subst_typed(Subst::Dot(Rc::new(Expr::DBI(0)), Rc::new(Subst::Shift(1).compose(s))), &a.t),
    }
}

fn subst_typed(s: Subst, e: &InferTypedTerm) -> InferTypedTerm {
    InferTypedTerm {
        tower: vec![subst(s.clone(), e.tower[0].clone()), subst(s, e.tower[1].clone())],
    }
}

pub(super) fn subst_typed_lazily(s: Subst, e: InferTypedTerm) -> InferTypedTerm {
    InferTypedTerm {
        tower: e.tower.into_iter().map(|e| Rc::new(Expr::Subst(s.clone(), e))).collect(),
    }
}

/* fn subst(t: &mut Rc<Expr>, dbi: usize, u: Rc<Expr>) {
    if let Expr::DBI(i) = *t.clone() {
        if i == dbi { *Rc::make_mut(t) = (*u).clone(); }
    }
    else {
        match *Rc::make_mut(t) {
            Expr::App{s: ref mut m, t: ref mut n} => {
                subst(&mut m.tower[0], dbi, u.clone());
                subst(&mut n.tower[0], dbi, u);
            },
            Expr::Lam(ref mut abs) => subst_abs(abs, dbi, u),
            Expr::Pi(ref mut abs) => subst_abs(abs, dbi, u),
            Expr::Let{..} => unimplemented!(),
            Expr::Case{..} => unimplemented!(),
            _ => (),
        }
    }

    return;

    fn subst_abs(abs: &mut InferAbs, dbi: usize, u: Rc<Expr>) {
        subst(&mut abs.A.tower[0], dbi, u.clone());
        subst(&mut abs.t.tower[0], dbi+1, u);
    }
}

fn shift(t: &mut Expr, n: usize) {
    match t {
        Expr::DBI(ref mut i) => *i += n,
        Expr::App{ref mut s, ref mut t} => {
            shift_typed(s, n);
            shift_typed(t, n);
        },
        Expr::Lam(abs) => shift_abs(abs, n),
        Expr::Pi(abs) => shift_abs(abs, n),
        Expr::Let{..} => unimplemented!(),
        Expr::Case{..} => unimplemented!(),
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
} */