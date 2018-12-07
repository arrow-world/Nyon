use std::fmt;
use std::rc::Rc;
use std::cell::RefCell;

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Term {
    Idx(u64),
    Universe(u64),
    Pi(Rc<RefCell<Term>>, Rc<RefCell<Term>>),
    Lambda(Rc<RefCell<Term>>, Rc<RefCell<Term>>),
    App(Rc<RefCell<Term>>, Rc<RefCell<Term>>),
}

pub fn substitute(s: &Rc<RefCell<Term>>, i: u64, t: &Term) -> bool {
    if let Term::Idx(j) = *s.borrow() {
        if j == i { *s.borrow_mut() = t.clone(); true }
        else { false }
    }
    else {
        match *s.borrow() {
            Term::Pi(ref _A, ref B) => substitute(B, i+1, t),
            Term::Lambda(ref _A, ref M) => substitute(M, i+1, t),
            Term::App(ref M, ref N) => substitute(M, i, t) || substitute(N, i, t),
            _ => false,
        }
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Term::Idx(i) => write!(f, "#{}", i),
            Term::Universe(i) => write!(f, "Type[{}]", i),
            Term::Pi(A, B) => write!(f, "Π0:{}.{}", A.borrow(), B.borrow()),
            Term::Lambda(A, t) => write!(f, "λ0:{}.{}", A.borrow(), t.borrow()),
            Term::App(t0, t1) => write!(f, "{} {}", t0.borrow(), t1.borrow()),
        }
    }
}

pub fn beta_contract(M: &Rc<RefCell<Term>>, N: &Term) -> bool {
    substitute(M, 0, N)
}

/* #[derive(Clone, PartialEq, Eq, Debug)]
pub enum Binder {
    Lambda(Term),
    Pi(Term),
}
impl fmt::Display for Binder {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
        }
    }
} */

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Context(Vec<Rc<RefCell<Term>>>);
impl Context {
    pub fn new() -> Self {
        Context(Vec::new())
    }

    fn push(&mut self, t: Rc<RefCell<Term>>) {
        self.0.push(t);
    }

    pub fn ty(&self, i: u64) -> Option<Rc<RefCell<Term>>> {
        if i >= self.0.len() as u64 { None }
        else { Some(self.0[self.0.len() - i as usize].clone()) }
    }
}
impl Extend<Rc<RefCell<Term>>> for Context {
    fn extend<T: IntoIterator<Item=Rc<RefCell<Term>>>>(&mut self, iter: T) { self.0.extend(iter) }
}

/* pub fn cow<T: Clone, U, F: FnOnce(&mut T) -> U>(data: &Rc<T>, f: F) -> (Rc<T>, U) {
    let new = data.clone();
    let result = f( Rc::make_mut(&mut new) );
    (new, result)
}

pub fn cow_dyn<T, U, F: FnOnce(&mut Rc<T>) -> U>(data: &mut Rc<T>, f: F) -> (&mut Rc<T>, U) {
    (data, f(data))
} */

pub fn cow<T: Clone, U, F: FnOnce(&mut T) -> U>(data: &T, f: F) -> (T, U) {
    let mut new = data.clone();
    let ret = f(&mut new);
    ( new, ret )
}

pub fn infer_type(ctx: &Context, t: &Term) -> Result<Rc<RefCell<Term>>, InferTypeErr> {
    match t {
        Term::Idx(i) =>
            if let Some(ty) = ctx.ty(*i) { Ok(ty.clone()) }
            else { Err(InferTypeErr::OutOfDeBruijnIndex(*i)) },
        Term::Universe(i) => Ok(Rc::new(RefCell::new( Term::Universe(i+1) ))),
        Term::Pi(A, B) =>
            {
                let k1 = infer_universe(ctx, &A.borrow())?;
                let k2 = infer_universe(ctx, &B.borrow())?;
                Ok(Rc::new(RefCell::new( Term::Universe(k1.max(k2)) )))
            },
        Term::Lambda(A, M) =>
            {
                let B = infer_type(&cow(ctx, |x| x.push(A.clone())).0, &M.borrow())?;
                Ok(Rc::new(RefCell::new( Term::Pi(A.clone(), B) )))
            },
        Term::App(M, N) =>
            {
                let (_A, B) = infer_pi(ctx, &M.borrow())?;
                beta_contract(&B, &N.borrow());
                Ok(B)
            },
    }
}

pub fn infer_universe(ctx: &Context, t: &Term) -> Result<u64, InferUniverseErr> {
    if let Term::Universe(i) = normalize(&ctx, &mut infer_type(ctx, t)?).map(|_| t)? { Ok(*i) }
    else { Err(InferUniverseErr::TypeExpected) }
}

pub fn infer_pi(ctx: &Context, e: &Term) -> Result<(Rc<RefCell<Term>>, Rc<RefCell<Term>>), InferPiErr> {
    let typeof_e = infer_type(ctx, e)?;
    normalize(ctx, &typeof_e)?;
    if let Term::Pi(A, B) = RefCell::clone(&typeof_e).into_inner() { Ok((A, B)) }
    else { Err(InferPiErr::NotAbsTerm) }
}

pub fn normalize(ctx: &Context, t: &Rc<RefCell<Term>>) -> NormalizeResult {
    match t.borrow().clone() {
        Term::Pi(ref A, ref B) =>
            match normalize_abs(ctx, A, B) {
                Ok((A_norm, B_norm)) => Ok(NormalizeOk { rewrited: A_norm.rewrited || B_norm.rewrited }),
                Err(e) => Err(NormalizeErr::AtPi(e)),
            },
        Term::App(ref M, ref N) =>
            {
                let M_norm = normalize(ctx, M)?;
                let N_norm = normalize(ctx, N)?;
                if M_norm.rewrited {
                    beta_contract(M, &N.borrow());
                    normalize(ctx, M)?;
                    *t.borrow_mut() = M.borrow().clone();
                    Ok(NormalizeOk { rewrited: true })
                }
                else { Ok(NormalizeOk { rewrited: M_norm.rewrited || N_norm.rewrited }) }
            },
        _ => Ok(NormalizeOk { rewrited: false }),
    }
}

pub type NormalizeResult = Result<NormalizeOk, NormalizeErr>;
pub struct NormalizeOk {
    rewrited: bool,
}
pub enum NormalizeErr {
    AtPi(NormalizeAbsErr),
}

pub fn normalize_abs(ctx: &Context, A: &Rc<RefCell<Term>>, M: &Rc<RefCell<Term>>) -> NormalizeAbsResult {
    let A_norm = match normalize(ctx, A) {
        Ok(x) => x,
        Err(e) => return Err(NormalizeAbsErr::AtSourceType(Rc::new(e))),
    };
    let M_norm = match normalize(&cow(ctx, |x| x.push(A.clone())).0, M) {
        Ok(x) => x,
        Err(e) => return Err(NormalizeAbsErr::AtBinded(Rc::new(e))),
    };
    Ok((A_norm, M_norm))
}

pub type NormalizeAbsResult = Result<NormalizeAbsOk, NormalizeAbsErr>;
pub type NormalizeAbsOk = (NormalizeOk, NormalizeOk);
pub enum NormalizeAbsErr {
    AtSourceType(Rc<NormalizeErr>),
    AtBinded(Rc<NormalizeErr>),
}

pub enum InferTypeErr {
    OutOfDeBruijnIndex(u64),
    InferUniverseErr(InferUniverseErr),
    InferPiErr(InferPiErr),
}
impl From<InferUniverseErr> for InferTypeErr {
    fn from(e: InferUniverseErr) -> Self {
        InferTypeErr::InferUniverseErr(e)
    }
}
impl From<InferPiErr> for InferTypeErr {
    fn from(e: InferPiErr) -> Self {
        InferTypeErr::InferPiErr(e)
    }
}

pub enum InferUniverseErr {
    TypeExpected,
    InferTypeErr(Rc<InferTypeErr>),
    NormalizeErr(NormalizeErr),
}
impl From<InferTypeErr> for InferUniverseErr {
    fn from(e: InferTypeErr) -> Self {
        InferUniverseErr::InferTypeErr(Rc::new(e))
    }
}
impl From<NormalizeErr> for InferUniverseErr {
    fn from(e: NormalizeErr) -> Self {
        InferUniverseErr::NormalizeErr(e)
    }
}

pub enum InferPiErr {
    NotAbsTerm,
    InferTypeErr(Rc<InferTypeErr>),
    NormalizeErr(NormalizeErr),
}
impl From<InferTypeErr> for InferPiErr {
    fn from(e: InferTypeErr) -> Self {
        InferPiErr::InferTypeErr(Rc::new(e))
    }
}
impl From<NormalizeErr> for InferPiErr {
    fn from(e: NormalizeErr) -> Self {
        InferPiErr::NormalizeErr(e)
    }
}
