use std::collections::HashMap;
use std::rc::Rc;

pub type ConstId = u64;
pub type ConstTypeId = u64;

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Term {
    Const(ConstId),
    Abs(Abs),
    App(Rc<Term>, Rc<Term>),
}

pub type TypeInferenceResult = Result<Type, TypeInferenceError>; 
pub type TypeInferenceError = ();

pub fn type_infer_global(E: &GlobalContext, t: &Term) -> TypeInferenceResult {
    match t {
        Term::Const(id) => E.get(*id).ok_or(()),
        Term::Abs(Abs(A, M)) => type_infer_local(E, &LocalContext(vec![A.clone()]), &M)
            .map(|B| Type::function(A.clone(), B)),
        Term::App(M, N) =>
            type_infer_global(E, &M).and_then(|ty| match ty {
                Type::Function(sigma, tau) =>
                    {
                        type_infer_global(E, &N).and_then( |rho|
                            if rho == *sigma { Ok((*tau).clone()) }
                            else { Err(()) }
                        )
                    },
                _ => Err(()),
            }),
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Type {
    Function(Rc<Type>, Rc<Type>),
    Const(ConstTypeId),
}
impl Type {
    pub fn function(sour: Type, tar: Type) -> Self {
        Type::Function(Rc::new(sour), Rc::new(tar))
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum GlobalDef {
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct GlobalContext {
    decls: HashMap<ConstId, Type>,
    defs: HashMap<ConstId, GlobalDef>,
}
impl GlobalContext {
    pub fn new() -> Self {
        GlobalContext {
            decls: HashMap::new(),
            defs: HashMap::new(),
        }
    }

    pub fn get(&self, id: ConstId) -> Option<Type> {
        self.decls.get(&id).cloned()
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct LocalContext(Vec<Type>);
impl LocalContext {
    pub fn new() -> Self {
        LocalContext(Vec::new())
    }

    pub fn append(mut self, A: Type) -> Self {
        self.0.push(A);
        self
    }

    fn get(&self, de_bruijn_index: u64) -> Option<Type> {
        let LocalContext(G) = self;
        if de_bruijn_index >= (G.len() as u64) { None }
        else { Some( G[G.len() - 1 - de_bruijn_index as usize].clone() ) }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Abs(Type, Rc<AbsTerm>);
impl Abs {
    pub fn new(A: Type, M: AbsTerm) -> Self {
        Abs(A, Rc::new(M))
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum AbsTerm {
    Abs(Abs),
    App(Rc<AbsTerm>, Rc<AbsTerm>),
    Idx(u64),
    Const(ConstId),
}
impl AbsTerm {
    pub fn substitute(self, i: u64, N: &AbsTerm) -> AbsTerm {
        match self {
            AbsTerm::Abs(Abs(ty, term)) =>
                AbsTerm::Abs(Abs::new(ty, (*term).clone().substitute(i+1, N))),
            AbsTerm::App(M2, N2) =>
                AbsTerm::App(
                    Rc::new((*M2).clone().substitute(i, &N)),
                    Rc::new((*N2).clone().substitute(i, &N)),
                ),
            AbsTerm::Idx(j) => if j == i { N.clone() } else { self },
            AbsTerm::Const(id) => self,
        }
    }

    pub fn beta_reduce(self, N: &AbsTerm) -> AbsTerm {
        match self {
            AbsTerm::Abs(Abs(ty, term)) => (*term).clone().substitute(0, N),
            _ => self,
        }
    }

    pub fn eta_convert(self) -> AbsTerm {
        fn shift(M: AbsTerm) -> AbsTerm {
            match M {
                AbsTerm::Idx(i) => AbsTerm::Idx(i-1),
                _ => M,
            }
        }

        if let AbsTerm::Abs(Abs(ty, term)) = &self {
            if let AbsTerm::App(ref M, ref N) = **term {
                if !M.is_occur(0) && **N == AbsTerm::Idx(0) { return shift((**M).clone()); }
            }
        }

        return self;
    }

    pub fn is_occur(&self, i: u64) -> bool {
        match self {
            AbsTerm::Abs(Abs(ty, term)) => term.is_occur(i+1),
            AbsTerm::App(M, N) => M.is_occur(i) || N.is_occur(i),
            AbsTerm::Idx(j) => *j == i,
            AbsTerm::Const(id) => false,
        }
    }
}
impl From<Term> for AbsTerm {
    fn from(t: Term) -> Self {
        match t {
            Term::Abs(abs) => AbsTerm::Abs(abs),
            Term::App(M, N) => AbsTerm::App( Rc::new((*M).clone().into()), Rc::new((*N).clone().into()) ),
            Term::Const(id) => AbsTerm::Const(id),
        }
    }
}

pub fn type_infer_local(E: &GlobalContext, G: &LocalContext, t: &AbsTerm) -> TypeInferenceResult {
    match t {
        AbsTerm::Abs(Abs(A, M)) => type_infer_local(E, G, M).map(|B| Type::function(A.clone(), B)),
        AbsTerm::App(M, N) =>
            type_infer_local(E, G, &M).and_then(|ty| match ty {
                Type::Function(sigma, tau) =>
                    {
                        type_infer_local(E, G, &N).and_then( |rho|
                            if rho == *sigma { Ok((*tau).clone()) }
                            else { Err(()) }
                        )
                    },
                _ => Err(()),
            }),
        AbsTerm::Idx(i) => G.get(*i).ok_or(()),
        AbsTerm::Const(id) => E.get(*id).ok_or(()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    pub fn typing_check_id_fn() {
        let nat = Type::Const(0);
        let id_nat = Term::Abs(Abs::new(nat.clone(), AbsTerm::Idx(0)));
        assert_eq!(
            type_infer_global(&GlobalContext::new(), &id_nat).unwrap(),
            Type::function(nat.clone(), nat.clone())
        );
    }

    #[test]
    pub fn beta_reduction() {
        let nat = Type::Const(0);
        let id_nat: AbsTerm = Term::Abs(Abs::new(nat.clone(), AbsTerm::Idx(0))).into();
        let zero = AbsTerm::Const(0);
        assert_eq!(
            id_nat.beta_reduce(&zero),
            zero
        );
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct BuiltinFunction(Type, Type, fn(Term) -> Term);

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Function {
    Builtin(BuiltinFunction),
    Lambda(Abs),
}
impl From<BuiltinFunction> for Function {
    fn from(f: BuiltinFunction) -> Self { Function::Builtin(f) }
}
impl From<Abs> for Function {
    fn from(f: Abs) -> Self { Function::Lambda(f) }
}