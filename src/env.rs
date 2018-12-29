use super::syntax::ast;
use idgen::IdGen;
use std::collections::HashMap;
use std::rc::Rc;

pub type DataTypeId = u64;
pub type ConstId = u64;
pub type ModuleId = u64;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Ident {
    module: ModuleId,
    name: String,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Module {
    names: HashMap<ConstId, String>,
    ids: HashMap<String, ConstId>,
    env: Env,
}
impl Module {
    pub fn new() -> Self {
        Module {
            names: HashMap::new(),
            ids: HashMap::new(),
            env: Env::new(),
        }
    }

    pub fn builtin() -> Self {
        let mut m: Module = Default::default();
        let mut idgen = IdGen::new();
        m.add_const(idgen.gen(), "Nat".into());
        m.add_const(idgen.gen(), "Int".into());
        m.add_const(idgen.gen(), "Unicode".into());
        m
    }

    pub fn add_const(&mut self, id: ConstId, name: String) {
        self.names.insert(id.clone(), name.clone());
        self.ids.insert(name, id);
    }
}
impl Default for Module {
    fn default() -> Self { Module::new() }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Env {
    datatypes: Vec<DataType>,
    defs: Vec<Rc<Term>>,
    typings: Vec<(Rc<Term>, Rc<Term>)>,
}
impl Env {
    pub fn new() -> Self {
        Env {
            datatypes: Vec::new(),
            defs: Vec::new(),
            typings: Vec::new(),
        }
    }

    pub fn extend(&mut self, other: Env) {
        self.datatypes.extend(other.datatypes.into_iter());
        self.defs.extend(other.defs.into_iter());
        self.typings.extend(other.typings.into_iter());
    }
}
impl Default for Env {
    fn default() -> Self { Env::new() }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Ctx {
    global: Env,
    local: Vec<Rc<Term>>,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct DataType {
    ctors_type: Vec<Rc<Term>>,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Term {
    Const(ConstId),
    DBI(u64),
    Universe(Option<u64>),
    App{s: Rc<Term>, t: Rc<Term>},
    Lam{A: Rc<Term>, t: Rc<Term>},
    Pi{A: Rc<Term>, B: Rc<Term>},
    Let(Env, Rc<Term>),
    Case(Rc<Term>, Vec<(Rc<Term>, Rc<Term>)>),
    Typing{x: Rc<Term>, T: Rc<Term>},
    Nat(::num::BigInt),
    Int(::num::BigInt),
    Str(String),
    Tuple(Vec<Rc<Term>>),
}

pub fn subst(s: Rc<Term>, i: u64, t: Rc<Term>) -> Rc<Term> {
    match *s.clone() {
        Term::DBI(j) if i == j => t,
        Term::App{s: ref M, t: ref N} =>
            Rc::new(Term::App{s: subst(M.clone(), i, t.clone()), t: subst(N.clone(), i, t)}),
        Term::Lam{ref A, t: ref M} => Rc::new(Term::Lam{A: A.clone(), t: subst(M.clone(), i+1, t)}),
        Term::Pi{ref A, ref B} => Rc::new(Term::Pi{A: A.clone(), B: subst(B.clone(), i+1, t)}),
        Term::Let(ref env, ref M) => Rc::new(Term::Let(
            Env {
                datatypes:
                    env.datatypes.iter().map( |datatype|
                        DataType {
                            ctors_type:
                                datatype.ctors_type.iter()
                                    .map(|ctor_type| subst(ctor_type.clone(), i, t.clone())).collect()
                        }
                    ).collect(),
                defs:
                    env.defs.iter().map(|def| subst(def.clone(), i, t.clone())).collect(),
                typings:
                    env.typings.iter().map( |(M, T)|
                        (subst(M.clone(), i, t.clone()), subst(T.clone(), i, t.clone()))
                    ).collect(),
            },
            subst(M.clone(), i, t),
        )),
        Term::Case(ref M, ref arms) => {
            let arms = arms.iter()
                .map(|(patn, N)| (subst(patn.clone(), i, t.clone()), subst(N.clone(), i, t.clone()))).collect();
            Rc::new(Term::Case(subst(M.clone(), i, t), arms))
        },
        Term::Typing{ref x, ref T} =>
            Rc::new(Term::Typing{x: subst(x.clone(), i, t.clone()), T: subst(T.clone(), i, t)}),
        Term::Tuple(ref ts) =>
            Rc::new(Term::Tuple( ts.iter().map(|M| subst(M.clone(), i, t.clone())).collect() )),
        _ => s,
    }
}

pub fn norm(ctx: &Ctx, t: Rc<Term>) -> Rc<Term> {
    match *t.clone() {
        Term::Const(id) => ctx.global.defs[id as usize].clone(),
        Term::DBI(i) => ctx.local[i as usize].clone(),
        Term::App{ref s, ref t} => {
            let s = norm(ctx, s.clone());
            let t = norm(ctx, t.clone());
            if let Term::Lam{A, t: M} = (*s).clone() {
                let M = subst(M, 0, t);
                norm(ctx, M)
            }
            else { t }
        },
        Term::Lam{ref A, ref t} => {
            let (A, t) = norm_abs(ctx, A.clone(), t.clone());
            Rc::new(Term::Lam{A, t})
        },
        Term::Pi{ref A, ref B} => {
            let (A, B) = norm_abs(ctx, A.clone(), B.clone());
            Rc::new(Term::Pi{A, B})
        },
        Term::Let(ref env, ref M) => {
            let mut ctx = ctx.clone();
            ctx.global.extend(env.clone());
            norm(&ctx, M.clone())
        },
        Term::Case(ref M, ref arms) => {
            let M = norm(ctx, M.clone());
            for (patn, N) in arms {
                let patn = norm(ctx, patn.clone());
            }
            unimplemented!()
        },
        Term::Tuple(ref ts) => Rc::new(Term::Tuple( ts.iter().map(|M| norm(ctx, M.clone())).collect() )),
        Term::Typing{..} => unreachable!(),
        _ => t,
    }
}

pub fn norm_abs(ctx: &Ctx, A: Rc<Term>, t: Rc<Term>) -> (Rc<Term>, Rc<Term>) {
    let mut ctx_t = ctx.clone();
    ctx_t.local.push(A.clone());
    (norm(ctx, A), norm(&ctx_t, t))
}