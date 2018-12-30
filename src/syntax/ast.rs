use std::fmt;
use std::rc::Rc;

#[derive(Clone, Debug)]
pub enum Term {
    Ident(Ident),
    Universe,
    App{f: TermWithPos, x: TermWithPos},
    Pi{x: Ident, A: TermWithPos, B: TermWithPos},
    Arrow{A: TermWithPos, B: TermWithPos},
    // Infix(Infix),
    Typing(Typing),
    Let{env: Env, body: TermWithPos},
    Lam{x: Ident, A: TermWithPos, t: TermWithPos},
    Case{t: TermWithPos, arms: Vec<Arm>},
    If{p: TermWithPos, tv: TermWithPos, fv: TermWithPos},
    Lit(Lit),
    Hole,
}
impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Term::Ident(i) => write!(f, "{}", i),
            Term::Universe => write!(f, "type"),
            Term::App{f:_f,x} => write!(f, "({} {})", _f, x),
            Term::Pi{x,A,B} => write!(f, "Π({}:{}){}", x, A, B),
            Term::Arrow{A,B} => write!(f, "({} -> {})", A, B),
            // Term::Infix(i) => write!(f, "({})", i),
            Term::Typing(ty) => write!(f, "({})", ty),
            Term::Let{env, body} => write!(f, "(let {} in {})", env, body),
            Term::Lam{x,A,t} => write!(f, "(λ{}:{}.{})", x, A, t),
            Term::Case{t, arms} => {
                write!(f, "(case {} of ", t)?;
                for i in 0..arms.len() {
                    write!(f, "{}", arms[i])?;
                    if i < arms.len()-1 { write!(f, "; ")?; }
                }
                write!(f, ")")
            },
            Term::If{p, tv, fv} => write!(f, "(if {} then {} else {})", p, tv, fv),
            Term::Lit(lit) => write!(f, "{}", lit),
            Term::Hole => write!(f, "_"),
        }
    }
}

#[derive(Clone, Debug)]
pub struct TermWithPos {
    pub term: Box<Term>,
    pub start: usize,
    pub end: usize,
}
impl fmt::Display for TermWithPos {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:}", self.term)
    }
}

#[derive(Clone, Debug)]
pub struct Ident {
    pub domain: Vec<String>,
    pub name: String,
}
impl fmt::Display for Ident {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for domain_name in &self.domain {
            write!(f, "{}::", domain_name)?;
        }
        write!(f, "{}", self.name)
    }
}

#[derive(Clone, Debug)]
pub struct Op(pub String);

#[derive(Clone, Debug)]
pub struct Infix {
    pub head: TermWithPos,
    pub tail: Vec<(Op, TermWithPos)>,
}
impl fmt::Display for Infix {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.head)?;
        for (op, t) in &self.tail {
            write!(f, " {} {}", op.0, t)?;
        }
        Ok(())
    }
}

#[derive(Clone, Debug)]
pub struct Arm {
    pub patn: TermWithPos,
    pub t: TermWithPos,
}
impl fmt::Display for Arm {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} => {}", self.patn, self.t)
    }
}

#[derive(Clone, Debug)]
pub struct Typing {
    pub x: TermWithPos,
    pub T: TermWithPos,
}
impl fmt::Display for Typing {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}:{}", self.x, self.T)
    }
}

#[derive(Clone, Debug)]
pub enum Lit {
    Nat(::num::BigInt),
    Int(::num::BigInt),
    Str(String),
    Tuple(Vec<TermWithPos>),
}
impl fmt::Display for Lit {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Lit::Nat(n) => write!(f, "{}", n),
            Lit::Int(i) => write!(f, "{:+}", i),
            Lit::Str(s) => write!(f, "{}", s),
            Lit::Tuple(es) => {
                write!(f, "[")?;
                for i in 0..es.len() {
                    write!(f, "{:}", es[i])?;
                    if i < es.len()-1 { write!(f, ", ")?; }
                }
                write!(f, "]")
            },
        }
    }
}

#[derive(Clone, Debug)]
pub struct Env(pub Vec<Statement>);
impl fmt::Display for Env {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let Env(stats) = self;
        for i in 0..stats.len() {
            write!(f, "{}", stats[i])?;
            if i < stats.len()-1 { write!(f, "; ")?; }
        }
        Ok(())
    }
}

#[derive(Clone, Debug)]
pub struct Module {
    pub env: Env,
    pub name: String,
    pub parents: Vec<Rc<Module>>,
    pub children: Vec<Rc<Module>>,
}

#[derive(Clone, Debug)]
pub enum Statement {
    Data{ident: Ident, T: TermWithPos, ctors: Vec<Ctor>},
    // DefInfix{op: Op, name: Ident},
    // InfixPrio{head: Ident, tail: Vec<Ident>},
    Def(TermWithPos, TermWithPos),
    Typing(Typing),
}
impl fmt::Display for Statement {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Statement::Data{ident, T, ctors} => {
                write!(f, "data {} : {} where (", ident, T)?;
                for i in 0..ctors.len() {
                    let ref ctor = ctors[i];
                    write!(f, "{} : {}", ctor.patn, ctor.T)?;
                    if i < ctors.len()-1 { write!(f, "; ")?; }
                }
                write!(f, ")")
            },
            // Statement::DefInfix{op: Op(op), name} => write!(f, "infix {} {}", op, name),
            /* Statement::InfixPrio{head, tail} => {
                write!(f, "infix_prio {}", head)?;
                for x in tail { write!(f, " {}", x)?; }
                Ok(())
            }, */
            Statement::Def(l,r) => write!(f, "{} := {}", l, r),
            Statement::Typing(Typing{x,T}) => write!(f, "{} : {}", x, T),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Ctor {
    pub patn: Ident,
    pub T: TermWithPos,
}