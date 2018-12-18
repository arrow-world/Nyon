use combine::stream::state::SourcePosition;
use std::fmt;

#[derive(Clone, Debug)]
pub enum TermWithoutPos {
    Var(Ident),
    Universe,
    DBI(::num::BigInt),
    App{f: Term, x: Term},
    Pi{x: Ident, A: Term, B: Term},
    Arrow{A: Term, B: Term},
    Infix(Infix),
    Typing(Typing),
    Let{patn:Term, t: Term, u: Term},
    Abs{x: Ident, A: Term, t: Term},
    Case{t: Term, arms: Vec<Arm>},
    Literal(Literal),
    Hole,
}
impl fmt::Display for TermWithoutPos {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            TermWithoutPos::Var(i) => write!(f, "{}", i),
            TermWithoutPos::Universe => write!(f, "type"),
            TermWithoutPos::DBI(n) => write!(f, "@{}", n),
            TermWithoutPos::App{f:_f,x} => write!(f, "({} {})", _f, x),
            TermWithoutPos::Pi{x,A,B} => write!(f, "Π({}:{}){}", x, A, B),
            TermWithoutPos::Arrow{A,B} => write!(f, "({} -> {})", A, B),
            TermWithoutPos::Infix(i) => write!(f, "({})", i),
            TermWithoutPos::Typing(ty) => write!(f, "({})", ty),
            TermWithoutPos::Let{patn, t, u} => write!(f, "(let {} = {} in {})", patn, t, u),
            TermWithoutPos::Abs{x,A,t} => write!(f, "(λ{}:{}.{})", x, A, t),
            TermWithoutPos::Case{t, arms} => {
                write!(f, "(case {} of ", t)?;
                for i in 0..arms.len() {
                    write!(f, "{}", arms[i])?;
                    if i < arms.len()-1 { write!(f, "; ")?; }
                }
                write!(f, ")")
            },
            TermWithoutPos::Literal(lit) => write!(f, "{}", lit),
            TermWithoutPos::Hole => write!(f, "_"),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Term {
    pub term: Box<TermWithoutPos>,
    pub start: SourcePosition,
    pub end: SourcePosition,
}
impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:}", self.term)
    }
}

#[derive(Clone, Debug)]
pub struct Domain(pub Vec<String>);

#[derive(Clone, Debug)]
pub struct Ident {
    pub domain: Domain,
    pub name: String,
}
impl fmt::Display for Ident {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for domain_name in &self.domain.0 {
            write!(f, "{}::", domain_name)?;
        }
        write!(f, "{}", self.name)
    }
}

#[derive(Clone, Debug)]
pub struct Op(pub String);

#[derive(Clone, Debug)]
pub struct Infix {
    pub head: Term,
    pub tail: Vec<(Op, Term)>,
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
    pub patn: Term,
    pub t: Term,
}
impl fmt::Display for Arm {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} => {}", self.patn, self.t)
    }
}

#[derive(Clone, Debug)]
pub struct Typing {
    pub x: Term,
    pub T: Term,
}
impl fmt::Display for Typing {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}:{}", self.x, self.T)
    }
}

#[derive(Clone, Debug)]
pub enum Literal {
    Nat(::num::BigInt),
    Int(::num::BigInt),
    Str(String),
    Tuple{head: Term, tail: Vec<Term>},
}
impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Literal::Nat(n) => write!(f, "{}", n),
            Literal::Int(i) => write!(f, "{:+}", i),
            Literal::Str(s) => write!(f, "{}", s),
            Literal::Tuple{head,tail} => {
                write!(f, "({:},", head)?;
                for i in 0..tail.len() {
                    write!(f, " {:}", tail[i])?;
                    if i < tail.len()-1 { write!(f, ",")?; }
                }
                write!(f, ")")
            },
        }
    }
}

pub enum Statement {
    Data{ident: IdentDef, T: Term, ctors: Vec<Ctor>},
    Typing(Typing),
    Let{patn: Term, t: Term},
    InfixPrio{infixs: Vec<Ident>}
}

pub enum IdentDef {
    Ident(Ident),
    Infix{name: Ident, ops: Vec<Op>},
}

pub struct Ctor {
    ident: IdentDef,
    T: Term,
}