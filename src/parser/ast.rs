use combine::stream::PointerOffset;
use combine::stream::state::SourcePosition;
use std::fmt;

#[derive(Clone, Debug)]
pub enum Term {
    Var(Ident),
    Universe,
    App{f: TermWithPos, x: TermWithPos},
    Pi{x: Ident, A: TermWithPos, B: TermWithPos},
    Arrow{A: TermWithPos, B: TermWithPos},
    Infix(Infix),
    Typing(Typing),
    Let{decs: Vec<(TermWithPos, TermWithPos)>, body: TermWithPos},
    Abs{x: Ident, A: TermWithPos, t: TermWithPos},
    Case{t: TermWithPos, arms: Vec<Arm>},
    Literal(Literal),
    Hole,
}
impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Term::Var(i) => write!(f, "{}", i),
            Term::Universe => write!(f, "type"),
            Term::App{f:_f,x} => write!(f, "({} {})", _f, x),
            Term::Pi{x,A,B} => write!(f, "Π({}:{}){}", x, A, B),
            Term::Arrow{A,B} => write!(f, "({} -> {})", A, B),
            Term::Infix(i) => write!(f, "({})", i),
            Term::Typing(ty) => write!(f, "({})", ty),
            Term::Let{decs, body} => {
                write!(f, "(let ")?;
                for i in 0..decs.len() {
                    let (ref lhs, ref rhs) = decs[i];
                    write!(f, "{} = {}", lhs, rhs)?;
                    if i < decs.len()-1 { write!(f, "; ")?; }
                }
                write!(f, " in {})", body)
            },
            Term::Abs{x,A,t} => write!(f, "(λ{}:{}.{})", x, A, t),
            Term::Case{t, arms} => {
                write!(f, "(case {} of ", t)?;
                for i in 0..arms.len() {
                    write!(f, "{}", arms[i])?;
                    if i < arms.len()-1 { write!(f, "; ")?; }
                }
                write!(f, ")")
            },
            Term::Literal(lit) => write!(f, "{}", lit),
            Term::Hole => write!(f, "_"),
        }
    }
}

#[derive(Clone, Debug)]
pub struct TermWithPos {
    pub term: Box<Term>,
    pub start: SourcePosition,
    pub end: SourcePosition,
}
impl fmt::Display for TermWithPos {
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
pub enum Literal {
    Nat(::num::BigInt),
    Int(::num::BigInt),
    Str(String),
    Tuple{head: TermWithPos, tail: Vec<TermWithPos>},
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
    Data{ident: IdentDef, T: TermWithPos, ctors: Vec<Ctor>},
    Typing(Typing),
    Let{patn: TermWithPos, t: TermWithPos},
    InfixPrio{infixs: Vec<Ident>}
}

pub enum IdentDef {
    Ident(Ident),
    Infix{name: Ident, ops: Vec<Op>},
}

pub struct Ctor {
    ident: IdentDef,
    T: TermWithPos,
}