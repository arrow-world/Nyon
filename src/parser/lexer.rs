use combine::*;
use combine::parser::char::*;
use combine::stream::{state::{SourcePosition, State}, easy};

pub enum Token {
    Ident{s: String},
    Keyword{kw: Keyword},
    Sep{sep: Sep},
    Op{op: Op},
    Lit{lit: Lit},
}

pub enum Keyword {
    Case,
    Let,
    Universe,
}

pub enum Sep {
    OpenParen,
    CloseParen,
}

pub enum Op {
    Arrow,
    Typing,
    Tuple,
    Domain,
    DeBruijnIndex,
    Hole,
    UserDef{s: String},
}

pub enum Lit {
    Nat{n: ::num::BigInt},
    Int{i: ::num::BigInt},
    Str{s: String},
}