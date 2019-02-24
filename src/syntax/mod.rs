pub mod ast;
mod lexer;
mod parser;

pub use self::lexer::lex_src;
pub use self::parser::parse_env;

#[derive(Serialize, Deserialize, Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct SourceLocation {
    pub start: usize,
    pub end: usize,
}

pub type Loc = Option<Vec<SourceLocation>>;

pub fn loc(t: &ast::TermWithLoc) -> Loc {
    Some( vec![ SourceLocation {
        start: t.start,
        end: t.end,
    } ] )
}

pub fn loc_range(start: usize, end: usize) -> Loc {
    Some( vec![ SourceLocation { start, end } ] )
}

/* #[derive(Clone, PartialEq, Eq)]
pub enum Error {
    Lex(LexError),
    Parse(ParseError),
}

#[derive(Clone, PartialEq, Eq)]
pub struct LexError {
    pos: SourcePosition,
    unexpected: Vec<easy::Info<char, &str>>,
    expected: Vec<easy::Info<char, &str>>,
}

#[derive(Clone, PartialEq, Eq)]
pub struct ParseError {
    start: SourcePosition,
    end: SourcePosition,
    unexpected: Vec<easy::Info<>
} */

/*
<term> ::= <ident> | type | <lit> | _ | \( <lfs> <expr> <lfs> \) | $ <lfs> <expr> &( \) | <lex_lf> )

<expr> ::= <expr_typing> | <expr_abs> | <expr_arrow>

<expr_let> ::= let <lfs> <env> <lfs> in <lfs> <expr>

<expr_case> ::= case <lfs> <expr> <lfs> of <lfs> sep_by(<expr> <lfs> => <lfs> <expr>, <lex_lf>+)

<expr_if> ::= if <lfs> <expr> <lfs> then <lfs> <expr> <lfs> else <lfs> <expr>

<expr_typing> ::= <expr_udi> <lfs> : <lfs> <expr_typer>
<expr_typer> ::= <expr_abs> | <expr_arrow>

<expr_arrow> ::= chainr1(<expr_primary>, <lfs> -> <lfs> )

<expr_primary> ::= <expr_udi> | <expr_let> | <expr_case> | <expr_if>

<expr_abs> ::= <expr_lam> | <expr_pi>
<expr_lam> ::= \\ <lfs> <ident> <lfs> : <lfs> <expr_primary> <lfs> -> <lfs> <expr>
<expr_pi> ::= \( <lfs> <ident> <lfs> : <lfs> <expr> <lfs> \) <lfs> -> <lfs> <expr>

<expr_udi> ::= sep_by1(<expr_app>, <lfs> <lex_op> <lfs>)
<lex_op> ::= &!(( -> | \\ | : | \, | :: | _ | \( | \) | => | := | $ | # | \(\* | \*\) | [ | ] { | }) &!<char_op>)
    <char_op>+

<expr_app> ::= chainl1(<term>, ε)

<ident> ::= many(<lfs> <lex_ident>, <lfs> ::) <lfs> <lex_ident>
<lex_ident> ::= &!(<lex_keyword> &!(<alpha>|<digit>|_)) (<digit>|_)* <alpha> (<alpha>|<digit>|_)*
<lex_keyword> ::= type | let | in | case | of | if | then | else | data | where | infix | infix_prio

<lit> ::= <lex_nat> | <lex_int> | <lex_str> | <lit_list>
<lex_nat> ::= <digit>*
<lex_int> ::= (+|-) <digit>*
<lex_str> ::= " ( &!" <any> )* "

<lit_list> ::= [ sep_end_by( <lfs> <expr>, <lfs> \, ) <lfs> ]

<lex_lf> ::= \n | ;
<lfs> ::= <lex_lf>*

<env> ::= sep_by(<statement>, <lex_lf>+)
<statement> ::= <def_datatype> | <def_infix> | <infix_prio> | <def> | <expr_typing>

<def_datatype> ::= data <lfs> <ident> <lfs> : <lfs> <expr_typer> <lfs> where <lfs> <ctor_list>
<ctor_list> ::= sep_by(<ident> <lfs> : <lfs> <expr_typer>, <lex_lf>+)

<def_infix> ::= infix <lfs> <op> <lfs> <ident>
<infix_prio> ::= infix_prio <lfs> many2(<ident> <lfs>)

<def> ::= <expr> <lfs> := <lfs> <expr>

<comment> ::= # (&!\n <any>)* | \(\* ( &!( \*\) ) <any> )* \*\)
*/