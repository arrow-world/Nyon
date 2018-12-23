mod ast;
mod parser;
mod lexer;

use combine::*;
use combine::parser::char::*;
use combine::stream::{state::{SourcePosition, State}, easy};

pub fn lex(top_level: &str) -> Result<Vec<lexer::TokenWithPos>, easy::Errors<char, &str, SourcePosition>> {
    lexer::top_level().skip(eof()).easy_parse(State::new(top_level)).map(|x| x.0)
}

pub fn parse(top_level: &[lexer::Token]) -> Result<ast::TermWithPos, easy::Errors<lexer::Token, &[lexer::Token], usize>> {
    parser::expr().skip(eof()).easy_parse(State::new(top_level)).map(|x| x.0)
}


/*
<term> ::= <ident> | type | <lit> | _ | \( <lfs> <expr> <lfs> \) | $ <lfs> <expr> &( \) | <lex_lf> )

<expr> ::= <expr_typing> | <expr_abs> | <expr_arrow>

<expr_let> ::= let <lfs> sep_by1(<patn_match>, <lex_lf>+) <lfs> in <lfs> <expr>
<patn_match> ::= <expr> <lfs> = <lfs> <expr>

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
<lex_op> ::= &!(( -> | \\ | : | \, | :: | _ | \( | \) | => | $ | # | \(\* | \*\) | \[ | ] ) &!<char_op>)
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

<top_level> ::= sep_by(<statement>, <lex_lf>+)
<statement> ::= <def_datatype> | <decl_infix> | <infix_prio>

<def_datatype> ::= data <lfs> <ident> <lfs> : <lfs> <expr_typer> <lfs> where <lfs> <ctor_list>
<ctor_list> ::= sep_by(<ident> <lfs> : <lfs> <expr_typer>, <lex_lf>+)

<decl_infix> ::= infix <ident> <op>
<infix_prio> ::= infix_prio many2(<ident>)

<comment> ::= # (&!\n <any>)* | \(\* ( &!( \*\) ) <any> )* \*\)
*/