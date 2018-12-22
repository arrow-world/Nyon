mod ast;
mod parser;
mod lexer;

use combine::*;
use combine::parser::char::*;
use combine::stream::{state::{SourcePosition, State}, easy};

pub fn lex(top_level: &str) -> Result<Vec<lexer::TokenWithPos>, easy::Errors<char, &str, SourcePosition>> {
    lexer::top_level().skip(eof()).easy_parse(State::new(top_level)).map(|x| x.0)
}

/*
<term> ::= <ident> | type | <lit> | _ | \( <expr> \) | $ <expr> &( \) | <lex_lf> )

<expr_let> ::= let sep_by1(<patn_match>, <lex_lf>) in <expr>
<patn_match> ::= <expr> = <expr>

<expr_case> ::= case <expr> of sep_by(<expr> => <expr>, <lex_lf>)

<expr_if> ::= if <expr> then <expr> else <expr>

<expr_tuple> ::= sep_by2(<expr>, \,)

<expr> ::= <expr_tuple> | <expr_arrow> | <expr_primary> | <term>

<expr_typing> ::= chainl2(<expr_typed>, :)
<expr_typed> ::= <expr_abs> | <expr_arrow> | <expr_udi> | <expr_app> | <term>

<expr_udi> ::= sep_by2(<expr_app> | <term>, <lex_op>)
<lex_op> ::= &!(( -> | \\ | : | \, | :: | _ | \( | \) | = | => | $ | # | \(\* | \*\) ) &!<char_op>) <char_op>+

<expr_app> ::= many2(<term>)

<expr_arrow> ::= chainr2(<expr_primary>, ->)

<expr_abs> ::= <expr_lam> | <expr_pi>
<expr_lam> ::= \\ <ident> : (<expr_abs> | <expr_primary>) -> (<expr_abs> | <expr_primary>)
<expr_pi> ::= \( <ident> : <expr> \) -> (<expr_abs> | <expr_primary>)

<expr_primary> ::= <expr_udi> | <expr_app> | <expr_let> | <expr_case> | <expr_if> | <term>

<ident> ::= sep_by(<lex_ident>, ::) <lex_ident>
<lex_ident> ::= &!(<lex_keyword> &!(<alpha>|<digit>|_)) (<digit>|_)* <alpha> (<alpha>|<digit>|_)*
<lex_keyword> ::= type | let | in | case | of | if | then | else | data | infix | infix_prio

<lit> ::= <lex_nat> | <lex_int> | <lex_str>
<lex_nat> ::= <digit>*
<lex_int> ::= (+|-) <digit>*
<lex_str> ::= " ( &!" <any> )* "

<lex_lf> ::= \n | ;

<top_level> ::= sep_by(<statement>, many1(<lex_lf>))
<statement> ::= <def_datatype> | <decl_infix> | <infix_prio>

<def_datatype> ::= data <ident> : <expr_typed> where <ctor_list>
<ctor_list> ::= sep_by(<ident> : <expr_typed>, <lex_lf>)

<decl_infix> ::= infix <ident> <op>
<infix_prio> ::= infix_prio many2(<ident>)

<comment> ::= # (&!\n <any>)* | \(\* ( &!( \*\) ) <any> )* \*\)
*/