mod ast;
mod term;
mod lexer;

use combine::*;
use combine::parser::char::*;
use combine::stream::{state::{SourcePosition, State}, easy};

use self::ast::*;
use self::term::*;

/*
<term> ::= <ident> | <lit> | _ | \( <expr> \) | $ <expr> &( \) | <lex_lf> )

<expr_let> ::= let sep_by1(<patn_match>, <lex_lf>) in <expr>
<patn_match> ::= <expr> = <expr>

<expr_case> ::= case <expr> of sep_by(<expr> => <expr>, <lex_lf>)

<expr_if> ::= if <expr> then <expr> opt(else <expr>)

<expr_tuple> ::= sep_by2(<expr>, \,)

<expr> ::= <expr_tuple> | <expr_arrow> | <expr_primary> | <term>

<expr_typing> ::= chainl2(<expr_typed>, :)
<expr_typed> ::= <expr_abs> | <expr_arrow> | <expr_udi> | <expr_app> | <term>

<expr_udi> ::= sep_by2(<expr_app> | <term>, <lex_op>)
<lex_op> ::= &!(( -> | \\ | : | \, | \( | \) | = | => | $ | # | \(\* | \*\) ) &!<char_op>) <char_op>+

<expr_app> ::= many2(<term>)

<expr_arrow> ::= chainr2(<expr_primary>, ->)

<expr_abs> ::= <expr_lam> | <expr_pi>
<expr_lam> ::= \\ <ident> : (<expr_abs> | <expr_primary>) -> (<expr_abs> | <expr_primary>)
<expr_pi> ::= \( <ident> : <expr> \) -> (<expr_abs> | <expr_primary>)

<expr_primary> ::= <expr_udi> | <expr_app> | <expr_let> | <expr_case> | <expr_if> | <term>

<ident> ::= sep_by(<lex_ident>, ::) <lex_ident>
<lex_ident> ::= &!(<lex_keyword> &!(<alpha>|<digit>|_)) (<digit>|_)* <alpha> (<alpha>|<digit>|_)*
<lex_keyword> ::= type | let | in | case | of | if | then | else

<lit> ::= <lex_nat> | <lex_int> | <lex_str> | <lex_universe>
<lex_nat> ::= <digit>*
<lex_int> ::= (+|-) <digit>*
<lex_str> ::= " ( &!" <any> )* "
<lex_universe> ::= type

<lex_lf> ::= \n | ;

<top_level> ::= sep_by(<statement>, <lex_lf>)
<statement> ::= <def_datatype> | <decl_infix> | 

<def_datatype> ::= data <ident> : <expr_typed> where <ctor_list>
<ctor_list> ::= sep_by(<ident> : <expr_typed>, <lex_lf>)

<decl_infix> ::= infix <ident> <op>
<infix_prio> ::= infix_prio many2(<ident>)

<comment> ::= # (&!\n <any>)* | \(\* ( &!( \*\) ) <any> )* \*\)
*/