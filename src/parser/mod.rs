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

/*
<lex_ident> ::= &!(type | let | in | case | of) (<digit>|_)* <alpha> (<alnum>|_)*
<ident> ::= <lex_ident> ( :: <lex_ident>)*
<dbi> ::= @<nat>
<typing> ::= <term> : <term>
<term> ::= <ident> | type | <dbi> | <term> <term> | <term> -> <term> | (<ident>:<term>) -> <term> | <infix>
    | <typing> | let <term> = <term> in <term> | \\ <ident>:<term> -> <term> | case <term> of <arm_list>
    | (<term>) | <term> $ <term> | _ | <literal>

<infix> ::= <term> <op> <infix_list>
<infix_list> ::= <term> | <term> <op> <infix_list>
<infix_prio> = infix_prio <ident>+

<arm_list> ::= <arm> | <arm> <lf> <arm_list>
<arm> ::= <term> => <term>

<term> ::= <ident> | type | <dbi> | \( <expr> \) | $ <expr> &( \) | <lf> ) | | _ | <literal>
<lam_expr> ::= \\ <ident> : <term> -> <term>
<arrow_expr> ::= <term> -> <term>
<pi_expr> ::= \( <ident> : <arrow_expr> \) -> <lam_expr>
<typing_expr> ::= chainl1( <pi_expr> | <arrow_expr> , : )
<app_expr> ::= chainl1( <term> , ε )
<tuple_expr> ::= sep_by1( <expr>, \, )
<user_def_infix_expr> ::= sep_by1(<term>, &!(->|:|\,|\(|\)|=|$) <op>)

<let_expr> ::= let sep_by1(<patn_match>, <lf>) in <expr>
<patn_match> ::= <expr> = <expr>

<case_expr> ::= case <expr> of sep_by1(<expr> => <expr>, <lf>)

<ident_def> ::= <ident> | infix(<ident>) <infix_def>
<infix_def> ::= _ <op> <infix_def_list>
<infix_def_list> ::= _ | _ <op> <infix_def_list>

<statement> ::= data <ident_def> : <term> where <ctor_list> | <typing> | let <term> = <term> | <infix_prio>

<ctor_list> ::= ϵ | <ctor> <lf> <ctor_list>
<ctor> ::= <ident_def> : <term>

<literal> ::= <nat> | <int> | <string> | <tuple>
<nat> ::= <digits>
<int> ::= (+|-)?<nat>
<string> ::= \"<any>*\"
*/