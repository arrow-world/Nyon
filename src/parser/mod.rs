mod ast;
mod term;
mod lexer;

use combine::*;
use combine::parser::char::*;
use combine::stream::{state::{SourcePosition, State}, easy};

use self::ast::*;
use self::term::*;

/*
<pre_ident> ::= (<alnum>|_)* <alpha> (<alnum>|_)*
<ident> ::= <pre_ident>(::<pre_ident>)*
<dbi> ::= @<nat>
<typing> ::= <term> : <term>
<term> ::= <ident> | type | <dbi> | <term> <term> | <term> -> <term> | (<ident>:<term>) -> <term> | <infix>
    | <typing> | let <term> = <term> in <term> | \<ident>:<term> -> <term> | case <term> of <arm_list>
    | (<term>) | <term> $ <term> | _ | <literal>

<term_alpha(byident:<ident>)> ::=
    type |
    \( <ident>:<term> \) -> <term> |
    let (<term> = <term(byident: "in")> <lf>)+ in <term> |
    \\ <ident>:<term> -> <term> |
    case <term(byident: "of")> of (<term(byop: "=>")> => <term> <lf>)* |
    _ |
    <nat> |
    <int> |
    <str> |
    !byident <ident> |
    \( <term> \) |
    $ <term> &( <lf> | \) ) |

<arrow_tail(byop, byident)> ::= -> <term(byop: byop | op_arrow, byident)> <arrow_tail>
<typing_tail(byop, byident)> ::= : <term(byop: byop | op_typing, byident) <typing_tail>
<tuple_tail(byop, byident)> ::= , <term(byop: byop | op_tuple, byident)> <tuple_tail>

<term_tail(byop, byident)> ::=
    !byop (
        <arrow_tail(byop, byident)> |
        <typing_tail(byop, byident)> |
        <tuple_tail(byop, byident)>
    )

<infix(byop, byident)> ::=
    seqby1( <term_alpha(byop, byident)> <term_tail(byop, byident)> , !byop <op> )

<term(byop = !ε, byident = !ε)> ::=
    chainl1( <infix(byop, byident)>, ε )

<term> ::=
    type <term_tail> |
    <ident> <term_tail> |
    <dbi> <term_tail> |
    ( <ts> <ident> <ts> : <ts> <term_with_app> <ts> ) <ts> -> <ts> <term_with_app> <term_tail> |
    let <ts> <term_with_app> <ts> = <ts> <term_with_app> <ts> in <ts> <term_with_app> <term_tail> |
    \\ <ts> <ident> <ts> : <ts> <term'_with_app> <ts> -> <ts> <term_with_app> <term_tail> |
    case <ts> <term_with_app> <ts> of (<ts> <term_with_app> <ts> => <ts> <term_with_app> <lf>)* <term_tail> |
    _ <term_tail> |
    <literal> <term_tail> |
    ( <ts> <term_with_app> <ts> ) <term_tail> |
    $ <ts> <term_with_app> &(\) | <lf>) <term_tail> |
<term_tail> ::=
    ε |
    (<ts> <op> <ts> <term_with_app>)+ <term_tail> |
    <ts> -> <ts> <term_with_app> <term_tail> |
    <ts> : <ts> <term_with_app> <term_tail> |
    <ts> , (<ts> <term_with_app> <ts> ,)* opt(<ts> <term_with_app>) <term_tail> |
<term_with_app> ::= chainl1(<term>, <sp>)

<term'> ::=
    type <term'_tail> |
    <ident> <term'_tail> |
    <dbi> <term'_tail> |
    let <ts> <term'_with_app> <ts> = <ts> <term'_with_app> <ts> in <ts> <term'_with_app> <term'_tail> |
    case <ts> <term'_with_app> <ts> of (<ts> <term'_with_app> <ts> => <ts> <term'_with_app> <lf>)* <term'_tail> |
    _ <term'_tail> |
    <literal> <term'_tail> |
    ( <ts> <term_with_app> <ts> ) <term'_tail> |
    $ <ts> <term_with_app> &(\) | <lf>) <term'_tail> |
<term'_tail> ::=
    ε |
    <ts> : <ts> <term'_with_app> <term'_tail> |
    (<ts> <op> <ts> <term'_with_app>)+ <term'_tail> |
    <ts> , (<ts> <term'_with_app> <ts> ,)* opt(<ts> <term'_with_app>) <term'_tail> |
<term'_with_app> ::= chainl1(<term'>)

<infix> ::= <term> <op> <infix_list>
<infix_list> ::= <term> | <term> <op> <infix_list>
<infix_prio> = infix_prio <ident>+

<arm_list> ::= <arm> | <arm> <lf> <arm_list>
<arm> ::= <term> => <term>

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
<tuple> ::= <term> , (<term> ,)* opt(<term>)
*/