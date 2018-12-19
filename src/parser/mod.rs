mod ast;
mod term;
mod lexer;

use combine::*;
use combine::parser::char::*;
use combine::stream::{state::{SourcePosition, State}, easy};

use self::ast::*;
use self::term::*;

pub fn parse_term(t: &str) -> Result<Term, easy::Errors<char, &str, SourcePosition>> {
    token_sep().with(term()).skip(token_sep()).skip(eof()).easy_parse(State::new(t)).map(|x| x.0)
}

fn pre_ident<I>() -> impl Parser<Input = I, Output = String>
    where I: Stream<Item = char>,
          I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    use std::iter::{FromIterator, once};
    let us = || token('_');

    not_followed_by(string("let").or(string("case")).or(string("in")).or(string("of")))
        .with((many::<String,_>(digit().or(us())), letter(), many::<String, _>(alpha_num().or(us()))))
        .map( |(sl,ch,sr)| String::from_iter( sl.chars().chain(once(ch)).chain(sr.chars())))
}

fn ident<I>() -> impl Parser<Input = I, Output = Ident>
    where I: Stream<Item = char>,
          I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    many::<Vec<String>,_>(attempt(pre_ident().skip(string("::")))).and(pre_ident())
        .map(|(domain, name)| Ident{domain: Domain(domain), name})
}

fn nat<I>() -> impl Parser<Input = I, Output = ::num::BigInt>
    where I: Stream<Item = char>,
          I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    let digits = many1::<String, _>(digit());
    digits.map(|ds| ::num::Num::from_str_radix(&ds, 10).unwrap())
}

fn int<I>() -> impl Parser<Input = I, Output = ::num::BigInt>
    where I: Stream<Item = char>,
          I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    let sign = optional(token('+').or(token('-')));
    sign.and(nat()).map(|(s, n): (Option<char>, ::num::BigInt)| if s == Some('-') {-n} else {n})
}

fn str<I>() -> impl Parser<Input = I, Output = String>
    where I: Stream<Item = char>,
          I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    use combine::error::Consumed;

    token('"').with(many::<String, _>( satisfy(|s| s != '"').then(|c| {
        parser(move |input|
            if c == '\\' {
                satisfy(|s| s == '\\' || s == '"' || s == 'n').map(|d| match d {
                    '\\' | '"' => d,
                    'n' => '\n',
                    _ => unreachable!()
                }).parse_stream(input)
            }
            else {
                Ok((c, Consumed::Empty(())))
            }
        )
    }) )).skip(token('"'))
}

fn tuple<I>() -> impl Parser<Input = I, Output = Vec<Term>>
    where I: Stream<Item = char, Position = SourcePosition>,
          I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    many::<Vec<Term>,_>(term().skip(spaces().skip(token(',')).skip(spaces()))).and(optional(term()))
        .map( |(mut ts, t)| {
            if let Some(t) = t {
                ts.push(t);
            }
            ts
        } )
}

fn op<I>() -> impl Parser<Input = I, Output = Op>
    where I: Stream<Item = char, Position = SourcePosition>,
          I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    use unicode_categories::UnicodeCategories;

    not_followed_by(string(".").or(string("=")).or(string("=>")).or(string(";")))
        .with( many1::<String, _>(satisfy(|c:char| c.is_punctuation_other() || c.is_symbol_math() )) )
        .map(|s| Op(s))
}

fn token_sep_char<I>() -> impl Parser<Input = I, Output = char>
    where I: Stream<Item = char, Position = SourcePosition>,
          I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    newline().or(crlf()).or(space())
}

fn token_sep<I>() -> impl Parser<Input = I, Output = ()>
    where I: Stream<Item = char, Position = SourcePosition>,
          I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    many( token_sep_char().with(value(())) )
}

fn token_sep1<I>() -> impl Parser<Input = I, Output = ()>
    where I: Stream<Item = char, Position = SourcePosition>,
          I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    many1( token_sep_char().with(value(())) )
}

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