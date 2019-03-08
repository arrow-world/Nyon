use syntax::Loc;
use syntax::loc_range;
use super::ast;
use super::lexer;
use super::ext;

use combine::*;
use combine::stream::{state::State, easy};

pub fn parse_env(top_level: &[lexer::Token])
    -> Result<ast::Env, easy::Errors<lexer::Token, &[lexer::Token], usize>>
{
    env(-1).skip(eof()).easy_parse(State::new(top_level)).map(|x| x.0)
}

fn env_<I>(indent_lvl: i64) -> impl Parser<Input = I, Output = ast::Env>
    where I: Stream<Item = lexer::Token, Position = usize>,
          I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    let comma = lexer::Token::Sep(lexer::Sep::Comma);

    let def_datatype = move |indent_lvl: i64|
        token(lexer::Token::Keyword(lexer::Keyword::Datatype)).skip(lfs())
        .with(expr(indent_lvl))
        .and(compound(|inner_indent_lvl| expr(inner_indent_lvl), indent_lvl, lexer::Token::Op(lexer::Op::VertialBar)))
        .map(|(header, ctors)| ast::Statement::Datatype{header, ctors: ctors.into_iter().map(|(t, _loc)| t).collect()});
    
    /* let def_infix = || token(lexer::Token::Keyword(lexer::Keyword::Infix)).skip(lfs())
        .with(userdefop()).skip(lfs())
        .and(ident())
        .map(|(op, name)| ast::Statement::DefInfix{op, name});
    
    let infix_prio = || token(lexer::Token::Keyword(lexer::Keyword::InfixPrio)).skip(lfs())
        .with(ident())
        .and(many(lfs().with(ident())))
        .map(|(head,tail)| ast::Statement::InfixPrio{head,tail}); */

    let statement = move |indent_lvl: i64| choice((
        attempt( def_datatype(indent_lvl) ),
        // attempt( def_infix() ),
        // attempt( infix_prio() ),
        attempt( def(indent_lvl) ).map(|(l,r)| ast::Statement::Def(l,r)),
        attempt( typing(indent_lvl) ).map(|t| ast::Statement::Typing(t)),
    ));

    compound(move |inner_indent_lvl| statement(inner_indent_lvl), indent_lvl, comma).map(|ss| ast::Env(ss))
}
parser! {
    pub fn env[I](indent_lvl: i64)(I) -> ast::Env where [I: Stream<Item = lexer::Token, Position = usize>] {
        env_(*indent_lvl)
    }
}

pub(super) fn compound<I, O, F, P>(mut p: F, indent_lvl: i64, sep: lexer::Token)
    -> impl Parser<Input = I, Output = Vec<(O, Loc)>>
    where I: Stream<Item = lexer::Token, Position = usize>,
          I::Error: ParseError<I::Item, I::Range, I::Position>,
          O: Clone,
          F: FnMut(i64) -> P,
          P: Parser<Input = I, Output = O>,
{
    let mut body = move |inner_indent_lvl| sep_end_by(
        (
            position(),
            p(inner_indent_lvl),
            position(),
        ).map( |(start, body, end)| (body, loc_range(start, end)) ),
        token(sep.clone()).with(lfs())
    );

    optional(body(indent_lvl)).and(optional(
        look_ahead(indent()).then( move |inner_indent_lvl| {
            if inner_indent_lvl <= indent_lvl {
                return unexpected("indent").message("inner indent level is not deeper than outer.")
                    .with(value(Vec::new())).right();
            }

            many(indent_fix(inner_indent_lvl).with(body(inner_indent_lvl))).left()
        })
    ))
        .map(|(head, tail):(Option<Vec<(O, Loc)>>, Option<Vec<Vec<(O, Loc)>>>)|
            head.into_iter().chain(tail.into_iter().flatten()).flatten().collect())
}

fn expr_app<I>(indent_lvl: i64) -> impl Parser<Input = I, Output = ast::TermWithLoc>
    where I: Stream<Item = lexer::Token, Position = usize>,
          I::Error: ParseError<I::Item, I::Range, I::Position>
{
    chainl1( term(indent_lvl),
        value(())
            .map( |_| |f: ast::TermWithLoc, x: ast::TermWithLoc| ast::TermWithLoc {
                start: f.start, end: x.end,
                term: Box::new(ast::Term::App{f,x}),
            } )
    )
}

fn expr_udi<I>(indent_lvl: i64) -> impl Parser<Input = I, Output = ast::Term>
    where I: Stream<Item = lexer::Token, Position = usize>,
          I::Error: ParseError<I::Item, I::Range, I::Position>
{
    /* expr_app().and(many(attempt(lfs().with(userdefop()).skip(lfs()).and(expr_app()))))
        .map( |(head, tail):(_, Vec<_>)| {
            if tail.is_empty() { *head.term }
            else { ast::Term::Infix(ast::Infix{head,tail}) }
        } ) */
    expr_app(indent_lvl).map(|x| *x.term)
}

fn typing<I>(indent_lvl: i64) -> impl Parser<Input = I, Output = ast::Typing>
    where I: Stream<Item = lexer::Token, Position = usize>,
          I::Error: ParseError<I::Item, I::Range, I::Position>
{
    (position(), expr_udi(indent_lvl), position())
        .skip(lfs()).skip(token(lexer::Token::Op(lexer::Op::Typing))).skip(lfs())
            .map(|(start, t, end)| ast::TermWithLoc{term: Box::new(t), start, end})
        .and(expr_typer(indent_lvl))
        .map(|(x,T)| ast::Typing{x,T})
}

fn def<I>(indent_lvl: i64) -> impl Parser<Input = I, Output = (ast::TermWithLoc, ast::TermWithLoc)>
    where I: Stream<Item = lexer::Token, Position = usize>,
          I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    expr_app(indent_lvl).skip(lfs()).skip(token(lexer::Token::Op(lexer::Op::Def))).skip(lfs()).and(expr(indent_lvl))
}

fn term<I>(indent_lvl: i64) -> impl Parser<Input = I, Output = ast::TermWithLoc>
    where I: Stream<Item = lexer::Token, Position = usize>,
          I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    choice((
        (position(), choice((
            attempt( ident().map(|i| ast::Term::Ident(i)) ),
            attempt( token(lexer::Token::Keyword(lexer::Keyword::Type)).map(|_| ast::Term::Universe) ),
            attempt( token(lexer::Token::Op(lexer::Op::Question)).with(optional(ident()))
                .map(|i| ast::Term::Hole(i)) ),
            attempt( ext::ext_term(indent_lvl).map(|et| ast::Term::Ext(et)) ),
        )), position()).map(|(start, t, end)| ast::TermWithLoc{term: Box::new(t), start, end}),
        attempt(
            token(lexer::Token::Sep(lexer::Sep::OpenParen)).skip(lfs())
            .with(expr(indent_lvl)).skip(lfs())
            .skip(token(lexer::Token::Sep(lexer::Sep::CloseParen)))
        ),
        attempt(
            token(lexer::Token::Sep(lexer::Sep::Dollar)).skip(lfs())
            .with(expr(indent_lvl))
            .skip(look_ahead( indent().with(value(()))
                .or(token(lexer::Token::Sep(lexer::Sep::Comma)).with(value(()))).or(eof()) ))
        ),
    ))
}

fn expr_typer<I>(indent_lvl: i64) -> impl Parser<Input = I, Output = ast::TermWithLoc>
    where I: Stream<Item = lexer::Token, Position = usize>,
          I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    choice((
        attempt(expr_abs(indent_lvl)),
        attempt(expr_arrow(indent_lvl)),
    ))
}

fn expr_abs<I>(indent_lvl: i64) -> impl Parser<Input = I, Output = ast::TermWithLoc>
    where I: Stream<Item = lexer::Token, Position = usize>,
          I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    let expr_lam = || token(lexer::Token::Op(lexer::Op::Backslash)).skip(lfs()).with(ident()).skip(lfs())
        .skip(token(lexer::Token::Op(lexer::Op::Typing))).skip(lfs()).and(expr_primary(indent_lvl)).skip(lfs())
        .skip(token(lexer::Token::Op(lexer::Op::Arrow))).skip(lfs()).and(expr(indent_lvl))
        .map(|((x,A),t)| ast::Term::Lam{x,A,t});
    
    let expr_pi = || token(lexer::Token::Sep(lexer::Sep::OpenParen)).skip(lfs()).with(ident()).skip(lfs())
        .skip(token(lexer::Token::Op(lexer::Op::Typing))).skip(lfs()).and(expr(indent_lvl)).skip(lfs())
        .skip(token(lexer::Token::Sep(lexer::Sep::OpenParen))).skip(lfs())
        .skip(token(lexer::Token::Op(lexer::Op::Arrow))).skip(lfs()).and(expr(indent_lvl))
        .map(|((x,A),B)| ast::Term::Pi{x,A,B});
    
    (position(), choice(( attempt(expr_lam()), attempt(expr_pi()) )), position())
        .map(|(start, t, end)| ast::TermWithLoc{term: Box::new(t), start, end})
}

fn expr_arrow<I>(indent_lvl: i64) -> impl Parser<Input = I, Output = ast::TermWithLoc>
    where I: Stream<Item = lexer::Token, Position = usize>,
          I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    chainr1(expr_primary(indent_lvl),
        attempt(lfs().skip(token(lexer::Token::Op(lexer::Op::Arrow))).skip(lfs()))
            .map(|_| |A: ast::TermWithLoc, B: ast::TermWithLoc|
                ast::TermWithLoc {
                    start: A.start, end: B.end,
                    term: Box::new(ast::Term::Arrow{A,B}),
                }
            )
        )
}

fn expr_primary<I>(indent_lvl: i64) -> impl Parser<Input = I, Output = ast::TermWithLoc>
    where I: Stream<Item = lexer::Token, Position = usize>,
          I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    let expr_let = || token(lexer::Token::Keyword(lexer::Keyword::Let))
        .with(env(indent_lvl)).skip(lfs())
        .skip(token(lexer::Token::Keyword(lexer::Keyword::In))).skip(lfs())
        .and(expr(indent_lvl))
        .map(|(env, body)| ast::Term::Let{env, body});
    
    let expr_case = || token(lexer::Token::Keyword(lexer::Keyword::Case)).skip(lfs())
        .with(expr(indent_lvl)).skip(lfs())
        .skip(token(lexer::Token::Keyword(lexer::Keyword::Of)))
        .and( compound(
            move |inner_indent_lvl|
                expr(inner_indent_lvl).skip(lfs()).skip(token(lexer::Token::Op(lexer::Op::Matcher))).skip(lfs())
                    .and(expr(inner_indent_lvl)).map(|(patn, t)| ast::Arm{patn,t}),
            indent_lvl,
            lexer::Token::Sep(lexer::Sep::Comma),
        ) )
        .map(|(t, arms)| ast::Term::Case{t, arms});
    
    let expr_if = || (
        token(lexer::Token::Keyword(lexer::Keyword::If)).skip(lfs()).with(expr(indent_lvl)).skip(lfs()),
        token(lexer::Token::Keyword(lexer::Keyword::Then)).skip(lfs()).with(expr(indent_lvl)).skip(lfs()),
        token(lexer::Token::Keyword(lexer::Keyword::Else)).skip(lfs()).with(expr(indent_lvl))
    ).map(|(p,tv,fv)| ast::Term::If{p,tv,fv});

    (position(), choice((
        attempt( expr_udi(indent_lvl) ),
        attempt( expr_let() ),
        attempt( expr_case() ),
        attempt( expr_if() ),
    )), position()).map(|(start, t, end)| ast::TermWithLoc{term: Box::new(t), start, end})
}

fn expr_<I>(indent_lvl: i64) -> impl Parser<Input = I, Output = ast::TermWithLoc>
    where I: Stream<Item = lexer::Token, Position = usize>,
          I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    let expr_typing = || (position(), typing(indent_lvl), position())
        .map(|(start, t, end)| ast::TermWithLoc{start, end, term: Box::new(ast::Term::Typing(t))});

    choice((
        attempt( expr_typing() ),
        attempt( expr_abs(indent_lvl) ),
        attempt( expr_arrow(indent_lvl) ),
    ))
}
parser! {
    pub fn expr[I](indent_lvl: i64)(I) -> ast::TermWithLoc where [I: Stream<Item = lexer::Token, Position = usize>] {
        expr_(*indent_lvl)
    }
}

fn ident<I>() -> impl Parser<Input = I, Output = ast::Ident>
    where I: Stream<Item = lexer::Token, Position = usize>,
          I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    let lex = || satisfy_map(|t| if let lexer::Token::Ident(s) = t {Some(s)} else {None});
    (
        position(),
        many(attempt( lex().skip(token(lexer::Token::Op(lexer::Op::Dot))) )).and(lex()),
        position(),
    ).map(|(start, (dns, name), end)| ast::Ident{domain: dns, name, loc: loc_range(start, end)})
}

fn indent<I>() -> impl Parser<Input = I, Output = i64> 
    where I: Stream<Item = lexer::Token>,
          I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    satisfy_map(|t| if let lexer::Token::Indent{lvl} = t { Some(lvl as i64) } else { None })
}

fn indent_fix<I>(indent_lvl: i64) -> impl Parser<Input = I, Output = ()> 
    where I: Stream<Item = lexer::Token>,
          I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    satisfy(move |t| if let lexer::Token::Indent{lvl} = t { lvl as i64 == indent_lvl } else { false }).with(value(()))
}

pub(super) fn lfs<I>() -> impl Parser<Input = I, Output = ()> 
    where I: Stream<Item = lexer::Token>,
          I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    skip_many(indent())
}