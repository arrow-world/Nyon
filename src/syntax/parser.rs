use super::ast;
use super::lexer;

use combine::*;

fn env_<I>() -> impl Parser<Input = I, Output = ast::Env>
    where I: Stream<Item = lexer::Token, Position = usize>,
          I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    let ctor = || ident().skip(lfs()).skip(token(lexer::Token::Op(lexer::Op::Typing))).skip(lfs())
        .and(expr_typer())
        .map(|(patn,T)| ast::Ctor{patn,T});

    let def_datatype = || token(lexer::Token::Keyword(lexer::Keyword::Data)).skip(lfs())
        .with(ident()).skip(lfs()).skip(token(lexer::Token::Op(lexer::Op::Typing))).skip(lfs())
        .and(expr_typer()).skip(lfs()).skip(token(lexer::Token::Keyword(lexer::Keyword::Where))).skip(lfs())
        .and(sep_end_by(ctor(), attempt(
            lfs().skip(token(lexer::Token::Sep(lexer::Sep::Line(lexer::LineSep::Semicolon)))).skip(lfs())
                .skip(look_ahead(ctor()))
        )))
        .map(|((ident, T), ctors)| ast::Statement::Data{ident, T, ctors});
    
    /* let def_infix = || token(lexer::Token::Keyword(lexer::Keyword::Infix)).skip(lfs())
        .with(userdefop()).skip(lfs())
        .and(ident())
        .map(|(op, name)| ast::Statement::DefInfix{op, name});
    
    let infix_prio = || token(lexer::Token::Keyword(lexer::Keyword::InfixPrio)).skip(lfs())
        .with(ident())
        .and(many(lfs().with(ident())))
        .map(|(head,tail)| ast::Statement::InfixPrio{head,tail}); */

    let statement = || choice((
        attempt( def_datatype() ),
        // attempt( def_infix() ),
        // attempt( infix_prio() ),
        attempt( def() ).map(|(l,r)| ast::Statement::Def(l,r)),
        attempt( typing() ).map(|t| ast::Statement::Typing(t)),
    ));

    sep_end_by1( statement(),
        attempt( lfs().skip(token(lexer::Token::Sep(lexer::Sep::Line(lexer::LineSep::Semicolon)))).skip(lfs()) )
    )
        .map(|ss| ast::Env(ss))
}
parser! {
    pub fn env[I]()(I) -> ast::Env where [I: Stream<Item = lexer::Token, Position = usize>] {
        env_()
    }
}

fn expr_app<I>() -> impl Parser<Input = I, Output = ast::TermWithPos>
    where I: Stream<Item = lexer::Token, Position = usize>,
          I::Error: ParseError<I::Item, I::Range, I::Position>
{
    chainl1( term(),
        value(())
            .map( |_| |f: ast::TermWithPos, x: ast::TermWithPos| ast::TermWithPos {
                start: f.start, end: x.end,
                term: Box::new(ast::Term::App{f,x}),
            } )
    )
}

fn userdefop<I>() -> impl Parser<Input = I, Output = ast::Op>
    where I: Stream<Item = lexer::Token, Position = usize>,
          I::Error: ParseError<I::Item, I::Range, I::Position>
{
    satisfy_map( |t|
        if let lexer::Token::Op(lexer::Op::UserDef(s)) = t { Some(ast::Op(s)) }
        else { None }
    )
}

fn expr_udi<I>() -> impl Parser<Input = I, Output = ast::Term>
    where I: Stream<Item = lexer::Token, Position = usize>,
          I::Error: ParseError<I::Item, I::Range, I::Position>
{
    /* expr_app().and(many(attempt(lfs().with(userdefop()).skip(lfs()).and(expr_app()))))
        .map( |(head, tail):(_, Vec<_>)| {
            if tail.is_empty() { *head.term }
            else { ast::Term::Infix(ast::Infix{head,tail}) }
        } ) */
    expr_app().map(|x| *x.term)
}

fn typing<I>() -> impl Parser<Input = I, Output = ast::Typing>
    where I: Stream<Item = lexer::Token, Position = usize>,
          I::Error: ParseError<I::Item, I::Range, I::Position>
{
    (position(), expr_udi(), position())
        .skip(lfs()).skip(token(lexer::Token::Op(lexer::Op::Typing))).skip(lfs())
            .map(|(start, t, end)| ast::TermWithPos{term: Box::new(t), start, end})
        .and(expr_typer())
        .map(|(x,T)| ast::Typing{x,T})
}

fn def<I>() -> impl Parser<Input = I, Output = (ast::TermWithPos, ast::TermWithPos)>
    where I: Stream<Item = lexer::Token, Position = usize>,
          I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    expr_app().skip(lfs()).skip(token(lexer::Token::Op(lexer::Op::Def))).skip(lfs()).and(expr())
}

fn term<I>() -> impl Parser<Input = I, Output = ast::TermWithPos>
    where I: Stream<Item = lexer::Token, Position = usize>,
          I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    choice((
        (position(), choice((
            attempt( ident().map(|i| ast::Term::Ident(i)) ),
            attempt( token(lexer::Token::Keyword(lexer::Keyword::Type)).map(|_| ast::Term::Universe) ),
            attempt( lit().map(|lit| ast::Term::Lit(lit)) ),
            attempt( token(lexer::Token::Op(lexer::Op::Hole)).map(|_| ast::Term::Hole) ),
        )), position()).map(|(start, t, end)| ast::TermWithPos{term: Box::new(t), start, end}),
        attempt(
            token(lexer::Token::Sep(lexer::Sep::OpenParen)).skip(lfs())
            .with(expr()).skip(lfs())
            .skip(token(lexer::Token::Sep(lexer::Sep::CloseParen)))
        ),
        attempt(
            token(lexer::Token::Sep(lexer::Sep::Dollar)).skip(lfs())
            .with(expr())
            .skip(look_ahead(token(lexer::Token::Sep(lexer::Sep::CloseParen)).or(lf())
                .or(token(lexer::Token::Sep(lexer::Sep::Line(lexer::LineSep::Semicolon))))))
        ),
    ))
}

fn expr_typer<I>() -> impl Parser<Input = I, Output = ast::TermWithPos>
    where I: Stream<Item = lexer::Token, Position = usize>,
          I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    choice((
        attempt(expr_abs()),
        attempt(expr_arrow()),
    ))
}

fn expr_abs<I>() -> impl Parser<Input = I, Output = ast::TermWithPos>
    where I: Stream<Item = lexer::Token, Position = usize>,
          I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    let expr_lam = || token(lexer::Token::Op(lexer::Op::Lambda)).skip(lfs()).with(ident()).skip(lfs())
        .skip(token(lexer::Token::Op(lexer::Op::Typing))).skip(lfs()).and(expr_primary()).skip(lfs())
        .skip(token(lexer::Token::Op(lexer::Op::Arrow))).skip(lfs()).and(expr())
        .map(|((x,A),t)| ast::Term::Lam{x,A,t});
    
    let expr_pi = || token(lexer::Token::Sep(lexer::Sep::OpenParen)).skip(lfs()).with(ident()).skip(lfs())
        .skip(token(lexer::Token::Op(lexer::Op::Typing))).skip(lfs()).and(expr()).skip(lfs())
        .skip(token(lexer::Token::Sep(lexer::Sep::CloseParen))).skip(lfs())
            .skip(token(lexer::Token::Op(lexer::Op::Arrow))).skip(lfs()).and(expr())
        .map(|((x,A),B)| ast::Term::Pi{x,A,B});
    
    (position(), choice(( attempt(expr_lam()), attempt(expr_pi()) )), position())
        .map(|(start, t, end)| ast::TermWithPos{term: Box::new(t), start, end})
}

fn expr_arrow<I>() -> impl Parser<Input = I, Output = ast::TermWithPos>
    where I: Stream<Item = lexer::Token, Position = usize>,
          I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    chainr1(expr_primary(),
        attempt(lfs().skip(token(lexer::Token::Op(lexer::Op::Arrow))).skip(lfs()))
            .map(|_| |A: ast::TermWithPos, B: ast::TermWithPos|
                ast::TermWithPos {
                    start: A.start, end: B.end,
                    term: Box::new(ast::Term::Arrow{A,B}),
                }
            )
        )
}

fn expr_primary<I>() -> impl Parser<Input = I, Output = ast::TermWithPos>
    where I: Stream<Item = lexer::Token, Position = usize>,
          I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    let expr_let = || token(lexer::Token::Keyword(lexer::Keyword::Let)).skip(lfs())
        .with(env()).skip(lfs())
        .skip(token(lexer::Token::Keyword(lexer::Keyword::In))).skip(lfs())
        .and(expr())
        .map(|(env, body)| ast::Term::Let{env, body});
    
    let expr_case = || token(lexer::Token::Keyword(lexer::Keyword::Case)).skip(lfs())
        .with(expr()).skip(lfs())
        .skip(token(lexer::Token::Keyword(lexer::Keyword::Of))).skip(lfs())
        .and(sep_end_by(
            expr().skip(lfs()).skip(token(lexer::Token::Op(lexer::Op::Matcher))).skip(lfs()).and(expr())
                .map(|(patn, t)| ast::Arm{patn,t}),
            attempt( lfs().skip(token(lexer::Token::Sep(lexer::Sep::Line(lexer::LineSep::Semicolon)))).skip(lfs()) )
        ))
        .map(|(t, arms)| ast::Term::Case{t, arms});
    
    let expr_if = || (
        token(lexer::Token::Keyword(lexer::Keyword::If)).skip(lfs()).with(expr()).skip(lfs()),
        token(lexer::Token::Keyword(lexer::Keyword::Then)).skip(lfs()).with(expr()).skip(lfs()),
        token(lexer::Token::Keyword(lexer::Keyword::Else)).skip(lfs()).with(expr())
    ).map(|(p,tv,fv)| ast::Term::If{p,tv,fv});

    (position(), choice((
        attempt( expr_udi() ),
        attempt( expr_let() ),
        attempt( expr_case() ),
        attempt( expr_if() ),
    )), position()).map(|(start, t, end)| ast::TermWithPos{term: Box::new(t), start, end})
}

fn expr_<I>() -> impl Parser<Input = I, Output = ast::TermWithPos>
    where I: Stream<Item = lexer::Token, Position = usize>,
          I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    let expr_typing = || (position(), typing(), position())
        .map(|(start, t, end)| ast::TermWithPos{start, end, term: Box::new(ast::Term::Typing(t))});

    choice((
        attempt( expr_typing() ),
        attempt( expr_abs() ),
        attempt( expr_arrow() ),
    ))
}
parser! {
    pub fn expr[I]()(I) -> ast::TermWithPos where [I: Stream<Item = lexer::Token, Position = usize>] {
        expr_()
    }
}

fn lit<I>() -> impl Parser<Input = I, Output = ast::Lit>
    where I: Stream<Item = lexer::Token, Position = usize>,
          I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    attempt( satisfy_map( |t| if let lexer::Token::Lit(lit) = t {
            Some( match lit {
                lexer::Lit::Nat(n) => ast::Lit::Nat(n),
                lexer::Lit::Int(i) => ast::Lit::Int(i),
                lexer::Lit::Str(s) => ast::Lit::Str(s),
            } )
        }
        else { None }
    ) ).or(
        token(lexer::Token::Sep(lexer::Sep::OpenBracket)).skip(lfs())
        .with(sep_end_by(expr(), attempt(lfs().skip(token(lexer::Token::Sep(lexer::Sep::Comma))).skip(lfs()))))
        .skip(token(lexer::Token::Sep(lexer::Sep::CloseBracket)))
        .map(|es| ast::Lit::Tuple(es))
    )
}

fn ident<I>() -> impl Parser<Input = I, Output = ast::Ident>
    where I: Stream<Item = lexer::Token>,
          I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    let lex = || satisfy_map(|t| if let lexer::Token::Ident(s) = t {Some(s)} else {None});
    many(attempt( lex().skip(token(lexer::Token::Op(lexer::Op::Domain))) )).and(lex())
        .map(|(dns, name)| ast::Ident{domain: ast::Domain(dns), name})
}

fn lf<I>() -> impl Parser<Input = I, Output = lexer::Token> 
    where I: Stream<Item = lexer::Token>,
          I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    // satisfy(|t| if let lexer::Token::Sep(lexer::Sep::Line(..)) = t {true} else {false})
    token(lexer::Token::Sep(lexer::Sep::Line(lexer::LineSep::NewLine)))
}

fn lfs<I>() -> impl Parser<Input = I, Output = ()> 
    where I: Stream<Item = lexer::Token>,
          I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    skip_many(lf())
}