use super::ast;
use super::lexer;

use combine::*;
use combine::stream::state::SourcePosition;

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
            .with(expr()).skip(lfs())
            .skip(look_ahead(token(lexer::Token::Sep(lexer::Sep::CloseParen)).or(lf())))
        ),
    ))
}

fn expr_<I>() -> impl Parser<Input = I, Output = ast::TermWithPos>
    where I: Stream<Item = lexer::Token, Position = usize>,
          I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    let userdefop = || satisfy_map( |t|
        if let lexer::Token::Op(lexer::Op::UserDef(s)) = t { Some(ast::Op(s)) }
        else { None }
    );

    let expr_app = || chainl1( term(),
        value(())
            .map( |_| |f: ast::TermWithPos, x: ast::TermWithPos| ast::TermWithPos {
                start: f.start, end: x.end,
                term: Box::new(ast::Term::App{f,x}),
            } )
    );

    let expr_udi = || expr_app().and(many(attempt(lfs().with(userdefop()).skip(lfs()).and(expr_app()))))
        .map( |(head, tail):(_, Vec<_>)| {
            if tail.is_empty() { *head.term }
            else { ast::Term::Infix(ast::Infix{head,tail}) }
        } );
    
    let expr_let = || token(lexer::Token::Keyword(lexer::Keyword::Let)).skip(lfs())
        .with(sep_by1(
            expr().skip(lfs()).skip(token(lexer::Token::Op(lexer::Op::UserDef("=".into())))).skip(lfs())
                .and(expr()),
            attempt(skip_many1(lf()).skip(look_ahead(expr()))) )).skip(lfs())
        .skip(token(lexer::Token::Keyword(lexer::Keyword::In))).skip(lfs())
        .and(expr())
        .map(|(defs, body)| ast::Term::Let{defs, body});
    
    let expr_case = || token(lexer::Token::Keyword(lexer::Keyword::Case)).skip(lfs())
        .with(expr()).skip(lfs())
        .skip(token(lexer::Token::Keyword(lexer::Keyword::Of))).skip(lfs())
        .and(sep_by(
            expr().skip(lfs()).skip(token(lexer::Token::Op(lexer::Op::Matcher))).skip(lfs()).and(expr())
                .map(|(patn, t)| ast::Arm{patn,t}),
            attempt(skip_many1(lf()).skip(look_ahead(expr())))
        ))
        .map(|(t, arms)| ast::Term::Case{t, arms});
    
    let expr_if = || (
        token(lexer::Token::Keyword(lexer::Keyword::If)).skip(lfs()).with(expr()).skip(lfs()),
        token(lexer::Token::Keyword(lexer::Keyword::Then)).skip(lfs()).with(expr()).skip(lfs()),
        token(lexer::Token::Keyword(lexer::Keyword::Else)).skip(lfs()).with(expr())
    ).map(|(p,tv,fv)| ast::Term::If{p,tv,fv});

    let expr_primary = || (position(), choice((
        attempt( expr_udi() ),
        attempt( expr_let() ),
        attempt( expr_case() ),
        attempt( expr_if() ),
    )), position()).map(|(start, t, end)| ast::TermWithPos{term: Box::new(t), start, end});

    let expr_lam = || token(lexer::Token::Op(lexer::Op::Lambda)).skip(lfs()).with(ident()).skip(lfs())
        .skip(token(lexer::Token::Op(lexer::Op::Typing))).skip(lfs()).and(expr_primary()).skip(lfs())
        .skip(token(lexer::Token::Op(lexer::Op::Arrow))).skip(lfs()).and(expr())
        .map(|((x,A),t)| ast::Term::Lam{x,A,t});
    
    let expr_pi = || token(lexer::Token::Sep(lexer::Sep::OpenParen)).skip(lfs()).with(ident()).skip(lfs())
        .skip(token(lexer::Token::Op(lexer::Op::Typing))).skip(lfs()).and(expr()).skip(lfs())
        .skip(token(lexer::Token::Sep(lexer::Sep::CloseParen))).skip(lfs())
            .skip(token(lexer::Token::Op(lexer::Op::Arrow))).skip(lfs()).and(expr())
        .map(|((x,A),B)| ast::Term::Pi{x,A,B});
    
    let expr_abs = || (position(), choice(( attempt(expr_lam()), attempt(expr_pi()) )), position())
        .map(|(start, t, end)| ast::TermWithPos{term: Box::new(t), start, end});
    
    let expr_arrow = || chainr1(expr_primary(),
        attempt(lfs().skip(token(lexer::Token::Op(lexer::Op::Arrow))).skip(lfs()))
            .map(|_| |A: ast::TermWithPos, B: ast::TermWithPos|
                ast::TermWithPos {
                    start: A.start, end: B.end,
                    term: Box::new(ast::Term::Arrow{A,B}),
                }
            )
        );

    let expr_typer = || choice((
        attempt(expr_abs()),
        attempt(expr_arrow()),
    ));

    let expr_typing = || (position(), expr_udi(), position())
        .skip(lfs()).skip(token(lexer::Token::Op(lexer::Op::Typing))).skip(lfs())
            .map(|(start, t, end)| ast::TermWithPos{term: Box::new(t), start, end})
        .and(expr_typer())
        .map(|(x,T)| ast::TermWithPos {
            start: x.start, end: T.end,
            term: Box::new(ast::Term::Typing(ast::Typing{x,T})),
        });

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
    where I: Stream<Item = lexer::Token>,
          I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    satisfy_map( |t| if let lexer::Token::Lit(lit) = t {
            Some( match lit {
                lexer::Lit::Nat(n) => ast::Lit::Nat(n),
                lexer::Lit::Int(i) => ast::Lit::Int(i),
                lexer::Lit::Str(s) => ast::Lit::Str(s),
            } )
        }
        else { None }
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
    satisfy(|t| if let lexer::Token::Sep(lexer::Sep::Line(..)) = t {true} else {false})
}

fn lfs<I>() -> impl Parser<Input = I, Output = ()> 
    where I: Stream<Item = lexer::Token>,
          I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    skip_many(lf())
}