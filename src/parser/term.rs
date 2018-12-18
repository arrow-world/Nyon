use combine::*;
use combine::parser::char::*;
use combine::stream::{state::{SourcePosition, State}, easy};

use super::*;
use super::ast::*;

pub fn term<I>() -> impl Parser<Input = I, Output = Term>
    where I: Stream<Item = char, Position = SourcePosition>,
          I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    let identifier = || ident::<I>().map(|i| TermWithoutPos::Var(i));

    let universe = || string("type").map(|_| TermWithoutPos::Universe);

    let de_bruijn_index = || token('@').with(nat()).map(|i| TermWithoutPos::DBI(i));

    let pi = || token('(').skip(token_sep()).with(ident()).skip(token_sep()).skip(token(':')).skip(token_sep())
        .and(term_avoid_rec().skip(token_sep()).skip(string("->")).skip(token_sep()))
        .and(term_avoid_rec())
        .map(|((x,A),B)| TermWithoutPos::Pi{x,A,B});

    let let_ = || (
        string::<I>("let").skip(token_sep()).with(term_avoid_rec()).skip(token_sep())
            .skip(token('=')).skip(token_sep()),
        term_avoid_rec().skip(token_sep()).skip(string("in")).skip(token_sep()),
        term_avoid_rec(),
    ).map(|(patn,t,u)| TermWithoutPos::Let{patn,t,u});

    let abs = || token('\\').skip(token_sep()).with(ident()).skip(token_sep()).skip(token(':')).skip(token_sep())
        .and(term_avoid_rec()).skip(token_sep()).skip(token('.')).skip(token_sep()).and(term_avoid_rec())
        .map(|((x,A),t)| TermWithoutPos::Abs{x,A,t});
    
    let arm = || term_avoid_rec::<I>().skip(token_sep()).skip(string("=>")).skip(token_sep())
        .and(term_avoid_rec()).map(|(patn,t)| Arm{patn,t});
    let case = || string("case").skip(token_sep()).with(term_avoid_rec()).skip(token_sep())
        .skip(string("of")).and(sep_end_by(spaces().with(arm()), spaces().skip(token(';'))))
        .map(|(t,arms)| TermWithoutPos::Case{t,arms});
    
    let hole = || token('_').with(value(TermWithoutPos::Hole));
    
    let lit_beta = || choice((
        try( nat().map(|n| TermWithoutPos::Literal(Literal::Nat(n))) ),
        try( int().map(|i| TermWithoutPos::Literal(Literal::Int(i))) ),
        try( str().map(|s| TermWithoutPos::Literal(Literal::Str(s))) ),
    ));

    let beta = || choice((
        try( universe() ),
        try( de_bruijn_index() ),
        try( pi() ),
        try( let_() ),
        try( abs() ),
        try( case() ),
        try( hole() ),
        try( lit_beta() ),
        try( identifier() ),
    ));

    let pre_term_beta = || (position(), beta(), position())
        .map(|(start, f, end)| Term{start, end, term: Box::new(f)});

    let term_beta = || choice((
        try( pre_term_beta() ),
        try( between(token('(').skip(spaces()), try(spaces().skip(token(')'))), term_avoid_rec()) ),
        try( between(token('$').skip(spaces()), try(spaces().skip(look_ahead(token(')').or(newline())))), term_avoid_rec()) ),
    ));

    let alpha_arrow = || term_beta().and(token_sep().skip(string("->")).skip(token_sep()).with(term_avoid_rec()))
        .map(|(A,B)| TermWithoutPos::Arrow{A,B});

    let alpha_typing = || term_beta().and(token_sep().skip(token(':')).skip(token_sep()).with(term_avoid_rec()))
        .map(|(x,T)| TermWithoutPos::Typing(Typing{x,T}));

    let alpha_infix = || term_beta()
        .and(many1(attempt( token_sep().with(op()).skip(token_sep()).and(term_avoid_rec()) )))
        .map(|(head,tail)| TermWithoutPos::Infix(Infix{head,tail}));
    
    let term_without_app_tuple = || try( (
        position(),
        choice((
            try( alpha_arrow() ),
            try( alpha_typing() ),
            try( alpha_infix() ),
        )),
        position(),
    ).map(|(start, t, end)| Term{start, end, term: Box::new(t)}) )
        .or(try( term_beta() ));
    
    let term_without_tuple = || term_without_app_tuple()
        .and( many::<Vec<_>,_>(try( spaces().skip(look_ahead(term_without_app_tuple())) )
            .with(term_without_app_tuple())) )
        .map( |(f,tail)| tail.into_iter()
            .fold(f, |f,x| Term{start: f.start, end: x.end, term: Box::new(TermWithoutPos::App{f,x})}) );

    try( term_without_tuple().and( token_sep().skip(token(',')).skip(token_sep())
        .with(sep_end_by(term_avoid_rec(), token_sep().skip(token(',').skip(token_sep())))) )
        .map( |(head,tail):(_,Vec<_>)| Term {
            start: head.start,
            end: if let Some(last) = tail.last() { last.end } else { head.end },
            term: Box::new( TermWithoutPos::Literal(Literal::Tuple{head,tail}) ),
        } )
    ).or(try( term_without_tuple() ))
}

fn term_avoid_rec<I>() -> impl Parser<Input = I, Output = Term>
    where I: Stream<Item = char, Position = SourcePosition>,
          I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    parser(|input| { term().parse_stream(input) })
}