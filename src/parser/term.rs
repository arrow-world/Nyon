use super::*;
use super::ast::*;
use super::lexer::*;

pub fn term_by_<I>(by: HashSet<Token>)
    -> impl Parser<Input = I, Output = TermWithPos>
    where I: Stream<Item = TokenWithPos, Position = PointerOffset>,
          I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    use std::iter::once;

    let by_or = |ts| {
        let mut x = by.clone();
        x.extend(ts);
        x
    };

    let kw_let = || token(Token::Keyword(Keyword::Let).into());
    let sep_open_paren = || token(Token::Sep(Sep::OpenParen).into());
    let sep_close_paren = || token(Token::Sep(Sep::CloseParen).into());
    let sep_lf = || many(token(Token::Sep(Sep::LF).into()));
    let op_typing = || token(Token::Op(lexer::Op::Typing).into());
    let op_arrow = || token(Token::Op(lexer::Op::Arrow).into());
    let op_eq = || token(Token::Op(lexer::Op::Equal).into());
    let op_lam = || token(Token::Op(lexer::Op::Lambda).into());
    
    let name = || satisfy_map( |t| {
        if let TokenWithPos{token: Token::Ident(s), ..} = t { Some((s, t.pos.unwrap().start, t.pos.unwrap().end)) }
        else { None }
    });

    let ident = || sep_by1(name(), token(Token::Op(lexer::Op::Domain).into()))
        .map( |ns: Vec<_>| {
            let ns_without_pos = ns.iter().map(|x| x.0).collect::<Vec<_>>();
            (
                Ident{name: ns_without_pos.pop().unwrap(), domain: Domain(ns_without_pos)},
                ns.first().unwrap().1,
                ns.last().unwrap().2,
            )
        } );

    let universe = || token(Token::Keyword(Keyword::Type).into())
        .map( |TokenWithPos{token, pos}| {
            let TokenPos{start, end} = pos.unwrap();
            TermWithPos{term: Box::new(Term::Universe), start, end}
        } );

    let pi = || (
            sep_open_paren().skip(sep_lf()),
            ident().skip(sep_lf()).skip(op_typing()).skip(sep_lf()),
            term_by(by).skip(sep_lf()).skip(sep_close_paren()).skip(sep_lf()).skip(op_arrow()).skip(sep_lf()),
            term_by(by),
        ).map( |(op, x, A, B)| TermWithPos{term: Box::new(Term::Pi{x: x.0, A, B}), start: op, end: B.end} );
    
    let patn_match = |add_by|
        term_by(by_or(once(Token::Op(lexer::Op::Equal)).chain(add_by))).skip(sep_lf()).skip(op_eq()).skip(sep_lf())
        .and(term_by(by_or(once(Token::Sep(Sep::LF)).chain(add_by))));
    let let_ = || (
            kw_let().skip(sep_lf()),
            sep_by1(patn_match(once(Token::Ident("in".into()))), sep_lf()).skip(Token::Ident("in".into()).into()),
            term_by(by)
        ).map( |(let_, decs, body)|
            TermWithPos{term: Box::new(Term::Let{decs, body}), start: let_, end: body.end} );
    
    let abs = op_lam();
    
    let alpha = || choice((
        attempt( universe() ),
        attempt( pi() ),
        attempt( let_() ),
    ));

    alpha()
}

parser! {
    fn term_by[I](by: HashSet<Token>)(I) -> TermWithPos
        where [I: Stream<Item = TokenWithPos>]
    {
        term_by_(*by)
    }
}