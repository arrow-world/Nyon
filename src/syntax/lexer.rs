use combine::*;
use combine::parser::char::*;
use combine::stream::state::SourcePosition;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Token {
    Ident(String),
    Keyword(Keyword),
    Sep(Sep),
    Op(Op),
    Lit(Lit),
}
impl From<TokenWithPos> for Token {
    fn from(x: TokenWithPos) -> Token { x.token }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct TokenWithPos {
    pub token: Token,
    pub start: SourcePosition,
    pub end: SourcePosition,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Keyword {
    Type,
    Let,
    In,
    Case,
    Of,
    If,
    Then,
    Else,
    Data,
    Where,
    Infix,
    InfixPrio,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Sep {
    OpenParen,
    CloseParen,
    OpenBracket,
    CloseBracket,
    OpenBrace,
    CloseBrace,
    Dollar,
    Comma,
    Line(LineSep),
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum LineSep {
    NewLine,
    Semicolon,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Op {
    Arrow,
    Lambda,
    Typing,
    Domain,
    Hole,
    Def,
    Matcher,
    UserDef(String),
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Lit {
    Nat(::num::BigInt),
    Int(::num::BigInt),
    Str(String),
}

pub fn top_level<I>() -> impl Parser<Input = I, Output = Vec<TokenWithPos>>
    where I: Stream<Item = char, Position = SourcePosition>,
          I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    let token_sep = || many::<(),_>(not_followed_by(newline()).skip(space()));
    let comment = || attempt( string("#").skip(many::<(),_>(not_followed_by(newline()).skip(any()))).skip(newline()) )
        .or(attempt( string("(*").skip(many::<(),_>(not_followed_by(string("*)")))).skip(string("*)")) ))
        .with(value(()));

    token_sep().with(many(lex().skip(attempt(token_sep()).or(comment()))))
}

fn lex<I>() -> impl Parser<Input = I, Output = TokenWithPos>
    where I: Stream<Item = char, Position = SourcePosition>,
          I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    use unicode_categories::UnicodeCategories;
    let op_char = || satisfy(|c:char| c.is_punctuation_other() || c.is_symbol_math());

    let kw = || choice((
        attempt( string("data").map(|_| Keyword::Data) ),
        attempt( string("where").map(|_| Keyword::Where) ),
        attempt( string("infix_prio").map(|_| Keyword::InfixPrio) ),
        attempt( string("infix").map(|_| Keyword::Infix) ),
        attempt( string("type").map(|_| Keyword::Type) ),
        attempt( string("let").map(|_| Keyword::Let) ),
        attempt( string("in").map(|_| Keyword::In) ),
        attempt( string("case").map(|_| Keyword::Case) ),
        attempt( string("of").map(|_| Keyword::Of) ),
        attempt( string("if").map(|_| Keyword::If) ),
        attempt( string("then").map(|_| Keyword::Then) ),
        attempt( string("else").map(|_| Keyword::Else) ),
    )).skip(not_followed_by(alpha_num()));

    let sep = || choice((
        token('(').map(|_| Sep::OpenParen),
        token(')').map(|_| Sep::CloseParen),
        token('[').map(|_| Sep::OpenBracket),
        token(']').map(|_| Sep::CloseBracket),
        token('{').map(|_| Sep::OpenBrace),
        token('}').map(|_| Sep::CloseBrace),
        token('$').map(|_| Sep::Dollar),
        token(',').map(|_| Sep::Comma),
        token(';').map(|_| Sep::Line(LineSep::Semicolon)),
    )).or( newline().map(|_| Sep::Line(LineSep::NewLine)) );

    let op = || attempt( choice((
        attempt( string("->").map(|_| Op::Arrow) ),
        attempt( string(":=").map(|_| Op::Def) ),
        attempt( string("::").map(|_| Op::Domain) ),
        attempt( string("=>").map(|_| Op::Matcher) ),
        token(':').map(|_| Op::Typing),
        token('_').map(|_| Op::Hole),
        token('\\').map(|_| Op::Lambda),
    )).skip(not_followed_by(op_char())) )
        .or(many1::<String,_>(op_char()).map(|s| Op::UserDef(s)));

    let token = || choice((
        attempt( kw().map(|kw| Token::Keyword(kw)) ),
        attempt( ident().map(|s| Token::Ident(s)) ),
        attempt( sep().map(|sep| Token::Sep(sep)) ),
        attempt( op().map(|op| Token::Op(op)) ),
        attempt( lit().map(|lit| Token::Lit(lit)) ),
    ));

    (position(), token(), position())
        .map( |(start, token, end)| TokenWithPos{token, start, end} )
}

fn ident<I>() -> impl Parser<Input = I, Output = String>
    where I: Stream<Item = char>,
          I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    use std::iter::{FromIterator, once};
    let us = || token('_');

    (many::<String,_>(digit().or(us())), letter(), many::<String, _>(alpha_num().or(us())), many::<String,_>(token('\'')))
        .map( |(sl,ch,sr,ap)| String::from_iter( sl.chars().chain(once(ch)).chain(sr.chars()).chain(ap.chars()) ))
}

fn lit<I>() -> impl Parser<Input = I, Output = Lit>
    where I: Stream<Item = char>,
          I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    choice((
        attempt( nat().map(|n| Lit::Nat(n)) ),
        attempt( int().map(|i| Lit::Int(i)) ),
        attempt( str().map(|s| Lit::Str(s)) ),
    ))
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
    let sign = token('+').or(token('-'));
    sign.and(nat()).map(|(s, n): (char, ::num::BigInt)| if s == '-' {-n} else {n})
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