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

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct TokenPos {
    pub start: SourcePosition,
    pub end: SourcePosition,
}

#[derive(Clone, Debug)]
pub struct TokenWithPos {
    pub token: Token,
    pub pos: Option<TokenPos>,
}
impl PartialEq for TokenWithPos {
    fn eq(&self, other: &Self) -> bool { self.token == other.token }
}
impl Eq for TokenWithPos {}
impl From<Token> for TokenWithPos {
    fn from(token: Token) -> TokenWithPos { TokenWithPos{token, pos: None} }
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
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Sep {
    OpenParen,
    CloseParen,
    Dollar,
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
    Tuple,
    Domain,
    Hole,
    Equal,
    Matcher,
    UserDef(String),
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Lit {
    Nat{n: ::num::BigInt},
    Int{i: ::num::BigInt},
    Str{s: String},
}

pub fn top_level<I>() -> impl Parser<Input = I, Output = Vec<TokenWithPos>>
    where I: Stream<Item = char, Position = SourcePosition>,
          I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    let spaces = || many::<(),_>(not_followed_by(newline()).skip(space()));
    spaces().with(many(lex().skip(spaces())))
}

fn lex<I>() -> impl Parser<Input = I, Output = TokenWithPos>
    where I: Stream<Item = char, Position = SourcePosition>,
          I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    use unicode_categories::UnicodeCategories;
    let op_char = || satisfy(|c:char| c.is_punctuation_other() || c.is_symbol_math());

    let kw = || choice((
        string("type").map(|_| Keyword::Type),
        string("let").map(|_| Keyword::Let),
        string("in").map(|_| Keyword::In),
        string("case").map(|_| Keyword::Case),
        string("of").map(|_| Keyword::Of),
        string("if").map(|_| Keyword::If),
        string("then").map(|_| Keyword::Then),
        string("else").map(|_| Keyword::Else),
    )).skip(not_followed_by(alpha_num()));

    let sep = || choice((
        token('(').map(|_| Sep::OpenParen),
        token(')').map(|_| Sep::CloseParen),
        token('$').map(|_| Sep::Dollar),
        newline().map(|_| Sep::Line(LineSep::NewLine)),
        token(';').map(|_| Sep::Line(LineSep::Semicolon)),
    )).skip(not_followed_by(op_char()));

    let op = || attempt( choice((
        string("->").map(|_| Op::Arrow),
        string("::").map(|_| Op::Domain),
        string("=>").map(|_| Op::Matcher),
        token(':').map(|_| Op::Typing),
        token(',').map(|_| Op::Tuple),
        token('_').map(|_| Op::Hole),
        token('\\').map(|_| Op::Lambda),
        token('=').map(|_| Op::Equal),
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
        .map( |(start, token, end)| TokenWithPos{token, pos: Some(TokenPos{start, end})} )
}

fn ident<I>() -> impl Parser<Input = I, Output = String>
    where I: Stream<Item = char>,
          I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    use std::iter::{FromIterator, once};
    let us = || token('_');

    (many::<String,_>(digit().or(us())), letter(), many::<String, _>(alpha_num().or(us())))
        .map( |(sl,ch,sr)| String::from_iter( sl.chars().chain(once(ch)).chain(sr.chars())))
}

fn lit<I>() -> impl Parser<Input = I, Output = Lit>
    where I: Stream<Item = char>,
          I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    choice((
        attempt( nat().map(|n| Lit::Nat{n}) ),
        attempt( int().map(|i| Lit::Int{i}) ),
        attempt( str().map(|s| Lit::Str{s}) ),
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