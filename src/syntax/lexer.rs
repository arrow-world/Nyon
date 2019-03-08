use combine::*;
use combine::parser::char::*;
use combine::stream::state::{SourcePosition, State};

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Token {
    Ident(String),
    Keyword(Keyword),
    Sep(Sep),
    Op(Op),
    Lit(Lit),
    Indent{lvl: usize},
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
    Datatype,
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
    LineComment,
    OpenCommentParen,
    CloseCommentParen,
    Semicolon,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Op {
    Arrow,
    Backslash,
    Typing,
    Def,
    Matcher,
    VertialBar,
    Dot,
    Question,
    ArgTyping,
    Other(String),
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Lit {
    Nat(::num::BigInt),
    Int(::num::BigInt),
    Str(String),
}

pub fn lex_src(src: &str) -> Result<Vec<TokenWithPos>, easy::Errors<char, &str, SourcePosition>> {
    top_level().skip(eof()).easy_parse(State::new(src)).map(|x| x.0)
}

fn top_level<I>() -> impl Parser<Input = I, Output = Vec<TokenWithPos>>
    where I: Stream<Item = char, Position = SourcePosition>,
          I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    use std::iter;    

    let token_sep = || many::<(),_>(not_followed_by(newline()).skip(space()));
    let line = || many(lex().skip( attempt(token_sep()) )).skip(token_sep());
    let indent = || (position(), many::<Vec<_>,_>( tab().or(token(' ')).with(value(())) ), position())
        .map(|(start, indent, end)| TokenWithPos{ start, end, token: Token::Indent{lvl: indent.len()} });

    sep_end_by((indent(), line()), attempt(newline()))
        .map(|lines: Vec<(_,Vec<_>)>| lines.into_iter().map(|(i,l)| iter::once(i).chain(l)).flatten().collect())
}

fn lex<I>() -> impl Parser<Input = I, Output = TokenWithPos>
    where I: Stream<Item = char, Position = SourcePosition>,
          I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    use unicode_categories::UnicodeCategories;
    let op_char = || satisfy(|c:char| c.is_punctuation_other() || c.is_symbol_math());

    let kw = || choice((
        attempt( string("data").map(|_| Keyword::Datatype) ),
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
        token(';').map(|_| Sep::Semicolon),
    ));

    let op = || attempt( choice((
        attempt( string("->").map(|_| Op::Arrow) ),
        attempt( string(":=").map(|_| Op::Def) ),
        attempt( string("=>").map(|_| Op::Matcher) ),
        token(':').map(|_| Op::Typing),
        token('\\').map(|_| Op::Backslash),
        token('|').map(|_| Op::VertialBar),
        token('.').map(|_| Op::Dot),
        token('?').map(|_| Op::Question),
        token('\'').map(|_| Op::ArgTyping),
    )).skip(not_followed_by(op_char())) )
        .or(many1::<String,_>(op_char()).map(|s| Op::Other(s)));

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

    attempt(
        (many::<String,_>(digit().or(us())), letter(), many::<String, _>(alpha_num().or(us())), many::<String,_>(token('\'')))
        .map( |(sl,ch,sr,ap)| String::from_iter( sl.chars().chain(once(ch)).chain(sr.chars()).chain(ap.chars()) ))
    ).or(us().map(|c| String::from_iter(once(c))))
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

fn comment<I>() -> impl Parser<Input = I, Output = ()>
    where I: Stream<Item = char, Position = SourcePosition>,
          I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    attempt( string("#").skip(many::<(),_>(not_followed_by(newline()).skip(any()))).skip(newline()) ).with(value(()))
        .or( attempt( paren_comment() ) )
}

fn paren_comment_<I>() -> impl Parser<Input = I, Output = ()>
    where I: Stream<Item = char, Position = SourcePosition>,
          I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    string("(*").with(many::<(),_>(not_followed_by(string("*)")).with(
        paren_comment().or(any().with(value(())))
    ))).skip(string("*)"))
}

parser! {
    pub fn paren_comment[I]()(I) -> () where [I: Stream<Item = char, Position = SourcePosition>] {
        paren_comment_()
    }
}
