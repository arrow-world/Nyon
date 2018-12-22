use super::ast;
use super::lexer;

trait Parser {
    type T;
    type E;

    fn parse<I: Iterator<Item=lexer::TokenWithPos>>(&self, src: &mut I) -> Result<Self::T, Self::E>;
}

pub struct Term {}
impl Parser for Term {
    type T = ast::TermWithPos;
    type E = TermParseErr;

    fn parse<I>(&self, src: &mut I) -> Result<ast::TermWithPos, TermParseErr> {
        unimplemented!()
    }
}
pub enum TermParseErr {
    EmptySource,
}

pub struct Ident {}
impl Parser for Ident {
    type T = ast::Ident;
    type E = IdentParseErr;

    fn parse<I: Iterator<Item=lexer::TokenWithPos>>(&self, src: &mut I) -> Result<ast::Ident, IdentParseErr> {
        let lex_ident = || if let Some(lexer::Token::Ident(s)) = src.next() {Ok(s)} else {None}

        let domain = sep_by(lex_ident(), token(lexer::Token::Op(lexer::Op::Domain))).parse(src)?;
        let name = lex_ident().parse(src)?;
        Ok(ast::Ident{domain,name})
    }
}
pub enum IdentParseErr {
    EmptySource,
}

fn token(t: lexer::Token) -> Token {
    Token{t}
}
pub struct Token { t: lexer::Token }
impl Parser for Token {
    type T = ();
    type E = ();

    fn parse<I: Iterator<Item=lexer::TokenWithPos>>(&self, src: &mut I) -> Result<(),()> {
        let t = self.t;
        if let Some(t) = src.next() { Ok(()) }
        else { Err(()) }
    }
}

fn sep_by<P,S,F,E>(p: P, separator: S) -> SepBy<P,S,F,E> {
    SepBy { p, s: separator, phantom: Default::default() }
}
pub struct SepBy<P,S,F,E> {
    p: P,
    s: S,
    phantom: ::std::marker::PhantomData<(F,E)>
}
impl<P: Parser, S: Parser, F: Extend<P::T>+Default, E: From<P::E> + From<S::E>> Parser for SepBy<P,S,F,E> {
    type T = F;
    type E = E;

    fn parse<I: Iterator<Item=lexer::TokenWithPos>>(&self, src: &mut I) -> Result<F,E> {
        use ::std::iter::once;

        let mut f: F = Default::default();
        loop {
            f.extend(once( self.p.parse(src)? ));
            if let Err(..) = self.s.parse(src) { return Ok(f); }
        }
    }
}