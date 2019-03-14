use syntax::Loc;
use syntax::loc_range;
use super::ast;
use super::lexer;
use super::parser::*;
use core::{HoledTerm};
use core::typechk::{Value};
use core::translator::{self, RegisterCtx, TranslateErr, translate_term};

use combine::*;
use std::fmt;
use std::rc::Rc;

#[derive(Clone, Debug)]
pub enum ExtTerm {
    Lit(Lit),
    Infix{head: ast::TermWithLoc, tail: Vec<(ast::Op, ast::TermWithLoc)>},
}
impl fmt::Display for ExtTerm {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ExtTerm::Lit(l) => write!(f, "{}", l),
            ExtTerm::Infix{head, tail} => {
                if tail.is_empty() {
                    write!(f, "{}", head)
                }
                else {
                    write!(f, "({} ", head)?;
                    for (op, t) in tail {
                        write!(f, "{} {}", op.0, t)?;
                    }
                    write!(f, ")")
                }
            }
        }
    }
}

pub(super) fn ext_term<I>(indent_lvl: i64) -> impl Parser<Input = I, Output = ExtTerm>
    where I: Stream<Item = lexer::Token, Position = usize>,
          I::Error: ParseError<I::Item, I::Range, I::Position>
{
    choice((
        attempt( lit(indent_lvl).map(|lit| ExtTerm::Lit(lit)) ),
    ))
}

pub(crate) fn translate_ext_term(et: ExtTerm, regctx: &mut RegisterCtx)
    -> Result<Rc<HoledTerm>, TranslateErr>
{
    match et {
        ExtTerm::Lit(l) => translate_literal(l, regctx),
        ExtTerm::Infix{head, tail} => translate_infix(head, tail, regctx),
    }
}

pub(crate) fn list_occurred(term: &ExtTerm, vars: &Vec<&str>, list: &mut Vec<usize>) {
    match term {
        ExtTerm::Lit(lit) => (),
        ExtTerm::Infix{head, tail} => {
            translator::list_occurred_accum(&head.term, vars, list);
            for (_op, t) in tail { translator::list_occurred_accum(&t.term, vars, list); }
        }
    }
}

#[derive(Clone, Debug)]
pub enum Lit {
    Nat(::num::BigInt),
    Int(::num::BigInt),
    Str(String),
    Tuple(Vec<ast::TermWithLoc>),
}
impl fmt::Display for Lit {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Lit::Nat(n) => write!(f, "{}", n),
            Lit::Int(i) => write!(f, "{:+}", i),
            Lit::Str(s) => write!(f, "{}", s),
            Lit::Tuple(es) => {
                write!(f, "[")?;
                for i in 0..es.len() {
                    write!(f, "{:}", es[i])?;
                    if i < es.len()-1 { write!(f, ", ")?; }
                }
                write!(f, "]")
            },
        }
    }
}

fn lit<I>(indent_lvl: i64) -> impl Parser<Input = I, Output = Lit>
    where I: Stream<Item = lexer::Token, Position = usize>,
          I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    attempt( satisfy_map( |t| if let lexer::Token::Lit(lit) = t {
            Some( match lit {
                lexer::Lit::Nat(n) => Lit::Nat(n),
                lexer::Lit::Int(i) => Lit::Int(i),
                lexer::Lit::Str(s) => Lit::Str(s),
            } )
        }
        else { None }
    ) ).or(
        token(lexer::Token::Sep(lexer::Sep::OpenBracket)).skip(lfs())
        .with(sep_end_by(expr(indent_lvl),
            attempt(lfs().skip(token(lexer::Token::Sep(lexer::Sep::Comma))).skip(lfs()))))
        .skip(token(lexer::Token::Sep(lexer::Sep::CloseBracket)))
        .map(|es| Lit::Tuple(es))
    )
}

fn translate_literal(lit: Lit, regctx: &mut RegisterCtx) -> Result<Rc<HoledTerm>, TranslateErr> {
    use std::iter;

    Ok( match lit {
        Lit::Nat(n) => Rc::new( HoledTerm::Value(Value::Nat(n)) ),
        Lit::Int(i) => Rc::new( HoledTerm::Value(Value::Int(i)) ),
        Lit::Str(s) => Rc::new( HoledTerm::Value(Value::Str(s)) ),
        Lit::Tuple(ts) => {
            let cons = (
                Rc::new(HoledTerm::Const( regctx.scope.resolve(iter::once("Tuple"), "Cons").unwrap() )),
                None,
            );
            let nil = Rc::new(HoledTerm::Const( regctx.scope.resolve(iter::once("Tuple"), "Nil").unwrap() ));

            ts.into_iter().try_fold( nil, |t, head| -> Result<_, TranslateErr> {
                Ok(Rc::new(
                    HoledTerm::App {
                        s:  (Rc::new( HoledTerm::App {
                                s: cons.clone(),
                                t: translate_term(head, regctx)?,
                                implicit: false
                            } ), None),
                        t: (t, None),
                        implicit: false,
                    }
                ))
            } )?
        },
    } )
}

fn ext_op<I>() -> impl Parser<Input = I, Output = ast::Op>
    where I: Stream<Item = lexer::Token, Position = usize>,
          I::Error: ParseError<I::Item, I::Range, I::Position>
{
    satisfy_map( |t|
        if let lexer::Token::Op(lexer::Op::Other(s)) = t { Some(ast::Op(s)) }
        else { None }
    )
}

fn translate_infix(head: ast::TermWithLoc, tail: Vec<(ast::Op, ast::TermWithLoc)>, regctx: &mut RegisterCtx)
    -> Result<Rc<HoledTerm>, TranslateErr>
{
    unimplemented!()
}

pub(super) enum ExtStatement {
    Struct{header: ast::TermWithLoc, fields: Vec<ast::TermWithLoc>},
}

pub(super) fn def_struct<I>(indent_lvl: i64) -> impl Parser<Input = I, Output = ExtStatement>
    where I: Stream<Item = lexer::Token, Position = usize>,
          I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    token(lexer::Token::Ident("struct".into())).skip(lfs())
        .with(expr(indent_lvl))
        .and(compound(|inner_indent_lvl| expr(inner_indent_lvl), indent_lvl, lexer::Token::Sep(lexer::Sep::Comma)))
        .map( |(header, fields)| ExtStatement::Struct {
            header,
            fields: fields.into_iter().map(|(t, _loc)| t).collect()
        } )
}