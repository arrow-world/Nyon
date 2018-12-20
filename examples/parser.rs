extern crate lassy;
use lassy::parser;
use std::fs::File;
use std::io::prelude::*;

fn main(){
    let mut source = String::new();
    File::open("test.ner").unwrap().read_to_string(&mut source).unwrap();
    let source = source;

    /* match parser::parse_term(&source) {
        Ok(ast) => println!("{}", ast),
        Err(e) => println!("{}", e),
    } */
}