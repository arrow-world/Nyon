extern crate lassy;
use lassy::syntax;
use std::fs::File;
use std::io::prelude::*;

fn main(){
    let mut source = String::new();
    File::open("test.ner").unwrap().read_to_string(&mut source).unwrap();
    let source = source;

    match syntax::lex(&source) {
        Ok(lexed) => {
            for token in lexed {
                println!("{:?}", token);
            }
        },
        Err(e) => println!("{}", e),
    }
}