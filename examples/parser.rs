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
            for (i, token) in lexed.iter().enumerate() {
                println!("{}: {:?}", i, token);
            }

            let lexed: Vec<_> = lexed.into_iter().map(|x| x.token).collect();
            match syntax::parse_env(&lexed) {
                Ok(expr) => println!("{}", expr),
                Err(e) => println!("{:?}", e),
            }
        },
        Err(e) => println!("{}", e),
    }
}