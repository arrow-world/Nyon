extern crate diyusi;
extern crate log;
extern crate env_logger;

use diyusi::syntax;
use diyusi::core;
use std::fs::File;
use std::io::prelude::*;

fn main(){
    env_logger::init();

    let mut source = String::new();
    File::open("stdlib/collections/list.nyn").unwrap().read_to_string(&mut source).unwrap();
    let source = source;

    let lexed = match syntax::lex_src(&source) {
        Ok(x) => x,
        Err(e) => {
            println!("{}", e);
            return;
        },
    };

    for (i, token) in lexed.iter().enumerate() {
        println!("{}: {:#?}", i, token);
    }

    let lexed: Vec<_> = lexed.into_iter().map(|x| x.token).collect();

    let expr = match syntax::parse_env(&lexed) {
        Ok(x) => x,
        Err(e) => {
            println!("{:#?}", e);
            return;
        },
    };
    println!("{}\n", expr);

    let module = syntax::ast::Module {
        env: expr,
        name: "top_level".into(),
        children: Vec::new(),
    };

    let (env, scope) = match core::translator::translate_module(module) {
        Ok(x) => x,
        Err(es) => {
            for (e, locs) in es {
                println!("translate error: {} at {:?}", e.message(), locs);
            }
            return;
        }
    };

    println!("env: {:#?}\n", env);
    println!("scope: {:#?}\n", scope);

    println!("{:#?}\n", core::typechk::typechk(env.into()));
}