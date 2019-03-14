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

    let (env, scope, errors) = core::translator::translate_module(module);

    let show_errors = || {
        for (e, locs) in &errors {
            println!("\terror: {} at {:?}", e.message(&scope), locs);
        }
    };

    println!("scope: {:#?}\n", scope);

    let env =
        if let Some(env) = env {
            println!("namespace registration successful");
            println!("env: {:#?}\n", env);
            env
        }
        else {
            println!("namespace registration failure");
            show_errors();
            return;
        };
    
    if !errors.is_empty() {
        println!("environment translation failure");
        show_errors();
        return;
    }

    println!("{}", diyusi::core::typechk::HoledEnv::from(env));

    return;

    println!("{:#?}\n", core::typechk::typechk(env.into()));
}