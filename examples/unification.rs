extern crate diyusi;

fn main() {
    use diyusi::core::typechk::*;
    use std::rc::Rc;

    let ctx = InferCtx {
        consts: Vec::new(),
        local: Vec::new(),
        typings: Vec::new(),
    };

    let mut subst = Vec::new();
    
    println!("{:?}", unify(Rc::new(InferTerm::Infer{id: 1}), Rc::new(InferTerm::Infer{id: 0}), &ctx, &mut subst));
    println!("{:?}", &subst);
    println!("{:?}", unify(Rc::new(InferTerm::Infer{id: 1}), Rc::new(InferTerm::Universe), &ctx, &mut subst));
    println!("{:?}", &subst);
    println!("{:?}", unify(Rc::new(InferTerm::Infer{id: 2}), Rc::new(InferTerm::Infer{id: 0}), &ctx, &mut subst));
    println!("{:?}", &subst);
}