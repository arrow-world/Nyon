extern crate diyusi;

fn main() {
    use diyusi::core::typechk::*;
    use std::rc::Rc;

    let ctx = InferCtx {
        consts: Vec::new(),
        local: Vec::new(),
        typings: Vec::new(),
    };
}