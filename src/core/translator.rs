use syntax::ast;
use core;

pub fn from_ast<'s>(ast: ast::Module) -> Result<core::TopLevel<'s>, TranslateErr> {
    let mut tl = core::TopLevel::with_builtin();
    let ref mut top = tl.top_module;

    let ast::Env(statements) = ast.env;
    for statement in statements {
        match statement {
            ast::Statement::Data{ident, T, ctors} => {
                if !ident.domain.is_empty() { Err(TranslateErr::CantSpecifyNamespace) }
                else 
            },
        }
    }

    tl
}

pub enum TranslateErr {
    CantSpecifyNamespace,
}