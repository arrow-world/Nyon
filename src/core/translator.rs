use syntax::ast;
use core;

pub fn from_ast<'s>(ast: ast::Module) -> Result<core::TopLevel<'s>, TranslateErr> {
    let mut tl = core::TopLevel::with_builtin();
    {
        let ref mut top = tl.top_module;

    }
    Ok(tl)
}

fn register_module<'s>(core_module: &mut core::Module, ast_module: ast::Module, tl: &core::TopLevel)
    -> Result<(), TranslateErr>
{
    use core::idgen::Generator;

    let ast::Env(statements) = ast_module.env;
    for statement in statements {
        match statement {
            ast::Statement::Data{ident, T, ctors} => {
                if !ident.domain.is_empty() { return Err(TranslateErr::CantSpecifyNamespace); }
                tl.idgen.gen()
                core_module.register()
            },
        }
    }
    Ok(())
}

pub enum TranslateErr {
    CantSpecifyNamespace,
}