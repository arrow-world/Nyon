use core::modules::Scope;
use syntax::{ast, Loc};
use core;

#[derive(Clone, Debug)]
pub enum TranslateErr {
    CantSpecifyNamespace(ast::Ident),
    UndefinedIdent(ast::Ident),
    ConflictedVar(String),
    ExpectedIdent,
    ExpectedIdentOfCtor,
    ExpectedIdentAtArgsOfCtor,
    ExpectedTyping,
    MismatchDataType{arm_no: usize},
    DuplicatedPatterns{arms_no: Vec<usize>, ctor: core::ConstId},
    NonExhaustivePattern{ctor: core::CtorId},
    ConflictedDatatypeName(String),
    ExpectedSelfDatatype,
    RegLocalEnvErr(Vec<(TranslateErr, Loc)>),
    ExpectedParam,
    UndefinedModule{name: String}
}
impl TranslateErr {
    pub fn message(&self, scope: &Scope) -> String {
        match self {
            TranslateErr::CantSpecifyNamespace(i) => format!("qualified name `{}` is not allowed here", i),
            TranslateErr::UndefinedIdent(i) => format!("undefined name `{}`", i),
            TranslateErr::ConflictedVar(s) => format!("conflicted variable name `{}`", s),
            TranslateErr::ExpectedIdent => format!("expected name"),
            TranslateErr::ExpectedIdentOfCtor => format!("expected name of datatype constructor"),
            TranslateErr::ExpectedIdentAtArgsOfCtor => format!("expected paramater name of constructor"),
            TranslateErr::ExpectedTyping => format!("expected type annotation"),
            TranslateErr::MismatchDataType{arm_no} => format!("mismatch datatype at {}-th arm", arm_no),
            TranslateErr::DuplicatedPatterns{..} => format!("duplicated pattern"),
            TranslateErr::NonExhaustivePattern{ctor} => format!("constructor `{}` not covered", scope.names()[*ctor]),
            TranslateErr::ConflictedDatatypeName(name) => format!("conflicted datatype name `{}`", name),
            TranslateErr::ExpectedSelfDatatype => format!("expected self datatype"),
            TranslateErr::RegLocalEnvErr(errs) => format!("local environment registering failed: {:#?}", errs),
            TranslateErr::ExpectedParam => format!("expected parameter"),
            TranslateErr::UndefinedModule{name} => format!("undefined module `{}`", name),
        }
    }
}