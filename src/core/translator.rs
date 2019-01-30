use syntax::ast;
use core;
use core::typechk;

use std::rc::Rc;
use std::collections::HashMap;

pub fn translate_module<'a>(ast: ast::Module) -> Result<(core::Env, Rc<core::modules::Scope>), Vec<TranslateErr>> {
    let mut regctx = RegisterCtx::new(core::modules::Scope::top());
    register_module(&mut regctx, ast).map_err(|x| vec![x])?;

    translate_all(&mut regctx).unwrap_or_else(|e| {
        regctx.errors.push(e);
    });

    if regctx.errors.is_empty() { Ok((regctx.env, regctx.scope)) }
    else { Err(regctx.errors) }
}

fn translate_all(regctx: &mut RegisterCtx) -> Result<(), TranslateErr> {
    assert_eq!(regctx.consts.len(), regctx.scope.names().len());

    regctx.env.consts.reserve(regctx.consts.len());
    for c in regctx.consts.split_off(0) {
        let c = translate_const(c, regctx).map_err(|e| regctx.errors.push(e)).ok();
        regctx.env.consts.push(c);
    }

    regctx.env.typings.reserve(regctx.typings.len());
    for t in regctx.typings.split_off(0) {
        let t = translate_typing(t, regctx).map_err(|e| regctx.errors.push(e)).ok();
        regctx.env.typings.push(t);
    }

    assert!(regctx.consts.is_empty());
    assert!(regctx.typings.is_empty());
    assert!(regctx.ac.vars.is_empty());

    Ok(())
}

fn translate_const(c: UntranslatedConst, regctx: &mut RegisterCtx) -> Result<typechk::HoledConst, TranslateErr> {
    Ok( match c {
        UntranslatedConst::Def{param_names, rhs} => typechk::HoledConst::Def(
            translate_parametric_term(rhs, param_names.into_iter().map(|x| Ok(x)), regctx)?
        ),
        UntranslatedConst::DataType{type_} => {
            let (param_types, universe) = unfold_arrow_chain(type_);
            typechk::HoledConst::DataType {
                param_types: param_types.into_iter().
                    map(|param| translate_term(param, regctx)).collect::<Result<_,_>>()?,
                universe: translate_term(universe, regctx)?,
            }
        },
        UntranslatedConst::Ctor{datatype, type_} => {
            let (param_types, ret_type) = unfold_arrow_chain(type_);
            typechk::HoledConst::Ctor {
                datatype,
                param_types: param_types.into_iter()
                    .map(|param| translate_term(param, regctx)).collect::<Result<_,_>>()?,
                ret_type: translate_term(ret_type, regctx)?,
            }
        },
    } )
}

fn translate_term(term: ast::TermWithPos, regctx: &mut RegisterCtx) -> Result<Rc<core::HoledTerm>, TranslateErr> {
    let term_with_pos = term.clone();
    let term = *term.term;
    Ok( match term {
        ast::Term::Ident(i) => Rc::new(
            regctx.scope.resolve_from_ident(&i)
                .map(|cid| core::HoledTerm::Const(cid))
                .or_else(|| regctx.ac.dbi(&i.name).map(|dbi| core::HoledTerm::DBI(dbi)))
                .ok_or(TranslateErr::UndefinedIdent(i))?
        ),
        ast::Term::Universe => Rc::new( core::HoledTerm::Universe ),
        ast::Term::App{f,x} => Rc::new( core::HoledTerm::App {
            s: translate_term(f, regctx)?,
            t: translate_term(x, regctx)?,
        } ),
        ast::Term::Lam{x, A, t} => Rc::new( core::HoledTerm::Lam(translate_abs(x, A, t, regctx)?) ),
        ast::Term::Pi{x, A, B} => Rc::new( core::HoledTerm::Pi(translate_abs(x, A, B, regctx)?) ),
        ast::Term::Arrow{A, B} => Rc::new( core::HoledTerm::Pi( core::typechk::HoledAbs {
            A: translate_term(A, regctx)?,
            t: translate_term(B, regctx)?,
        } ) ),
        ast::Term::Typing(ast::Typing{x,T}) => {
            let x = translate_term(x, regctx)?;
            let T = translate_term(T, regctx)?;
            regctx.env.typings.push(Some( (x.clone(), T) ));
            x
        },
        ast::Term::Let{env: letenv, body} => {
            let mut local_regctx =
                RegisterCtx::new(core::modules::Scope::new(regctx.scope.module(), regctx.scope.clone()));

            register_env(&mut local_regctx, letenv)?;
            let t = translate_term(body, &mut local_regctx)?;

            translate_all(&mut local_regctx)?;

            Rc::new( core::HoledTerm::Let{env: local_regctx.env.into(), t} )
        },
        ast::Term::Case{t, arms} => {
            let translated_arms: Vec<(CtorInfo, Rc<typechk::HoledTerm>)> = arms.into_iter().map( |arm| {
                let ctor_err = TranslateErr::ExpectedIdentOfCtor(arm.patn.clone());

                let (ctor_cid, body) = translate_arm(arm, regctx)?;
                regctx.ctor_info.get(&ctor_cid).map(|ctor_info| (ctor_info.clone(), body)).ok_or(ctor_err)
            } ).collect::<Result<_,_>>()?;

            let datatype = translated_arms.first().map(|(ctor_info,_)| ctor_info.datatype);

            if let Some(datatype) = datatype {
                let mismatch_datatype_arms: Vec<usize> =
                    translated_arms.iter().enumerate()
                        .filter(|(_, (ctor_info,_))| ctor_info.datatype != datatype).map(|(arm_no, _)| arm_no)
                        .collect();
                if !mismatch_datatype_arms.is_empty() {
                    regctx.errors.push(TranslateErr::MismatchDataType {
                        expr: term_with_pos.clone(),
                        arms_no: mismatch_datatype_arms,
                    })
                }
            }

            let mut cases = vec![ (None, vec![]);
                datatype.map(|datatype| regctx.datatype_info[&datatype].ctors.len()).unwrap_or(0)];
            for (arm_no, (ctor_info, body)) in translated_arms.into_iter().enumerate() {
                let (ref mut case_body, ref mut arms_no) = cases[ctor_info.ctor_id];
                if case_body.is_none() {
                    *case_body = Some(body);
                }
                arms_no.push(arm_no);
            }
            let cases = cases;
            
            let duplicated_cases: Vec<_> = cases.iter().filter(|(_,arms_no)| arms_no.len() > 1)
                .map(|(_,arms_no)| arms_no.clone()).collect();
            if !duplicated_cases.is_empty() {
                for (ctor_id, arms_no) in duplicated_cases.into_iter().enumerate() {
                    let ctor = regctx.datatype_info[&datatype.unwrap()].ctors[ctor_id];
                    regctx.errors.push(TranslateErr::DuplicatedPatterns {expr: term_with_pos.clone(), ctor, arms_no})
                }
            }

            let non_exhaustive_cases: Vec<_> = cases.iter()
                .enumerate().filter(|(_, (case_body,_))| case_body.is_none()).map(|(i,_)| i).collect();
            if !non_exhaustive_cases.is_empty() {
                regctx.errors.push(TranslateErr::NonExhaustivePatterns {
                    expr: term_with_pos,
                    ctors: non_exhaustive_cases.clone(),
                });
            }

            let hole = Rc::new(typechk::HoledTerm::Hole(None));

            Rc::new( core::HoledTerm::Case {
                t: translate_term(t, regctx)?,
                cases: cases.into_iter().map(|(case_body,_)| case_body.unwrap_or(hole.clone())).collect(),
                datatype,
            } )
        },
        ast::Term::If{..} => unimplemented!(),
        ast::Term::Lit(lit) => translate_literal(lit, regctx)?,
        ast::Term::Hole(i) =>
            if let Some(i) = i {
                unimplemented!()
            }
            else { Rc::new(typechk::HoledTerm::Hole(None)) }
    } )
}

fn translate_typing(t: UntranslatedTyping, regctx: &mut RegisterCtx)
    -> Result<(Rc<typechk::HoledTerm>, Rc<typechk::HoledTerm>), TranslateErr>
{
    Ok( (
        translate_term(t.typed, regctx)?,
        translate_term(t.type_, regctx)?,
    ) )
}

fn translate_arm(arm: ast::Arm, regctx: &mut RegisterCtx)
    -> Result<(core::ConstId, Rc<typechk::HoledTerm>), TranslateErr>
{
    let (ctor, args) = unfold_app_chain(arm.patn);

    // Note that it doesn't check here if the first of application chain of the pattern is a datatype constructor.
    // That will be checked in Type Checking stage.
    // It just checks here if the first of application chain of the pattern is a identifier.
    if let ast::Term::Ident(ident) = *ctor.term {
        if let Some(ctor_id) = regctx.scope.resolve_from_ident(&ident) {
            let args = args.into_iter().map( |arg| {
                if let ast::Term::Ident(ident) = *arg.term { Ok(ident) }
                else { Err(TranslateErr::ExpectedIdentAtArgsOfCtor(arg)) }
            } );

            let rhs = arm.t;
            let t = translate_parametric_term(rhs, args, regctx)?;

            Ok(( ctor_id, t ))
        }
        else { Err(TranslateErr::UndefinedIdent(ident)) }
    }
    else { Err(TranslateErr::ExpectedIdent(ctor)) }
}

fn translate_abs(x: ast::Ident, A: ast::TermWithPos, t: ast::TermWithPos, regctx: &mut RegisterCtx)
    -> Result<typechk::HoledAbs, TranslateErr>
{
    regctx.ac_push_temporary( x, |regctx, _| {
        Ok( core::typechk::HoledAbs {
            A: translate_term(A, regctx)?,
            t: translate_term(t, regctx)?,
        } )
    } )
}

fn translate_parametric_term<I>(term: ast::TermWithPos, mut params: I, regctx: &mut RegisterCtx)
    -> Result<Rc<typechk::HoledTerm>, TranslateErr>
    where I: Iterator<Item = Result<ast::Ident, TranslateErr>>
{
    let hole = Rc::new(typechk::HoledTerm::Hole(None));
    if let Some(param) = params.next() {
        regctx.ac_push_temporary( param?, |regctx, _name| Ok( Rc::new(typechk::HoledTerm::Lam(
            typechk::HoledAbs{A: hole.clone(), t: translate_parametric_term(term, params, regctx)?}
        )) ) )
    }
    else { translate_term(term, regctx) }
}

#[derive(Clone)]
struct AbsCtx {
    vars: Vec<String>,
}
impl AbsCtx {
    fn new() -> Self { AbsCtx{vars: Vec::new()} }

    fn dbi(&self, ident: &str) -> Option<u64> {
        self.vars.iter().position(|var| var == ident).map(|i| (self.vars.len() - i) as u64)
    }
}

fn translate_literal(lit: ast::Lit, regctx: &mut RegisterCtx) -> Result<Rc<typechk::HoledTerm>, TranslateErr> {
    use std::iter;

    Ok( match lit {
        ast::Lit::Nat(n) => Rc::new( typechk::HoledTerm::Value(typechk::Value::Nat(n)) ),
        ast::Lit::Int(i) => Rc::new( typechk::HoledTerm::Value(typechk::Value::Int(i)) ),
        ast::Lit::Str(s) => Rc::new( typechk::HoledTerm::Value(typechk::Value::Str(s)) ),
        ast::Lit::Tuple(ts) => {
            let cons = Rc::new(typechk::HoledTerm::Const( regctx.scope.resolve(iter::once("Tuple"), "Cons").unwrap() ));
            let nil = Rc::new(typechk::HoledTerm::Const( regctx.scope.resolve(iter::once("Tuple"), "Nil").unwrap() ));

            ts.into_iter().try_fold( nil, |t, head| -> Result<_, TranslateErr> {
                Ok(Rc::new(
                    typechk::HoledTerm::App{
                        s: Rc::new( typechk::HoledTerm::App{s: cons.clone(), t: translate_term(head, regctx)? } ),
                        t: t
                    }
                ))
            } )?
        },
    } )
}

fn register_module(regctx: &mut RegisterCtx, ast_module: ast::Module) -> Result<(), TranslateErr>
{
    register_env(regctx, ast_module.env)?;

    for child in ast_module.children {
        register_module(regctx, *child)?;
    }

    Ok(())
}

fn register_env(regctx: &mut RegisterCtx, ast_env: ast::Env) -> Result<(), TranslateErr> {
    use std::iter;

    assert_eq!(regctx.consts.len(), regctx.scope.next_cid());

    let ast::Env(statements) = ast_env;
    for statement in statements {
        match statement {
            ast::Statement::Datatype{header, ctors} => {
                let (name, params) = coerce_name_with_params(header)?;

                let datatype_cid =
                    register_const(regctx, iter::empty(), name.clone(), UntranslatedConst::DataType{type_: T})?;

                let m = core::modules::add_child(&regctx.scope.module(), name.clone());

                println!("{:?}", ctors);

                let ctors_id: Vec<core::ConstId> =
                    ctors.into_iter().enumerate().map( |(ctor_id, ctor)| {
                        let ctor_cid =
                            register_const(regctx, iter::once(name.clone()), coerce_name(ctor.patn)?,
                                UntranslatedConst::Ctor{datatype: datatype_cid, type_: ctor.T})?;
                        
                        regctx.ctor_info.insert(ctor_cid, CtorInfo{datatype: datatype_cid, ctor_id});

                        Ok( ctor_cid )
                    } ).collect::<Result<_,TranslateErr>>()?;

                regctx.datatype_info.insert(datatype_cid, DataTypeInfo{ctors: ctors_id});
            }
            ast::Statement::Def(lhs,rhs) => {
                let (name, params) = unfold_app_chain(lhs.clone());

                if let ast::Term::Ident(i) = *name.term {
                    let mut param_names = Vec::with_capacity(params.len());
                    for param in params {
                        if let ast::Term::Ident(i) = *param.term {
                            param_names.push(i);
                        }
                        else { return Err(TranslateErr::InvalidDefLhsParam(param)); }
                    }

                    register_const( regctx, iter::empty(), coerce_name(i)?,
                        UntranslatedConst::Def{param_names, rhs} )?;
                }
                else { return Err(TranslateErr::InvalidDefLhs(lhs)); }
            }
            ast::Statement::Typing(ast::Typing{x,T}) =>
                regctx.typings.push(UntranslatedTyping{typed: x, type_: T}),
        }
    }
    
    Ok(())
}

fn register_const<Q: IntoIterator<Item=String> + Clone>(
    regctx: &mut RegisterCtx,
    qualifier: Q, identifier: String,
    c: UntranslatedConst,
)
    -> Result<core::ConstId, TranslateErr>
{
    let cid = regctx.scope.next_cid();
    assert_eq!(cid - regctx.scope.base_cid(), regctx.consts.len());

    Rc::make_mut(&mut regctx.scope).register_const(qualifier, identifier);
    regctx.consts.push(c);

    Ok(cid)
}

fn coerce_name_with_params(term: ast::TermWithPos) -> Result<(String, Vec<String>), TranslateErr> {
    let (name, params) = unfold_app_chain(term.clone());

    if let ast::Term::Ident(ident) = *name.term {
        let mut param_names = Vec::with_capacity(params.len());
        for param in params {
            if let ast::Term::Ident(i) = *param.term {
                param_names.push(coerce_name(i)?);
            }
            else { return Err(TranslateErr::ExpectedNameWithParams(param)); }
        }
        
        Ok((ident, param_names))
    }
    else {
        Err(TranslateErr::ExpectedIdent(term))
    }
}

#[derive(Clone)]
struct RegisterCtx {
    env: core::Env,
    scope: Rc<core::modules::Scope>,
    consts: Vec<UntranslatedConst>,
    typings: Vec<UntranslatedTyping>,
    ac: AbsCtx,
    ctor_info: HashMap<core::ConstId, CtorInfo>,
    datatype_info: HashMap<core::ConstId, DataTypeInfo>,
    errors: Vec<TranslateErr>,
}
impl RegisterCtx {
    fn new(scope: core::modules::Scope) -> Self {
        RegisterCtx {
            env: core::Env::new(),
            scope: Rc::new(scope),
            consts: Vec::new(),
            typings: Vec::new(),
            ac: AbsCtx::new(),
            ctor_info: HashMap::new(),
            datatype_info: HashMap::new(),
            errors: Vec::new(),
        }
    }

    fn ac_push_temporary<F, B>(&mut self, ident: ast::Ident, f: F) -> Result<B, TranslateErr>
        where F: FnOnce(&mut Self, String) -> Result<B, TranslateErr>,
    {
        let name = coerce_name(ident.clone())?;
        if self.ac.vars.iter().any(|var| *var == name) { return Err(TranslateErr::ConflictedVar(ident)); }
        self.ac.vars.push(name.clone());

        let b = f(self, name);

        self.ac.vars.pop();

        b
    }
}
#[derive(Clone)]
struct CtorInfo {
    datatype: core::ConstId,
    ctor_id: core::CtorId,
}
#[derive(Clone)]
struct DataTypeInfo {
    ctors: Vec<core::ConstId>,
}

#[derive(Clone)]
enum UntranslatedConst {
    Def{param_names: Vec<ast::Ident>, rhs: ast::TermWithPos},
    DataType{param_names: Vec<ast::Ident>},
    Ctor{datatype: core::ConstId, type_: ast::TermWithPos},
}

#[derive(Clone)]
struct UntranslatedTyping {
    typed: ast::TermWithPos,
    type_: ast::TermWithPos,
}

#[derive(Clone, Debug)]
pub enum TranslateErr {
    CantSpecifyNamespace(ast::Ident),
    InvalidDefLhs(ast::TermWithPos),
    InvalidDefLhsParam(ast::TermWithPos),
    UndefinedIdent(ast::Ident),
    UndefinedModule(ast::Ident),
    AmbiguousIdent(ast::Ident),
    ConflictedVar(ast::Ident),
    ExpectedIdent(ast::TermWithPos),
    ExpectedIdentOfCtor(ast::TermWithPos),
    ExpectedIdentAtArgsOfCtor(ast::TermWithPos),
    InvalidDataTypeParam(ast::TermWithPos),
    MismatchDataType{expr: ast::TermWithPos, arms_no: Vec<usize>},
    DuplicatedPatterns{expr: ast::TermWithPos, arms_no: Vec<usize>, ctor: core::ConstId},
    NonExhaustivePatterns{expr: ast::TermWithPos, ctors: Vec<core::CtorId>},
    ExpectedNameWithParams(ast::TermWithPos),
}
impl From<CoerceNameErr> for TranslateErr {
    fn from(e: CoerceNameErr) -> Self {
        match e {
            CoerceNameErr::CantSpecifyNamespace(i) => TranslateErr::CantSpecifyNamespace(i),
        }
    }
}

fn unfold_app_chain(app_chain: ast::TermWithPos) -> (ast::TermWithPos, Vec<ast::TermWithPos>) {
    let mut list = Vec::new();

    let mut rest = app_chain;
    let mut rest_term = *rest.term;
    while let ast::Term::App{f,x} = rest_term {
        list.push(x);
        rest = f;
        rest_term = *rest.term;
    }

    rest.term = Box::new(rest_term);
    (rest, list)
}

fn unfold_arrow_chain(app_chain: ast::TermWithPos) -> (Vec<ast::TermWithPos>, ast::TermWithPos) {
    let mut list = Vec::new();

    let mut rest = app_chain;
    let mut rest_term = *rest.term;
    while let ast::Term::Arrow{A,B} = rest_term {
        list.push(A);
        rest = B;
        rest_term = *rest.term;
    }

    rest.term = Box::new(rest_term);
    (list, rest)
}

fn coerce_name(ident: ast::Ident) -> Result<String, CoerceNameErr> {
    if !ident.domain.is_empty() { Err(CoerceNameErr::CantSpecifyNamespace(ident)) }
    else { Ok(ident.name) }
}
enum CoerceNameErr {
    CantSpecifyNamespace(ast::Ident),
}