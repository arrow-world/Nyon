use syntax::loc_range;
use syntax::ast;
use syntax::ext;
use core;
use core::typechk;

use core::errors::TranslateErr as TranslateErrWithoutLoc;

use syntax::{Loc, loc};

use std::rc::Rc;
use std::collections::HashMap;

pub(crate) type TranslateErr = (TranslateErrWithoutLoc, Loc);

pub fn translate_module<'a>(ast: ast::Module) -> (Option<core::Env>, Rc<core::modules::Scope>, Vec<TranslateErr>) {
    let mut regctx = RegisterCtx::new(core::modules::Scope::top(), 0);

    let (mut sub_regctxs, next_cid) = register_module(&mut regctx, ast);
    regctx.next_cid = next_cid;

    if ! regctx.errors.is_empty() || sub_regctxs.iter().any(|regctx| ! regctx.errors.is_empty()) {
        return ( None, regctx.scope,
            regctx.errors.into_iter().chain(sub_regctxs.into_iter().map(|regctx| regctx.errors).flatten()).collect()
        );
    }

    regctx.datatype_info.extend( sub_regctxs.iter_mut().map(|r| r.datatype_info.drain()).flatten() );
    regctx.ctor_info.extend( sub_regctxs.iter_mut().map(|r| r.ctor_info.drain()).flatten() );

    sub_regctxs.iter_mut().for_each(|r| r.datatype_info.extend(regctx.datatype_info.iter().map(|(x,y)| (*x, y.clone()))));
    sub_regctxs.iter_mut().for_each(|r| r.ctor_info.extend(regctx.ctor_info.iter().map(|(x,y)| (*x, y.clone()))));

    translate_all(&mut regctx).unwrap_or_else( |e| {
        regctx.errors.push(e);
    } );

    for mut sub_regctx in sub_regctxs {
        translate_all(&mut sub_regctx).unwrap_or_else( |e| {
            sub_regctx.errors.push(e);
        } );
        regctx.env.extend(sub_regctx.env);
        regctx.errors.extend(sub_regctx.errors);
    }

    (Some(regctx.env), regctx.scope, regctx.errors)
}

fn translate_all(regctx: &mut RegisterCtx) -> Result<(), TranslateErr> {
    assert_eq!(regctx.consts.len(), regctx.scope.names().len());

    regctx.env.consts.reserve(regctx.consts.len());
    for (c, loc) in regctx.consts.split_off(0) {
        let c = translate_const(c, regctx.env.consts.len(), regctx).map_err(|e| regctx.errors.push(e)).ok();
        regctx.env.consts.push(c.map( |c| (c, loc) ));
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

fn translate_const(c: UntranslatedConst, id: core::ConstId, regctx: &mut RegisterCtx)
    -> Result<typechk::HoledConst, TranslateErr>
{
    Ok( match c {
        UntranslatedConst::Def{params, ret_type, rhs} => {
            let params = params.into_iter();

            typechk::HoledConst::Def {
                rhs: translate_parametric_term(rhs, params.clone(), regctx,
                    |abs, implicit| typechk::HoledTerm::Lam(abs, implicit))?,
                type_:
                    translate_parametric_term(
                        ret_type.unwrap_or(ast::TermWithLoc{term: Box::new(ast::Term::Hole(None)), start: 0, end: 0}),
                        params, regctx, |abs,_| (*abs.t.0).clone(),
                    )?,
            }
        },
        UntranslatedConst::DataType{params, ret_type} => {
            let (gadt_params, gadt_type) = {
                let gadt_params_len = params.len();

                let type_ = translate_parametric_term(
                    ret_type.unwrap_or(ast::TermWithLoc{term: Box::new(ast::Term::Hole(None)), start: 0, end: 0}),
                    params.into_iter(), regctx, |abs, implicit| typechk::HoledTerm::Pi(abs, implicit),
                )?;

                unfold_pi_chain(type_, gadt_params_len)
            };

            typechk::HoledConst::DataType {
                param_types: gadt_params,
                type_: gadt_type,
                ctors: regctx.datatype_info[&id].ctors.clone(),
            }
        },
        UntranslatedConst::Ctor{datatype, type_} => {
            let datatype_params = regctx.datatype_info[&datatype].params.clone();

            let datatype_param_names = datatype_params.iter().map(|s| s.name.0.as_str()).collect();

            let occurred = list_occurred(&type_.term, &datatype_param_names);
                
            let datatype_params_part = 
                datatype_params.iter().enumerate().filter(|(i,_)| occurred.contains(i)).map(|(_,p)| p.clone());
            
            let translated_type = translate_parametric_term(type_, datatype_params_part, regctx,
                |abs, _implicit| typechk::HoledTerm::Pi(abs, true))?;
            
            typechk::HoledConst::Ctor{datatype, type_: translated_type}
        },
    } )
}

fn list_occurred(term: &ast::Term, vars: &Vec<&str>) -> Vec<usize>
{
    let mut list = Vec::new();
    list_occurred_accum(term, vars, &mut list);
    return list;
}

pub(crate) fn list_occurred_accum(term: &ast::Term, vars: &Vec<&str>, list: &mut Vec<usize>) {
    match term {
        ast::Term::Ident(a) =>
            if let Some(i) = vars.iter().position(|b| a.name == *b && a.domain.is_empty()) {
                list.push(i)
            },
        ast::Term::AppChain{f, args} => {
            list_occurred_accum(&f.term, vars, list);
            for (arg, _implicit) in args { list_occurred_accum(&arg.term, vars, list); }
        },
        ast::Term::Pi{A, B, ..} => {
            list_occurred_accum(&A.term, vars, list);
            list_occurred_accum(&B.term, vars, list);
        },
        ast::Term::Arrow{A, B} => {
            list_occurred_accum(&A.term, vars, list);
            list_occurred_accum(&B.term, vars, list);
        },
        ast::Term::Typing(ast::Typing{x, T}) => {
            list_occurred_accum(&x.term, vars, list);
            list_occurred_accum(&T.term, vars, list);
        },
        ast::Term::Let{env: ast::Env(statements), body} => {
            for (statement, _loc) in statements {
                match statement {
                    ast::Statement::Datatype{header, ctors} => {
                        list_occurred_accum(&header.term, vars, list);
                        for ctor in ctors { list_occurred_accum(&ctor.term, vars, list); }
                    },
                    ast::Statement::Def(lhs, rhs) => {
                        list_occurred_accum(&lhs.term, vars, list);
                        list_occurred_accum(&rhs.term, vars, list);
                    },
                    ast::Statement::Typing(ast::Typing{x, T}) => {
                        list_occurred_accum(&x.term, vars, list);
                        list_occurred_accum(&T.term, vars, list);
                    },
                    ast::Statement::Module{..} => unreachable!(),
                }
            }
            list_occurred_accum(&body.term, vars, list);
        },
        ast::Term::Lam{A, t, ..} => {
            list_occurred_accum(&A.term, vars, list);
            list_occurred_accum(&t.term, vars, list);
        },
        ast::Term::Case{t, arms} => {
            list_occurred_accum(&t.term, vars, list);
            for (ast::Arm{patn, t}, _loc) in arms {
                list_occurred_accum(&patn.term, vars, list);
                list_occurred_accum(&t.term, vars, list);
            }
        },
        ast::Term::If{p, tv, fv} => {
            list_occurred_accum(&p.term, vars, list);
            list_occurred_accum(&tv.term, vars, list);
            list_occurred_accum(&fv.term, vars, list);
        },
        ast::Term::Ext(et) => ext::list_occurred(et, vars, list),
        ast::Term::Universe => (),
        ast::Term::Hole(..) => (),
    }
}

pub(crate) fn translate_term(term_withloc: ast::TermWithLoc, regctx: &mut RegisterCtx)
    -> Result<(Rc<core::HoledTerm>, Loc), TranslateErr>
{
    let term = *term_withloc.term.clone();
    let l = loc(&term_withloc);

    let t = match term {
        ast::Term::Ident(i) => Rc::new(
            regctx.scope.resolve_from_ident(&i)
                .map(|cid| core::HoledTerm::Const(cid))
                .or_else(|| regctx.ac.dbi(&i.name).map(|dbi| core::HoledTerm::DBI(dbi)))
                .ok_or((TranslateErrWithoutLoc::UndefinedIdent(i), l))?
        ),
        ast::Term::Universe => Rc::new( core::HoledTerm::Universe ),
        ast::Term::AppChain{f, args} => {
            let f_start = f.start;

            args.into_iter().try_fold(
                translate_term(f, regctx)?,
                |f, (x, implicit)| {
                    let x_end = x.end;
                    Ok(( Rc::new(core::HoledTerm::App{
                        s: f,
                        t: translate_term(x, regctx)?,
                        implicit
                    }), loc_range(f_start, x_end) ))
                },
            )?.0
        },
        /*Rc::new( core::HoledTerm::App {
            s: translate_term(f, regctx)?,
            t: translate_term(x, regctx)?,
        } )*/
        ast::Term::Lam{x, A, t} =>
            Rc::new( core::HoledTerm::Lam(translate_abs(coerce_name(x)?, A, t, regctx)?, false) ),
        ast::Term::Pi{x, A, B, implicit} =>
            Rc::new( core::HoledTerm::Pi(translate_abs(coerce_name(x)?, A, B, regctx)?, implicit) ),
        ast::Term::Arrow{A, B} => {
            // Adds anonymous dummy variable to abstraction context for alignment of De-Bruijn-Indices.
            Rc::new( core::HoledTerm::Pi(translate_arrow(A, B, regctx)?, false) )
        },
        ast::Term::Typing(ast::Typing{x,T}) => {
            let x = translate_term(x, regctx)?;
            let T = translate_term(T, regctx)?;
            regctx.env.typings.push(Some( (x.clone(), T) ));

            let (t, _loc) = x;
            t
        },
        ast::Term::Let{env: letenv, body} => {
            let mut local_regctx =
                RegisterCtx::new(core::modules::Scope::new(
                    regctx.scope.module(),
                    regctx.scope.clone(),
                ), regctx.next_cid);

            register_env(&mut local_regctx, letenv, true);
            if !local_regctx.errors.is_empty() {
                return Err((TranslateErrWithoutLoc::LocalEnvRegErr(local_regctx.errors), None));
            }
            let t = translate_term(body, &mut local_regctx)?;

            translate_all(&mut local_regctx)?;

            Rc::new( core::HoledTerm::Let{env: local_regctx.env.into(), t} )
        },
        ast::Term::Case{t, arms} => {
            let translated_arms: Vec<(CtorInfo, (Rc<typechk::HoledTerm>, Loc))> = arms.into_iter().map( |arm| {
                let ctor_err = (TranslateErrWithoutLoc::ExpectedIdentOfCtor, loc(&arm.0.patn));

                let (ctor_cid, body) = translate_arm(arm.0, regctx)?;
                regctx.ctor_info.get(&ctor_cid).map(|ctor_info| (ctor_info.clone(), body)).ok_or(ctor_err)
            } ).collect::<Result<_,_>>()?;

            let datatype = translated_arms.first().map(|(ctor_info,_)| ctor_info.datatype);

            if let Some(datatype) = datatype {
                let mismatch_datatype_arms: Vec<usize> =
                    translated_arms.iter().enumerate()
                        .filter(|(_, (ctor_info,_))| ctor_info.datatype != datatype).map(|(arm_no, _)| arm_no)
                        .collect();
                if !mismatch_datatype_arms.is_empty() {
                    regctx.errors.extend(
                        mismatch_datatype_arms.into_iter().map( |arm_no| 
                            (TranslateErrWithoutLoc::MismatchDataType{arm_no}, (translated_arms[arm_no].1).1.clone())
                        )
                    );
                }
            }

            let mut cases = vec![ (None, vec![]);
                datatype.map(|datatype| regctx.datatype_info[&datatype].ctors.len()).unwrap_or(0)];
            for (arm_no, (ctor_info, body)) in translated_arms.iter().enumerate() {
                let (ref mut case_body, ref mut arms_no) = cases[ctor_info.ctor_id];
                if case_body.is_none() {
                    *case_body = Some(body.clone());
                }
                arms_no.push(arm_no);
            }
            let cases = cases;
            
            let duplicated_cases: Vec<_> = cases.iter().filter(|(_,arms_no)| arms_no.len() > 1)
                .map(|(_,arms_no)| arms_no.clone()).collect();
            if !duplicated_cases.is_empty() {
                for (ctor_id, arms_no) in duplicated_cases.into_iter().enumerate() {
                    let ctor = regctx.datatype_info[&datatype.unwrap()].ctors[ctor_id];
                    let err_loc =
                        arms_no.iter().map(|arm_no| (translated_arms[*arm_no].1).1.clone().unwrap())
                            .flatten().collect();
                    regctx.errors.push((
                        TranslateErrWithoutLoc::DuplicatedPatterns{ctor, arms_no},
                        Some(err_loc),
                    ));
                }
            }

            let non_exhaustive_cases: Vec<_> = cases.iter()
                .enumerate().filter(|(_, (case_body,_))| case_body.is_none()).map(|(i,_)| i).collect();
            if !non_exhaustive_cases.is_empty() {
                regctx.errors.extend(
                    non_exhaustive_cases.into_iter().map( |ctor| (
                        TranslateErrWithoutLoc::NonExhaustivePattern{ctor},
                        l.clone(),
                    ) )
                );
            }

            let hole = (Rc::new(typechk::HoledTerm::Hole(None)), None);

            Rc::new( core::HoledTerm::Case {
                t: translate_term(t, regctx)?,
                cases: cases.into_iter().map(|(case_body,_)| case_body.unwrap_or(hole.clone())).collect(),
                datatype,
            } )
        },
        ast::Term::If{..} => unimplemented!(),
        ast::Term::Ext(et) => ext::translate_ext_term(et, regctx)?,
        ast::Term::Hole(i) =>
            if let Some(i) = i {
                let hole_id = regctx.scope.resolve_namedhole(&i)
                    .map_or_else(|| {
                        let new = regctx.new_namedhole_id();
                        regctx.scope.register_namedhole(i, new)?;
                        Ok(new)
                    }, |hole_id| Ok(hole_id))?;
                
                Rc::new(typechk::HoledTerm::Hole(Some(hole_id)))
            }
            else { Rc::new(typechk::HoledTerm::Hole(None)) }
    };
    Ok(( t, loc(&term_withloc) ))
}

fn translate_typing(t: UntranslatedTyping, regctx: &mut RegisterCtx)
    -> Result<((Rc<core::HoledTerm>, Loc), (Rc<core::HoledTerm>, Loc)), TranslateErr>
{
    Ok( (
        translate_term(t.typed, regctx)?,
        translate_term(t.type_, regctx)?,
    ) )
}

fn translate_arm(arm: ast::Arm, regctx: &mut RegisterCtx)
    -> Result<(core::ConstId, (Rc<core::HoledTerm>, Loc)), TranslateErr>
{
    let (ctor, args) = unfold_app_chain(arm.patn);

    if let ast::Term::Ident(ident) = *ctor.term {
        if let Some(ctor_id) = regctx.scope.resolve_from_ident(&ident) {
            let args = args.into_iter().map( |(arg, implicit)| {
                if let ast::Term::Ident(ident) = *arg.term {
                    let name = coerce_name(ident)?;
                    let loc = name.1.clone();
                    Ok( Param{name, type_: None, implicit, loc} )
                }
                else { Err((TranslateErrWithoutLoc::ExpectedIdentAtArgsOfCtor, loc(&arg))) }
            } ).collect::<Result<Vec<_>,_>>()?;

            let rhs = arm.t;
            let t = translate_parametric_term(rhs, args.into_iter(), regctx,
                |abs, implicit| typechk::HoledTerm::Lam(abs, implicit))?;

            Ok(( ctor_id, t ))
        }
        else { Err((TranslateErrWithoutLoc::UndefinedIdent(ident.clone()), ident.loc)) }
    }
    else { Err((TranslateErrWithoutLoc::ExpectedIdent, loc(&ctor))) }
}

fn translate_abs(x: (String, Loc), A: ast::TermWithLoc, t: ast::TermWithLoc, regctx: &mut RegisterCtx)
    -> Result<typechk::HoledAbs, TranslateErr>
{
    Ok( core::typechk::HoledAbs {
        A: translate_term(A, regctx)?,
        t: regctx.ac_push_temporary( x, |regctx, _| translate_term(t, regctx) )?,
    } )
}

fn translate_arrow(A: ast::TermWithLoc, t: ast::TermWithLoc, regctx: &mut RegisterCtx)
    -> Result<typechk::HoledAbs, TranslateErr>
{
    Ok( core::typechk::HoledAbs {
        A: translate_term(A, regctx)?,
        t: regctx.ac_push_anonymous_temporary( |regctx| translate_term(t, regctx) )?,
    } )
}

fn translate_parametric_term<I, F>(term: ast::TermWithLoc, params: I, regctx: &mut RegisterCtx, abs_term: F)
    -> Result<(Rc<typechk::HoledTerm>, Loc), TranslateErr>
    where I: DoubleEndedIterator<Item = Param>,
          F: Fn(typechk::HoledAbs, bool) -> typechk::HoledTerm + Clone,
{
    fn translate_rest<I,F>(term: ast::TermWithLoc, mut params: I, regctx: &mut RegisterCtx, abs_term: F)
        -> Result<(Rc<typechk::HoledTerm>, Loc), TranslateErr>
        where I: Iterator<Item = Param>,
            F: Fn(typechk::HoledAbs, bool) -> typechk::HoledTerm + Clone,
    {
        let hole = Rc::new(typechk::HoledTerm::Hole(None));
        if let Some(param) = params.next() {
            let implicit = param.implicit;
            let A =
                if let Some(param_type) = param.type_ {
                    translate_term(param_type, regctx)?
                }
                else { (hole.clone(), None) };

            regctx.ac_push_temporary( param.name, |regctx, _name| Ok( Rc::new(abs_term.clone()(
                typechk::HoledAbs{A, t: translate_rest(term.clone(), params, regctx, abs_term)?},
                implicit,
            )) ) )
                .map( |t| (t, loc(&term)) )
        }
        else { translate_term(term, regctx) }
    }

    translate_rest(term, params, regctx, abs_term)
}

#[derive(Clone)]
struct AbsCtx {
    vars: Vec<String>,
}
impl AbsCtx {
    fn new() -> Self { AbsCtx{vars: Vec::new()} }

    fn dbi(&self, ident: &str) -> Option<u64> {
        self.vars.iter().position(|var| var == ident).map(|i| (self.vars.len() - i - 1) as u64)
    }

    fn is_empty(&self) -> bool { self.vars.is_empty() }
}

fn register_module(regctx: &mut RegisterCtx, ast_module: ast::Module)
    -> (Vec<RegisterCtx>, usize)
{
    let mut sub_regctxs = Vec::new();

    let inner_sub_modules = register_env(regctx, ast_module.env, false);

    let sub_modules = ast_module.children.into_iter().map(|m| (*m, None)).chain(inner_sub_modules);
    for (child, mod_name_loc) in sub_modules {
        let name = child.name.clone();

        let module = 
            match core::modules::add_child(&regctx.scope.module(), name.clone()) {
                Ok(m) => m,
                Err(_) => {
                    regctx.errors.push( (
                        TranslateErrWithoutLoc::ConflictedModuleName{name: name.clone()},
                        mod_name_loc
                    ) );
                    continue;
                },
            };
        
        let inner_scope = core::modules::Scope::new(module, regctx.scope.clone());
        let mut regctx_inner = RegisterCtx::new(inner_scope, regctx.next_cid);

        let (inner_sub_regctxs, next_cid) = register_module(&mut regctx_inner, child);
        sub_regctxs.push(regctx_inner);
        sub_regctxs.extend(inner_sub_regctxs);
        regctx.next_cid = next_cid;
    }

    (sub_regctxs, regctx.next_cid)
}

fn register_env(regctx: &mut RegisterCtx, ast_env: ast::Env, is_local: bool) -> Vec<(ast::Module, Loc)> {
    let mut child_modules = Vec::new();

    let ast::Env(statements) = ast_env;
    for (statement, l) in statements {
        let result = register_statement(regctx, statement, l, is_local);

        if let Ok(child_module) = result {
            child_modules.extend(child_module);
        }
        else {
            regctx.errors.extend( result.err() );
        }
    }

    child_modules
}

fn register_statement(regctx: &mut RegisterCtx, statement: ast::Statement, l: Loc, is_local: bool)
    -> Result<Option<(ast::Module, Loc)>, TranslateErr>
{
    use std::iter;

    match statement {
        ast::Statement::Datatype{header, ctors} => {
            let (name, params, ret_type) = decompose_defun(header)?;

            let datatype_cid =
                register_const( regctx, iter::empty(), name.0.clone(),
                    UntranslatedConst::DataType{params: params.clone(), ret_type}, l.clone() )?;

            core::modules::add_child(&regctx.scope.module(), name.0.clone())
                .map_err( |_| (TranslateErrWithoutLoc::ConflictedDatatypeName(name.0.clone()), name.1.clone()) )?;

            let ctors_id: Vec<core::ConstId> =
                ctors.into_iter().enumerate().map( |(ctor_id, ctor)| {
                    let (ctor_name, ctor_type) =
                        if let ast::Term::Typing(typing) = *ctor.term {
                            (coerce_ident(typing.x).and_then(|i| coerce_name(i).map_err(|e| e.into())), typing.T)
                        }
                        else { return Err((TranslateErrWithoutLoc::ExpectedTyping, loc(&ctor))); };

                    let ctor_cid =
                        register_const( regctx, iter::once(name.0.clone()), ctor_name?.0,
                            UntranslatedConst::Ctor{datatype: datatype_cid, type_: ctor_type}, l.clone() )?;
                    
                    regctx.ctor_info.insert(ctor_cid, CtorInfo{datatype: datatype_cid, ctor_id});

                    Ok( ctor_cid )
                } ).collect::<Result<_,TranslateErr>>()?;

            regctx.datatype_info.insert(datatype_cid, DataTypeInfo{ctors: ctors_id, params});
            Ok(None)
        }
        ast::Statement::Def(lhs,rhs) => {
            let (name, params, ret_type) = decompose_defun(lhs)?;
            register_const( regctx, iter::empty(), name.0, UntranslatedConst::Def{params, ret_type, rhs}, l )?;
            Ok(None)
        }
        ast::Statement::Typing(ast::Typing{x,T}) => {
            regctx.typings.push(UntranslatedTyping{typed: x, type_: T});
            Ok(None)
        },
        ast::Statement::Module{header, env} => {
            assert!(regctx.ac.is_empty());

            if is_local {
                return Err((TranslateErrWithoutLoc::ModuleDefInLocalScope, l));
            }

            let (name, name_loc) = coerce_ident(header).and_then(|i| coerce_name(i).map_err(|e| e.into()))?;

            Ok(Some((ast::Module{env, name, children: vec![]}, name_loc)))
        },
    }
}

fn register_const<Q: IntoIterator<Item=String> + Clone>(
    regctx: &mut RegisterCtx,
    qualifier: Q, identifier: String,
    c: UntranslatedConst, loc: Loc
)
    -> Result<core::ConstId, TranslateErr>
{
    let cid = regctx.next_cid;

    Rc::make_mut(&mut regctx.scope).register_const(qualifier, identifier, cid)
        .map_err(|s| (TranslateErrWithoutLoc::UndefinedModule{name: s}, loc.clone()))?;
    regctx.consts.push((c, loc));

    regctx.next_cid += 1;

    Ok(cid)
}

/* fn coerce_name_with_params(term: ast::TermWithLoc) -> Result<((String, Loc), Vec<(String, Loc)>), TranslateErr> {
    let (name, params) = unfold_app_chain(term.clone());

    if let ast::Term::Ident(ident) = *name.term {
        params.into_iter().map( |(param, implicit)|
            coerce_ident(param).and_then(|i| coerce_name(i).map_err( |e| e.into() ))
        )
            .collect::<Result<_,_>>()
            .and_then( |param_names| Ok((coerce_name(ident)?, param_names)) )
    }
    else { Err((TranslateErrWithoutLoc::ExpectedIdent, loc(&term))) }
} */

fn decompose_defun(term: ast::TermWithLoc)
    -> Result<((String, Loc), Vec<Param>, Option<ast::TermWithLoc>), TranslateErr>
{
    let (app, ret_type) =
        if let ast::Term::Typing(t) = *term.term {
            let ast::Typing{x,T} = t;
            (x, Some(T))
        }
        else {
            (term, None)
        };

    let (name, params) = unfold_app_chain(app.clone());

    if let ast::Term::Ident(ident) = *name.term {
        params.into_iter().map( |(param, implicit)| {
            let loc = loc(&param);
            let (param_name, type_) = decompose_param(param)?;
            Ok( Param{name: param_name, type_, implicit, loc} )
        } )
            .collect::<Result<_,_>>()
            .and_then( |param_names| Ok((coerce_name(ident)?, param_names, ret_type)) )
    }
    else { Err((TranslateErrWithoutLoc::ExpectedIdent, loc(&name))) }
}

fn decompose_param(param: ast::TermWithLoc) -> Result<((String, Loc), Option<ast::TermWithLoc>), TranslateErr> {
    let (param_name, type_) =
        if let ast::Term::Typing(t) = *param.term {
            let ast::Typing{x,T} = t;
            (x, Some(T))
        }
        else { (param, None) };

    Ok( (coerce_ident(param_name).and_then(|i| coerce_name(i).map_err(|e| e.into()))?, type_) )
}

fn coerce_ident(term: ast::TermWithLoc) -> Result<ast::Ident, TranslateErr> {
    if let ast::Term::Ident(i) = *term.term { Ok(i) }
    else { Err((TranslateErrWithoutLoc::ExpectedIdent, loc(&term))) }
}

#[derive(Clone)]
pub(crate) struct RegisterCtx {
    env: core::Env,
    pub(crate) scope: Rc<core::modules::Scope>,
    consts: Vec<(UntranslatedConst, Loc)>,
    typings: Vec<UntranslatedTyping>,
    ac: AbsCtx,
    ctor_info: HashMap<core::ConstId, CtorInfo>,
    datatype_info: HashMap<core::ConstId, DataTypeInfo>,
    errors: Vec<TranslateErr>,
    next_cid: ::core::ConstId,
}
impl RegisterCtx {
    fn new(scope: core::modules::Scope, next_cid: ::core::ConstId) -> Self {
        RegisterCtx {
            env: core::Env::new(),
            scope: Rc::new(scope),
            consts: Vec::new(),
            typings: Vec::new(),
            ac: AbsCtx::new(),
            ctor_info: HashMap::new(),
            datatype_info: HashMap::new(),
            errors: Vec::new(),
            next_cid,
        }
    }

    fn ac_push_temporary<F, B>(&mut self, name: (String, Loc), f: F) -> Result<B, TranslateErr>
        where F: FnOnce(&mut Self, String) -> Result<B, TranslateErr>,
    {
        let (name, name_loc) = name;

        if self.ac.vars.iter().any(|var| *var == name) {
            return Err((TranslateErrWithoutLoc::ConflictedVar(name), name_loc));
        }
        self.ac.vars.push(name.clone());

        let b = f(self, name);

        self.ac.vars.pop();

        b
    }

    fn ac_push_anonymous_temporary<F, B>(&mut self, f: F) -> Result<B, TranslateErr>
        where F: FnOnce(&mut Self) -> Result<B, TranslateErr>,
    {
        self.ac.vars.push("".into());

        let b = f(self);

        self.ac.vars.pop();

        b
    }

    fn new_namedhole_id(&mut self) -> usize {
        let id = self.env.nof_namedhole;
        self.env.nof_namedhole += 1;
        id
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
    params: Vec<Param>,
}

#[derive(Clone)]
enum UntranslatedConst {
    Def{params: Vec<Param>, ret_type: Option<ast::TermWithLoc>, rhs: ast::TermWithLoc},
    DataType{params: Vec<Param>, ret_type: Option<ast::TermWithLoc>},
    Ctor{datatype: core::ConstId, type_: ast::TermWithLoc},
    // PrimitiveCtor{datatype: core::ConstId, type_: ast::Term},
}

#[derive(Clone, Debug)]
struct Param {
    name: (String, Loc),
    type_: Option<ast::TermWithLoc>,
    implicit: bool,
    loc: Loc,
}

#[derive(Clone)]
struct UntranslatedTyping {
    typed: ast::TermWithLoc,
    type_: ast::TermWithLoc,
}

fn unfold_app_chain(app_chain: ast::TermWithLoc) -> (ast::TermWithLoc, Vec<(ast::TermWithLoc, bool)>) {
    let mut list = Vec::new();

    let mut rest = app_chain;
    let mut rest_term = *rest.term;
    while let ast::Term::AppChain{f, args} = rest_term {
        list.push(args);
        rest = f;
        rest_term = *rest.term;
    }

    let list = list.into_iter().rev().flatten().collect();

    rest.term = Box::new(rest_term);
    (rest, list)
}

fn unfold_pi_chain(pi_chain: (Rc<typechk::HoledTerm>, Loc), len: usize)
    -> (Vec<((Rc<typechk::HoledTerm>, Loc), bool)>, (Rc<typechk::HoledTerm>, Loc))
{
    let mut count = 0;

    let mut list = Vec::new();

    let mut rest = pi_chain;
    while let typechk::HoledTerm::Pi(typechk::HoledAbs{A: ref T, t: ref U}, implicit) = *rest.0.clone() {
        if count >= len { break; }

        list.push((T.clone(), implicit));
        rest = U.clone();

        count += 1;
    }

    (list, rest)
}

fn coerce_name(ident: ast::Ident) -> Result<(String, Loc), TranslateErr> {
    if !ident.domain.is_empty() { Err((TranslateErrWithoutLoc::CantSpecifyNamespace(ident.clone()), ident.loc)) }
    else { Ok((ident.name, ident.loc)) }
}