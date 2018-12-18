use std::collections::HashMap;
use std::rc::Rc;
use std::cell::RefCell;

pub type DataTypeId = u64; // Data Type ID
pub type CtorId = u64; // Constructor ID

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Term {
    Data { T: Type, cid: CtorId, args: Vec<Rc<RefCell<Term>>> }, // a term constructed by data constructor.
    Case{cases: Vec<(CaseTerm, Rc<RefCell<Term>>)>, otherwise: Option<Rc<RefCell<Term>>>},
    Value(Value), // a term represented by the processor's internal efficient representation.
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum CaseTerm {
    Data { T: Type, cid: CtorId, args: Vec<Rc<RefCell<CaseTerm>>> },
    Case{cases: Vec<(CaseTerm, Rc<RefCell<CaseTerm>>)>, otherwise: Rc<RefCell<Term>>},
    Value(Value),
    Hole,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Value { T: Type, data: *mut u8 }

pub fn type_check(term: &Term, ctx: &Context) -> Result<Type, TypeErr> {
    match term {
        Term::Data{T, cid, args} =>
            {
                let T_def = match T {
                    Type::Identified(id) => if let Some(x) = ctx.lookup_datatype(*id) { x.borrow().clone() }
                        else { return Err(TypeErr::UnkDataTypeId{tid: *id}); },
                    Type::Anonymous(x) => x.borrow().clone(),
                };
                if let AnonymousType::Ind(ind) = T_def {
                    if *cid >= ind.ctors.len() as u64 { return Err(TypeErr::InvalidCtorId); }
                    let ref ctor = ind.ctors[*cid as usize];
                    if args.len() != ctor.params.len() { return Err(TypeErr::ArgNumMismatch); }
                    for (i, (a, p)) in args.iter().zip(&ctor.params).enumerate() {
                        if type_check(&a.borrow(), ctx)? != *p {
                            return Err(TypeErr::ArgTypeMismatch(i as u64));
                        }
                    }
                    Ok(T.clone())
                }
                else {
                    Err(TypeErr::ConstructNonDataType)
                }
            }
        Term::Case{cases, otherwise} => unimplemented!(),
        Term::Value(Value{T, ..}) => Ok(T.clone()),
    }
}

pub enum TypeErr {
    UnkDataTypeId{tid: DataTypeId},
    ConstructNonDataType,
    InvalidCtorId,
    ArgNumMismatch,
    ArgTypeMismatch(u64),
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Type {
    Identified(DataTypeId),
    Anonymous(Rc<RefCell<AnonymousType>>),
}
impl From<Rc<RefCell<AnonymousType>>> for Type {
    fn from(x: Rc<RefCell<AnonymousType>>) -> Self {
        Type::Anonymous(x)
    }
}
impl From<DataTypeId> for Type {
    fn from(x: DataTypeId) -> Self {
        Type::Identified(x)
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum AnonymousType {
    Fun { sour: Type, tar: Type },
    Ind(Inductive),
}
impl AnonymousType {
    pub fn fun(sour: Type, tar: Type) -> Self { AnonymousType::Fun{sour, tar} }
    pub fn ind(ctors: Vec<(Vec<Type>, TargetDataType)>) -> Self {
        AnonymousType::Ind(
            Inductive{ ctors: ctors.into_iter().map(|ctor| DataConstructor{params: ctor.0, tar: ctor.1}).collect() }
        )
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Inductive {
    ctors: Vec<DataConstructor>,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct DataConstructor {
    params: Vec<Type>, // paramaters list
    tar: TargetDataType, // target data type id
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum TargetDataType {
    Self_,
    Other(DataTypeId),
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Context {
    datatypes: HashMap<DataTypeId, Rc<RefCell<AnonymousType>>>,
    next_id: DataTypeId,
}
impl Context {
    pub fn new() -> Self {
        Context { datatypes: HashMap::new(), next_id: 0 }
    }

    pub fn append_datatype(&mut self, t: Rc<RefCell<AnonymousType>>) -> DataTypeId {
        let id = self.next_id;
        self.datatypes.insert(id, t);
        self.next_id += 1;
        id
    }

    pub fn lookup_datatype(&self, id: DataTypeId) -> Option<Rc<RefCell<AnonymousType>>> {
        self.datatypes.get(&id).cloned()
    } 
}

#[derive(Clone)]
pub struct Function { pub sour: Type, pub tar: Type, pub f: fn(&mut Term) }