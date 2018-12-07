use std::collections::HashMap;
use std::rc::Rc;

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Current {
    tt,
    Product(Vec<Current>),
    Sum(Rc<Current>, u64, Vec<Type>),
    Data(ConstantTypeId, u64, Rc<Current>),
    Value(Value),
}

#[derive(Clone, Debug)]
pub struct Value { T: Rc<Type>, data: ValueData }
impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        self.T == other.T && match (&self.data, &other.data) {
            (ValueData::f32(f), ValueData::f32(g)) => f.to_bits() == g.to_bits(),
            (ValueData::f64(f), ValueData::f64(g)) => f.to_bits() == g.to_bits(),
            (a, b) => a == b,
        }
    }
}
impl Eq for Value {}

#[derive(Clone, PartialEq, Debug)]
pub enum ValueData {
    u64(u64),
    f32(f32),
    f64(f64),
    bytes(Vec<u8>),
}

pub fn type_of(current: &Current) -> Type {
    match current {
        Current::tt => Type::Unit,
        Current::Product(cs) => Type::Product(cs.iter().map(|x| type_of(&x)).collect()),
        Current::Sum(_c, _i, ts) => Type::Sum(ts.clone()),
        Current::Data(ct, _ctor, _c) => Type::Constant(*ct),
        Current::Value(Value{T, data}) => (**T).clone(),
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Type {
    Unit,
    Product(Vec<Type>),
    Sum(Vec<Type>),
    Constant(ConstantTypeId),
}

pub type ConstantTypeId = u64;

pub struct ConstantTypeSet(HashMap<ConstantTypeId, Type>);
impl ConstantTypeSet {
    pub fn new() -> Self {
        ConstantTypeSet(HashMap::new())
    }
}
impl Default for ConstantTypeSet {
    fn default() -> ConstantTypeSet {
        let mut map = HashMap::new();
        map.insert(0, Type::Sum(vec![Type::Unit; 2]));

        ConstantTypeSet(map)
    }
}

#[derive(Clone)]
pub struct Function(pub Type, pub Type, pub fn(&mut Current));