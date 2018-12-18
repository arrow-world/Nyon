use super::current::*;
use super::dns::*;

pub type SigFunId = u64;

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum SigType {
    C(Type), // Continuous Time
    E(Type), // Event
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct SigVecType(Vec<SigType>);

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct SFType {
    input: SigVecType,
    output: SigVecType,
}

#[derive(Clone)]
pub enum SigFun {
    Const(SigFunId),
    Hold{T: Type, init: Value},
    Sample{T: Type},
    StatelessC{I: Vec<Type>, O: Vec<Type>, f: fn(&[&Value]) -> Value},
    Automaton{S: Type, I: Vec<Type>, O: Vec<Type>, f: fn(&Value, &[&Value]) -> (Value, Vec<Value>)},
}
impl SigFun {
    pub fn ty(&self) -> SFType {
        match self {
            SigFun::Const(sfid) => unimplemented!(),
            SigFun::Hold{T, ..} =>
                SFType {
                    input: SigVecType(vec![SigType::E(T.clone())]),
                    output: SigVecType(vec![SigType::C(T.clone())]),
                },
            SigFun::Sample{T} =>
                SFType {
                    input: SigVecType(vec![SigType::C(T.clone()), SigType::C(StdType::Unit.into())]),
                    output: SigVecType(vec![SigType::E(T.clone())]),
                },
            SigFun::StatelessC{I, O, ..} =>
                SFType {
                    input: SigVecType(I.iter().map(|T| SigType::C(T.clone())).collect()),
                    output: SigVecType(O.iter().map(|T| SigType::C(T.clone())).collect()),
                },
            SigFun::Automaton{I, O, ..} =>
                SFType {
                    input: SigVecType(I.iter().map(|T| SigType::E(T.clone())).collect()),
                    output: SigVecType(O.iter().map(|T| SigType::E(T.clone())).collect()),
                },
        }
    }
}