use super::current::*;

use std::collections::HashMap;
use std::rc::Rc;

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Transition {
    Prod(Vec<Type>),
    Proj(Vec<Type>, u64),
    Inj(Vec<Type>, u64),
    Case(Vec<(Type, Rc<Transition>)>, Vec<Type>),
    Identity(Type),
    Cut(Type),
    Lifted(Type, Vec<Type>, Vec<Type>, fn(Current) -> Current),
}
impl Transition {
    pub fn prod(types: Vec<Type>) -> Self {
        Transition::Prod(types)
    }

    pub fn proj(types: Vec<Type>, index: u64) -> Option<Self> {
        if index as usize >= types.len() { None }
        else { Some( Transition::Proj(types, index) ) }
    }

    pub fn inj(types: Vec<Type>, index: u64) -> Option<Self> {
        if index as usize >= types.len() { None }
        else { Some( Transition::Inj(types, index) ) }
    }

    pub fn case(cases: Vec<(Type, Rc<Transition>)>, Y: Vec<Type>) -> Option<Self> {
        if cases.iter().all( |x| {
            let signature = x.1.signature();
            signature.input == [x.0.clone()] && signature.output == Y
        } ) {
            Some( Transition::Case(cases, Y) )
        }
        else { None }
    }

    pub fn identity(type_: Type) -> Self {
        Transition::Identity(type_)
    }

    pub fn cut(type_: Type) -> Self {
        Transition::Cut(type_)
    }

    pub fn lifted(f: Function) -> Option<Self> {
        if let Function(Type::Product(ts_in), Type::Product(ts_out), eval) = f {
            if let [ref state_type, ref input_type] = *ts_in.as_slice() {
                if let Type::Product(ref input_types) = input_type {
                    Some( Transition::Lifted(state_type.clone(), input_types.clone(), ts_out.clone(), eval) )
                }
                else { None }
            }
            else { None }
        }
        else { None }
    }

    pub fn apply(&self, state: &Current, input: &[Current]) -> (Current, Vec<Current>) {
        let signature = self.signature();

        assert_eq!( type_of(state), signature.state );
        assert_eq!( input.iter().map(|x| type_of(&x)).collect::<Vec<_>>(), signature.input );
        
        let (next_state, output) = match self {
            Transition::Prod(..) => ( Current::tt, vec![ Current::Product(input.into()) ] ),
            Transition::Proj(_ts, i) => match input[0] {
                Current::Product(ref cs) => ( Current::tt, vec![ cs[*i as usize].clone() ] ),
                _ => unreachable!(),
            },
            Transition::Inj(ts, i) => ( Current::tt,
                vec![ Current::Sum(Rc::new(input[0].clone()), *i, ts.clone()) ] ),
            Transition::Case(cases, _Y) => match &input[0] {
                Current::Sum(c, i, _ts) => cases[*i as usize].1.apply(state, &[ (**c).clone() ]),
                _ => unreachable!(),
            },
            Transition::Identity(..) => ( Current::tt, vec![ input[0].clone() ] ),
            Transition::Cut(..) => ( Current::tt, vec![] ),
            Transition::Lifted(_, _, _, eval) =>
                {
                    if let Current::Product(xs) = eval(
                        Current::Product(vec![ state.clone(), Current::Product(input.to_vec()) ])
                    ) {
                        if let Current::Product(ref output) = xs[1] {
                            (xs[0].clone(), output.clone())
                        }
                        else { unreachable!(); }
                    }
                    else { unreachable!(); }
                },
        };

        assert_eq!( type_of(&next_state), signature.state );
        assert_eq!( output.iter().map(|x| type_of(&x)).collect::<Vec<_>>(), signature.output );

        (next_state, output)
    }

    pub fn signature(&self) -> Signature {
        match self {
            Transition::Prod(ts) => Signature {
                state: Type::Unit,
                input: ts.clone(),
                output: vec![ Type::Product(ts.clone()) ],
            },
            Transition::Proj(ts, index) => Signature {
                state: Type::Unit,
                input: vec![ Type::Product(ts.clone()) ],
                output: vec![ ts[*index as usize].clone() ],
            },
            Transition::Inj(ts, index) => Signature {
                state: Type::Unit,
                input: vec![ ts[*index as usize].clone() ],
                output: vec![ Type::Sum(ts.clone()) ],
            },
            Transition::Case(cases, Y) => Signature {
                state: Type::Product( cases.iter().map(|x| x.1.signature().state).collect() ),
                input: vec![ Type::Sum( cases.iter().map(|x| x.0.clone()).collect() ) ],
                output: Y.clone(),
            },
            Transition::Identity(t) => Signature {
                state: Type::Unit,
                input: vec![ t.clone() ],
                output: vec![ t.clone() ],
            },
            Transition::Cut(t) => Signature {
                state: Type::Unit,
                input: vec![ t.clone() ],
                output: vec![],
            },
            Transition::Lifted(s, i, o, _) => Signature {
                state: s.clone(),
                input: i.clone(),
                output: o.clone(),
            },
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Signature {
    state: Type,
    input: Vec<Type>,
    output: Vec<Type>,
}

pub enum Composite {
    Node(Node),
    Serial(Box<Composite>, Box<Composite>, HashMap<u64, u64>, Signature),
    Recursive(Box<Composite>, HashMap<u64, u64>, Signature),
}
impl Composite {
    pub fn node(node: Node) -> Self {
        Composite::Node(node)
    }

    pub fn serial(A: Composite, B: Composite, connection: HashMap<u64, u64>) -> CompositeResult {
        if let Some(&i) = connection.keys().find(|&&xB| xB >= B.signature().input.len() as u64) {
            return Err(CompositeError::OutOfInputIndex(i));
        }
        if let Some(&i) = connection.values().find(|&&yA| yA >= A.signature().output.len() as u64) {
            return Err(CompositeError::OutOfOutputIndex(i));
        }

        if let Some((&i,&j)) = connection.iter().find( |&(&i,&j)|
            A.signature().output[j as usize] != B.signature().input[i as usize]
        ) {
            return Err(CompositeError::TypeError { input: j, output: i});
        }
        
        let (mut sigA, mut sigB) = (A.signature(), B.signature());
        sigA.input.extend(
            sigB.input.into_iter().enumerate().filter_map( |(i,t)|
                if connection.contains_key(&(i as u64)) { Some(t) }
                else { None }
            )
        );
        sigB.output.extend(sigA.output);
        let sig = Signature {
            state: Type::Product(vec![sigA.state, sigB.state]),
            input: sigA.input,
            output: sigB.output,
        };
        Ok( Composite::Serial(Box::new(A), Box::new(B), connection, sig) )
    }

    pub fn recursive(A: Composite, connection: HashMap<u64, u64>) -> CompositeResult {
        if let Some(&i) = connection.keys().find(|&&xA| xA >= (A.signature().input.len() as u64)) {
            return Err(CompositeError::OutOfInputIndex(i));
        }
        if let Some(&i) = connection.values().find(|&&yA| yA >= (A.signature().output.len() as u64)) {
            return Err(CompositeError::OutOfOutputIndex(i));
        }

        let sigA = A.signature();
        let stream_state_type = Type::Product(
            connection.keys().map(|&xA| A.signature().input[xA as usize].clone()).collect()
        );
        let sig = Signature {
            state: Type::Product(vec![sigA.state, stream_state_type]),
            input:
                sigA.input.into_iter().enumerate().filter_map( |(i,t)|
                    if connection.contains_key(&(i as u64)) { Some(t) }
                    else { None }
                ).collect(),
            output: sigA.output,
        };
        Ok( Composite::Recursive(Box::new(A), connection, sig) )
    }

    pub fn compile(&self) -> Transition {
        let sig = self.signature();
        let fun = Function(
            Type::Product(vec![sig.state, Type::Product(sig.input)]),
            Type::Product(sig.output),
            |c| {
                let (state, inputs) =
                    if let Current::Product(ref cs) = c {
                        (&cs[0], &cs[1])
                    }
                    else { unreachable!() };
                

                // Current::Product(vec![next_state, Current::Product(outputs)])
                unimplemented!()
            }
        );
        let tra = Transition::lifted(fun).unwrap();
        assert_eq!(tra.signature(), self.signature());
        tra
    }

    pub fn signature(&self) -> Signature {
        match self {
            Composite::Node(n) => n.transition.signature(),
            Composite::Serial(_, _, _, sig) => sig.clone(),
            Composite::Recursive(_, _, sig) => sig.clone(),
        }
    }
}

pub enum CompositeError {
    OutOfInputIndex(u64),
    OutOfOutputIndex(u64),
    TypeError { input: u64, output: u64 },
}

pub type CompositeResult = Result<Composite, CompositeError>;

#[derive(Clone)]
pub struct Node {
    transition: Transition,
    state: Current,
}
impl Node {
    pub fn input(&mut self, input: &[Current]) -> Vec<Current> {
        let (next_state, output) = self.transition.apply(&self.state, input);
        self.state = next_state;
        output
    }
}