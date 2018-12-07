use std::collections::{HashMap, HashSet};
use std::cell::RefCell;

use super::current::*;

pub type OperatorId = u64;

pub struct Operator {
    id: OperatorId,
    inputs_type: Vec<Type>,
    outputs_type: Vec<Type>,
}

pub struct OperatorSet {
    operators: HashMap<OperatorId, RefCell<Operator>>,
}
impl OperatorSet {
    pub fn new() -> Self {
        OperatorSet {
            operators: HashMap::new(),
        }
    }

    pub fn insert(&mut self, id: OperatorId, inputs_type: Vec<Type>, outputs_type: Vec<Type>) {
        self.operators.insert(id, RefCell::new(Operator { id, inputs_type, outputs_type }));
    }

    pub fn remove(&mut self, id: OperatorId) -> bool {
        self.operators.remove(&id).is_some()
    }

    pub fn tryget(&self, id: OperatorId) -> Result<&RefCell<Operator>, OperatorSetError> {
        match self.operators.get(&id) {
            Some(operator) => Ok(&operator),
            None => Err(OperatorSetError::OperatorNotExist(id)),
        }
    }
}

pub enum OperatorSetError {
    OperatorNotExist(OperatorId),
}

pub enum StreamType {
    Continuous(Type),
    Discrete(Type),
}

pub type StreamId = u64;

pub struct Stream {
    id: StreamId,
    stream_type: StreamType,
    source_terminal: Option<OutputTerminal>,
    target_terminal: Option<InputTerminal>,
}

pub enum StreamTerminal {
    Source(StreamId),
    Target(StreamId),
}

pub type NodeId = u64;

pub struct Node {
    id: NodeId,
    operator: OperatorId,
    input_stream: Option<StreamId>,
    output_stream: HashSet<StreamId>,
}

pub type InputPortId = u64;
pub type OutputPortId = u64;

pub struct InputTerminal {
    node: NodeId,
    port: InputPortId,
}
pub struct OutputTerminal {
    node: NodeId,
    port: OutputPortId,
}

pub enum Terminal {
    Input(InputTerminal),
    Output(OutputTerminal),
}
impl From<InputTerminal> for Terminal {
    fn from(x: InputTerminal) -> Self { Terminal::Input(x) }
}
impl From<OutputTerminal> for Terminal {
    fn from(x: OutputTerminal) -> Self { Terminal::Output(x) }
}

pub struct Net {
    nodes: HashMap<NodeId, RefCell<Node>>,
    streams: HashMap<StreamId, RefCell<Stream>>,
    operator_set: OperatorSet,
}
impl Net {
    pub fn insert_node(&mut self, id: NodeId, operator: OperatorId) {
        let node = Node {
            id, operator,
            input_stream: None,
            output_stream: HashSet::new(),
        };
        self.nodes.insert(id, RefCell::new(node));
    }

    pub fn insert_stream(&mut self, id: StreamId, stream_type: StreamType) {
        let stream = Stream {
            id, stream_type,
            source_terminal: None,
            target_terminal: None,
        };
        self.streams.insert(id, RefCell::new(stream));
    }

    pub fn remove_node(&mut self, id: NodeId) -> bool {
        self.nodes.remove(&id).is_some()
    }

    pub fn remove_stream(&mut self, id: StreamId) -> bool {
        self.streams.remove(&id).is_some()
    }

    fn tryget_node(&self, id: NodeId) -> Result<&RefCell<Node>, NetError> {
        match self.nodes.get(&id) {
            Some(node) => Ok(&node),
            None => Err(NetError::NodeNotExist(id)),
        }
    }

    fn tryget_stream(&self, id: StreamId) -> Result<&RefCell<Stream>, NetError> {
        match self.streams.get(&id) {
            Some(stream) => Ok(&stream),
            None => Err(NetError::StreamNotExist(id)),
        }
    }

    pub fn attach_source(&mut self, stream_id: StreamId, output_terminal: OutputTerminal) -> Result<(), NetError> {
        let mut stream = self.tryget_stream(stream_id)?.borrow_mut();
        let mut node = self.tryget_node(output_terminal.node)?.borrow_mut();

        if stream.source_terminal.is_some() {
            return Err(NetError::OccupiedStreamSource(stream_id));
        }

        stream.source_terminal = Some(output_terminal);
        node.output_stream.insert(stream_id);

        Ok(())
    }

    pub fn attach_target(&mut self, stream_id: StreamId, input_terminal: InputTerminal) -> Result<(), NetError> {
        let mut stream = self.tryget_stream(stream_id)?.borrow_mut();
        let mut node = self.tryget_node(input_terminal.node)?.borrow_mut();

        if stream.target_terminal.is_some() {
            return Err(NetError::OccupiedStreamTarget(stream_id));
        }
        if node.input_stream.is_some() {
            return Err(NetError::OccupiedInputTerminal(input_terminal));
        }

        stream.target_terminal = Some(input_terminal);
        node.input_stream = Some(stream_id);

        Ok(())
    }
}

pub enum NetError {
    NodeNotExist(NodeId),
    StreamNotExist(StreamId),
    OccupiedInputTerminal(InputTerminal),
    OccupiedStreamSource(StreamId),
    OccupiedStreamTarget(StreamId),
}