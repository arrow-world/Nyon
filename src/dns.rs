use std::collections::HashMap;

use super::current::{Context, DataTypeId, Type};

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct DNS<'a> {
    ctx: &'a Context,
    dt_names: HashMap<DataTypeId, DataTypeNames>,
    dt_names_inv: HashMap<String, DataTypeId>,
}
impl<'a> DNS<'a> {
    pub fn new(ctx: &'a Context) -> Self {
        DNS {
            ctx,
            dt_names: HashMap::new(),
            dt_names_inv: HashMap::new(),
        }
    }

    pub fn lookup_id(&self, id: DataTypeId) -> Option<&DataTypeNames> {
        self.dt_names.get(&id)
    }

    pub fn lookup_name(&self, name: &String) -> Option<DataTypeId> {
        self.dt_names_inv.get(name).cloned()
    }

    pub fn name_dt(&mut self, name: String, dt: DataTypeId) {
        self.dt_names_inv.insert(name.clone(), dt);
        self.dt_names.insert(dt, DataTypeNames{name, ctors: Vec::new()});
    }
}

#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub struct DataTypeNames {
    name: String,
    ctors: Vec<String>,
}

pub enum StdType {
    Unit,
}
impl From<StdType> for Type {
    fn from(x: StdType) -> Self {
        match x {
            StdType::Unit => 0.into(),
        }
    }
}