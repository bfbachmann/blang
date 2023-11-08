use crate::analyzer::ast::r#type::AType;

pub type TypeKey = u64;

#[derive(Debug)]
pub struct TypeStore {
    types: Vec<AType>,
}

impl TypeStore {
    pub fn new() -> Self {
        TypeStore { types: vec![] }
    }

    fn new_type_key(&mut self) -> TypeKey {
        self.types.len() as TypeKey
    }

    pub fn insert(&mut self, typ: AType) -> TypeKey {
        let key = self.new_type_key();
        self.types.push(typ);
        key
    }

    pub fn replace(&mut self, type_key: TypeKey, typ: AType) {
        self.types[type_key as usize] = typ;
    }

    pub fn must_get(&self, key: TypeKey) -> &AType {
        match self.types.get(key as usize) {
            Some(typ) => typ,
            None => panic!("type key {} not found", key),
        }
    }
}
