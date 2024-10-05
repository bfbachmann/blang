use std::fmt::{Debug, Formatter};

use crate::analyzer::ast::r#type::AType;

/// A key that is associated with an analyzed type inside the type store. This is actually just an
/// index into the Vec that the type store uses to store analyzed types.
pub type TypeKey = u64;

/// Stores analyzed types.
pub struct TypeStore {
    /// We're just using a Vec here because types should never be removed from the store after
    /// insertion, and Vecs allow for fast and simple access.
    types: Vec<AType>,
}

impl Debug for TypeStore {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        for (i, typ) in self.types.iter().enumerate() {
            writeln!(f, "{i}: {:#?}", typ)?;
        }

        Ok(())
    }
}

impl TypeStore {
    /// Creates a new empty type store.
    pub fn new() -> Self {
        TypeStore { types: vec![] }
    }

    /// Generates the type key to be used for the next stored type.
    fn new_type_key(&mut self) -> TypeKey {
        self.types.len() as TypeKey
    }

    /// Inserts `typ` into the store and returns the key that can be used to retrieve it.
    pub fn insert(&mut self, typ: AType) -> TypeKey {
        let key = self.new_type_key();
        self.types.push(typ);
        key
    }

    /// Replaces the existing type associated with `type_key`.
    pub fn replace(&mut self, type_key: TypeKey, typ: AType) {
        self.types[type_key as usize] = typ;
    }

    /// Gets the type associated with `key`. Panics if `key` is not assigned.
    pub fn must_get(&self, key: TypeKey) -> &AType {
        match self.types.get(key as usize) {
            Some(typ) => typ,
            None => panic!("type key {} not found", key),
        }
    }
}
