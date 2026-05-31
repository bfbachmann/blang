use crate::analyzer::type_store::TypeKey;
use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};

/// Contains additional constraints for generic parameters on a type impl.
#[derive(Clone, Default, Debug)]
pub struct ImplConstraints {
    /// Maps generic type key to specs that it is assumed to implement for a given impl.
    generic_tk_to_spec_tks: HashMap<TypeKey, HashSet<TypeKey>>,
}

impl ImplConstraints {
    /// Adds a new constraint for the given parameter. Returns false if the parameter is already
    /// constrained.
    pub fn add_constraint(&mut self, param_tk: TypeKey, spec_tks: HashSet<TypeKey>) -> bool {
        match self.generic_tk_to_spec_tks.entry(param_tk) {
            Entry::Occupied(_) => false,
            Entry::Vacant(entry) => {
                entry.insert(spec_tks);
                true
            }
        }
    }

    /// Returns the set of specs that constrains the given param, if any.
    pub fn get_constraints(&self, param_tk: TypeKey) -> Option<&HashSet<TypeKey>> {
        self.generic_tk_to_spec_tks.get(&param_tk)
    }

    /// Returns true iff there are no constraints.
    pub fn is_empty(&self) -> bool {
        self.generic_tk_to_spec_tks.is_empty()
    }
    /// Returns the mapping from generic type key to the set of specs implemented by that
    /// generic type under these constraints.
    pub fn entries(&self) -> &HashMap<TypeKey, HashSet<TypeKey>> {
        &self.generic_tk_to_spec_tks
    }
}
