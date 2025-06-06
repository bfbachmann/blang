use crate::analyzer::ast::expr::AExpr;
use crate::analyzer::ast::ext::AExternFn;
use crate::analyzer::ast::func::AFn;
use crate::analyzer::ast::r#impl::AImpl;
use crate::analyzer::ident::{Ident, IdentKind, ModAlias, Usage};
use crate::analyzer::scope::{Scope, ScopeKind};
use crate::analyzer::type_store::TypeKey;
use crate::parser::ast::symbol::{Name, Symbol};
use crate::parser::ast::unresolved::UnresolvedType;
use crate::parser::FileID;
use std::collections::hash_map::Entry;
use std::collections::HashMap;

/// Stores information about code in a given module.
pub struct ModuleContext {
    /// Each scope on this stack corresponds to a scope in the program. Each scope will store
    /// information local to only that scope like variables (identifiers).
    scopes: Vec<Scope>,
    /// Maps file ID to a mapping from name to foreign identifier.
    imported_idents: HashMap<FileID, HashMap<String, Ident>>,
    /// The ID of the current file being analyzed.
    cur_file_id: Option<FileID>,
    /// The type key for the current `impl` or `spec` type.
    cur_self_type_key: Option<TypeKey>,
    /// Contains information about aliases for imported modules.
    mod_aliases: HashMap<FileID, HashMap<String, ModAlias>>,
    // Contains impl types and their specs for all unchecked impls blocks.
    unchecked_impls: Vec<(UnresolvedType, Option<Symbol>)>,

    // Analyzed values that need to be passed to codegen.
    fns: Vec<AFn>,
    impls: Vec<AImpl>,
    extern_fns: Vec<AExternFn>,
}

impl ModuleContext {
    /// Creates a new empty module context.
    pub fn new(primitive_types: &HashMap<String, TypeKey>) -> ModuleContext {
        let mut scope = Scope::new(ScopeKind::TopLevel, None);

        // Init scope with primitive types.
        for (name, type_key) in primitive_types {
            scope
                .insert_ident(Ident::new_type(
                    name.clone(),
                    true,
                    *type_key,
                    None,
                    Default::default(),
                ))
                .unwrap();
        }

        ModuleContext {
            scopes: Vec::from([scope]),
            imported_idents: Default::default(),
            cur_file_id: None,
            cur_self_type_key: None,
            mod_aliases: Default::default(),
            unchecked_impls: vec![],
            fns: vec![],
            impls: vec![],
            extern_fns: vec![],
        }
    }

    pub fn set_cur_file_id(&mut self, id: FileID) -> Option<FileID> {
        self.imported_idents.entry(id).or_default();

        self.cur_file_id.replace(id)
    }

    /// Inserts `ident` into the current scope. Return an error containing the existing identifier
    /// if there is a conflict.
    pub fn insert_ident(&mut self, ident: Ident) -> Result<(), &Ident> {
        // If the current scope is the top-level scope, make sure the ident doesn't collide with
        // imported idents.
        if self.scopes.len() == 1 {
            return self.insert_top_level_ident(ident);
        }

        self.scopes.last_mut().unwrap().insert_ident(ident)
    }

    fn insert_top_level_ident(&mut self, ident: Ident) -> Result<(), &Ident> {
        if let Some(existing) = self
            .imported_idents
            .get(self.cur_file_id.as_ref().unwrap())
            .unwrap()
            .get(&ident.name)
        {
            return Err(existing);
        }

        self.scopes.first_mut().unwrap().insert_ident(ident)
    }

    pub fn insert_imported_ident(&mut self, ident: Ident) -> Result<(), &Ident> {
        let cur_file_id = self.cur_file_id.unwrap();

        match self.imported_idents.entry(cur_file_id) {
            Entry::Occupied(o) => match o.into_mut().entry(ident.name.clone()) {
                Entry::Occupied(existing) => {
                    return Err(existing.into_mut());
                }
                Entry::Vacant(v) => {
                    v.insert(ident);
                }
            },

            Entry::Vacant(v) => {
                v.insert(HashMap::from([(ident.name.clone(), ident)]));
            }
        }

        Ok(())
    }

    fn get_imported_ident_mut(
        &mut self,
        name: &str,
        set_usage: Option<Usage>,
    ) -> Option<&mut Ident> {
        match self.imported_idents.get_mut(&self.cur_file_id.unwrap()) {
            Some(idents) => {
                let ident = idents.get_mut(name);

                match (ident, set_usage) {
                    (Some(ident), Some(usage)) => {
                        ident.usage = usage;
                        Some(ident)
                    }
                    (ident, _) => ident,
                }
            }
            None => None,
        }
    }

    fn get_imported_ident(&self, name: &str) -> Option<&Ident> {
        match self.imported_idents.get(&self.cur_file_id.unwrap()) {
            Some(idents) => idents.get(name),
            None => None,
        }
    }

    /// Pushes `scope` onto the stack.
    pub fn push_scope(&mut self, scope: Scope) {
        self.scopes.push(scope);
    }

    /// Pops the current scope from the stack and returns it.
    pub fn pop_scope(&mut self) -> Scope {
        self.scopes.pop().unwrap()
    }

    /// Returns the current scope.
    pub fn cur_scope(&self) -> &Scope {
        self.scopes.last().unwrap()
    }

    /// Returns all unused import identifiers.
    pub fn unused_imports(&self) -> (Vec<&Ident>, Vec<&ModAlias>) {
        let mut unused_idents = vec![];
        let mut unused_aliases = vec![];

        for map in self.imported_idents.values() {
            for ident in map.values() {
                if ident.is_unused() {
                    unused_idents.push(ident);
                }
            }
        }

        for map in self.mod_aliases.values() {
            for alias in map.values() {
                if alias.is_unused() {
                    unused_aliases.push(alias);
                }
            }
        }

        (unused_idents, unused_aliases)
    }

    pub fn unwind_to_top_scope(&mut self) -> Vec<Scope> {
        self.scopes.drain(1..).collect()
    }

    pub fn push_scopes(&mut self, scopes: Vec<Scope>) {
        self.scopes.extend(scopes);
    }

    /// Finds the scope with the given kind and returns it, if any. Searches the stack upwards from
    /// the current scope.
    pub fn get_scope_by_kind(&self, kind: &ScopeKind) -> Option<&Scope> {
        self.scopes
            .iter()
            .rev()
            .find(|scope| scope.kind.matches(kind))
    }

    /// Finds the scope with the given kind and returns it, if any. Searches the stack upwards from
    /// the current scope.
    pub fn get_scope_by_kind_mut(&mut self, kind: &ScopeKind) -> Option<&mut Scope> {
        self.scopes
            .iter_mut()
            .rev()
            .find(|scope| scope.kind.matches(kind))
    }

    /// Finds the top-level identifier declared in the module with the given name.
    pub fn get_top_level_ident(&self, name: &str) -> Option<&Ident> {
        self.scopes.first().unwrap().get_ident(name)
    }

    pub fn remove_unchecked_ident_from_cur_scope(&mut self, name: &str) -> Option<Ident> {
        self.scopes.last_mut().unwrap().remove_unchecked_ident(name)
    }

    pub fn drain_consts_and_statics(&mut self) -> (HashMap<String, AExpr>, HashMap<String, AExpr>) {
        self.scopes.first_mut().unwrap().drain_consts_and_statics()
    }

    /// Searches the stack for the identifier with the given name. Note that variables from parent
    /// functions aren't resolved because they can't be accessed from child functions.
    pub fn get_ident_mut(&mut self, name: &str, set_usage: Option<Usage>) -> Option<&mut Ident> {
        let maybe_ident = {
            if self.search_scopes(name).is_some() {
                self.search_scopes(name)
            } else {
                self.get_imported_ident_mut(name, set_usage)
            }
        };

        match (maybe_ident, set_usage) {
            (Some(ident), Some(usage)) => {
                ident.usage = usage;
                Some(ident)
            }
            (maybe_ident, _) => maybe_ident,
        }
    }

    fn search_scopes(&mut self, name: &str) -> Option<&mut Ident> {
        let mut allow_variables = true;

        for scope in self.scopes.iter_mut().rev() {
            let is_fn = matches!(scope.kind, ScopeKind::FnBody);

            if let Some(ident) = scope.get_ident_mut(name) {
                if allow_variables || !matches!(ident.kind, IdentKind::Variable { .. }) {
                    return Some(ident);
                }
            }

            if is_fn {
                allow_variables = false;
            }
        }

        None
    }

    pub fn get_ident(&self, name: &str) -> Option<&Ident> {
        let mut allow_variables = true;

        for scope in self.scopes.iter().rev() {
            if let Some(ident) = scope.get_ident(name) {
                if allow_variables || !matches!(ident.kind, IdentKind::Variable { .. }) {
                    return Some(ident);
                }
            }

            if matches!(scope.kind, ScopeKind::FnBody) {
                allow_variables = false;
            }
        }

        if let Some(existing) = self.get_imported_ident(name) {
            return Some(existing);
        }

        None
    }

    /// Searches for an identifier with the given name only in the current scope.
    pub fn get_ident_in_cur_scope(&self, name: &str) -> Option<&Ident> {
        match self.scopes.last().unwrap().get_ident(name) {
            Some(ident) => Some(ident),
            None if self.scopes.len() == 1 => self.get_imported_ident(name),
            None => None,
        }
    }

    /// Searches for an identifier with the given name only in the current scope and returns a
    /// mutable reference to it, if found.
    pub fn get_ident_in_cur_scope_mut(&mut self, name: &str) -> Option<&mut Ident> {
        self.scopes.last_mut().unwrap().get_ident_mut(name)
    }

    pub fn cur_self_type_key(&self) -> Option<TypeKey> {
        self.cur_self_type_key
    }

    pub fn set_cur_self_type_key(&mut self, type_key: Option<TypeKey>) {
        self.cur_self_type_key = type_key;
    }

    /// Inserts the given mod alias, or returns an error containing the existing alias with the
    /// same name.
    pub fn insert_mod_alias(&mut self, alias: ModAlias) -> Result<(), &ModAlias> {
        match self.mod_aliases.entry(alias.span.file_id) {
            Entry::Occupied(o) => match o.into_mut().entry(alias.name.clone()) {
                Entry::Occupied(existing) => {
                    return Err(existing.into_mut());
                }
                Entry::Vacant(entry) => {
                    entry.insert(alias);
                }
            },

            Entry::Vacant(v) => {
                v.insert(HashMap::from([(alias.name.clone(), alias)]));
            }
        }

        Ok(())
    }

    /// Gets the module ID that corresponds fo the given mod alias.
    pub fn get_mod_alias(&mut self, mod_name: &Name) -> Option<&ModAlias> {
        if let Some(aliases) = self.mod_aliases.get_mut(&mod_name.span.file_id) {
            if let Some(alias) = aliases.get_mut(&mod_name.value) {
                alias.usage = Usage::Read;
                return Some(alias);
            }
        }

        None
    }

    pub fn insert_unchecked_impl(&mut self, impl_type: UnresolvedType, maybe_spec: Option<Symbol>) {
        self.unchecked_impls.push((impl_type, maybe_spec));
    }

    pub fn unchecked_impls(&self) -> &Vec<(UnresolvedType, Option<Symbol>)> {
        &self.unchecked_impls
    }

    pub fn insert_fn(&mut self, func: AFn) {
        self.fns.push(func);
    }

    pub fn insert_impl(&mut self, impl_: AImpl) {
        self.impls.push(impl_);
    }

    pub fn insert_extern_fn(&mut self, extern_fn: AExternFn) {
        self.extern_fns.push(extern_fn);
    }

    pub fn drain_fns(&mut self) -> (Vec<AFn>, Vec<AImpl>, Vec<AExternFn>) {
        (
            std::mem::take(&mut self.fns),
            std::mem::take(&mut self.impls),
            std::mem::take(&mut self.extern_fns),
        )
    }
}
