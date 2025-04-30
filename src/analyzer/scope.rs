use crate::analyzer::ast::expr::AExpr;
use crate::analyzer::ident::{Ident, IdentKind};
use crate::analyzer::type_store::TypeKey;
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::fmt;

/// Represents a kind of scope in which symbols can be defined.
#[derive(PartialEq, Clone, Debug)]
pub enum ScopeKind {
    TopLevel,
    FnBody,
    InlineClosure,
    BranchBody,
    LoopBody,
    FromBody,
    Params,
}

impl fmt::Display for ScopeKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ScopeKind::TopLevel => write!(f, "top-level"),
            ScopeKind::FnBody => write!(f, "function body"),
            ScopeKind::InlineClosure => write!(f, "inline closure"),
            ScopeKind::BranchBody => write!(f, "branch body"),
            ScopeKind::LoopBody => write!(f, "loop body"),
            ScopeKind::FromBody => write!(f, "from body"),
            ScopeKind::Params => write!(f, "params"),
        }
    }
}

impl ScopeKind {
    pub fn matches(&self, other: &ScopeKind) -> bool {
        match (self, other) {
            (ScopeKind::TopLevel, ScopeKind::TopLevel)
            | (ScopeKind::FnBody, ScopeKind::FnBody)
            | (ScopeKind::InlineClosure, ScopeKind::InlineClosure)
            | (ScopeKind::BranchBody, ScopeKind::BranchBody)
            | (ScopeKind::LoopBody, ScopeKind::LoopBody)
            | (ScopeKind::FromBody, ScopeKind::FromBody) => true,
            (ScopeKind::Params, ScopeKind::Params) => true,
            _ => false,
        }
    }
}

/// Represents a scope (generally a closure) in which variables and types can be defined
/// or resolved.
pub struct Scope {
    pub kind: ScopeKind,
    /// Contains symbols defined in this scope.
    idents: HashMap<String, Ident>,
    /// Represents the expected return type for the current scope. This should only ever be `Some`
    /// for scopes with kind `FnBody`.
    maybe_ret_type_key: Option<TypeKey>,
    /// Represents the expected yield type for the current scope. This should only ever be `Some`
    /// for scopes with kind `FromBody`.
    maybe_yield_type_key: Option<TypeKey>,
    /// Tracks the number of anonymous functions that were defined directly inside this scope.
    /// This is used to give each anonymous function a unique mangled name within this scope.
    anon_fn_count: usize,
}

impl Scope {
    /// Creates a new scope with return type set to `maybe_ret_type_key`.
    pub fn new(kind: ScopeKind, maybe_ret_type_key: Option<TypeKey>) -> Scope {
        Scope {
            kind,
            idents: Default::default(),
            maybe_ret_type_key,
            maybe_yield_type_key: None,
            anon_fn_count: 0,
        }
    }

    // Adds the identifier to the scope. If there was already a matching identifier in the scope,
    // does nothing and returns an error with the existing symbol.
    pub fn insert_ident(&mut self, ident: Ident) -> Result<(), &Ident> {
        match self.idents.entry(ident.name.clone()) {
            Entry::Occupied(existing) => Err(existing.into_mut()),
            Entry::Vacant(entry) => {
                entry.insert(ident);
                Ok(())
            }
        }
    }

    /// Removes the identifier from this scope and returns it only if it's unchecked.
    pub fn remove_unchecked_ident(&mut self, name: &str) -> Option<Ident> {
        if self
            .idents
            .get(name)
            .is_some_and(|ident| ident.kind.is_unchecked())
        {
            self.idents.remove(name)
        } else {
            None
        }
    }

    /// Returns the symbol in the scope with the given name and kind, or None.
    pub fn get_ident(&self, name: &str) -> Option<&Ident> {
        self.idents.get(name)
    }

    /// Returns a mutable reference to the identifier with the given name.
    pub fn get_ident_mut(&mut self, name: &str) -> Option<&mut Ident> {
        self.idents.get_mut(name)
    }

    /// Sets the scope's yield type key to `maybe_yield_type_key` and returns the
    /// existing one.
    pub fn set_yield_type_key(&mut self, maybe_yield_type_key: Option<TypeKey>) -> Option<TypeKey> {
        let old = self.maybe_yield_type_key;
        self.maybe_yield_type_key = maybe_yield_type_key;
        old
    }

    /// Returns the expected return type for this scope, if one exists. Only function body scopes
    /// should have expected return types.
    pub fn ret_type_key(&self) -> Option<TypeKey> {
        self.maybe_ret_type_key
    }

    /// Returns the expected yield type for this scope, if one exists. Only `from` scopes
    /// should have expected return types.
    pub fn yield_type_key(&self) -> Option<TypeKey> {
        self.maybe_yield_type_key
    }

    /// Returns the current number of anonymous functions inside this scope and increments
    /// the counter.
    pub fn get_and_inc_fn_count(&mut self) -> usize {
        let count = self.anon_fn_count;
        self.anon_fn_count += 1;
        count
    }

    pub fn drain_consts(&mut self) -> HashMap<String, AExpr> {
        self.idents
            .drain()
            .filter_map(|(name, ident)| match ident.kind {
                IdentKind::Const { value, .. } => Some((name, value)),
                _ => None,
            })
            .collect()
    }

    /// Returns all idents declared in this scope that were never used.
    pub fn unused_idents(&self) -> Vec<&Ident> {
        self.idents.values().filter(|i| i.is_unused()).collect()
    }

    /// Returns all idents in the scope that are not `pub` and are unused.
    pub fn unused_top_level_idents(&self) -> Vec<&Ident> {
        self.idents
            .values()
            .filter(|i| i.is_unused_top_level())
            .collect()
    }
}
