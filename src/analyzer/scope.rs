use std::collections::HashMap;
use std::fmt;

use crate::analyzer::ast::arg::AArg;
use crate::analyzer::type_store::TypeKey;
use crate::parser::r#type::Type;

/// Represents a symbol defined in a specific scope.
#[derive(Clone)]
pub struct ScopedSymbol {
    pub name: String,
    pub type_key: TypeKey,
    pub is_mut: bool,
    pub is_arg: bool,
    pub is_const: bool,
}

impl ScopedSymbol {
    pub fn new(name: &str, type_key: TypeKey, is_mut: bool, is_arg: bool) -> Self {
        ScopedSymbol {
            name: name.to_string(),
            type_key: type_key,
            is_mut,
            is_arg,
            is_const: false,
        }
    }

    pub fn new_const(name: &str, type_key: TypeKey) -> Self {
        ScopedSymbol {
            name: name.to_string(),
            type_key: type_key,
            is_mut: false,
            is_arg: false,
            is_const: true,
        }
    }
}

/// Represents a kind of scope in which symbols can be defined.
#[derive(PartialEq, Copy, Clone, Debug)]
pub enum ScopeKind {
    FnBody,
    InlineClosure,
    BranchBody,
    LoopBody,
}

impl fmt::Display for ScopeKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ScopeKind::FnBody => write!(f, "function body"),
            ScopeKind::InlineClosure => write!(f, "inline closure"),
            ScopeKind::BranchBody => write!(f, "branch body"),
            ScopeKind::LoopBody => write!(f, "loop body"),
        }
    }
}

pub struct Scope {
    pub kind: ScopeKind,
    symbols: HashMap<String, ScopedSymbol>,
    /// Maps unchecked types from the parser to type keys that can be used to look up the
    /// corresponding analyzed types. This is just here so we can avoid re-analyzing the same
    /// type from the parser if we've already analyzed it.
    type_keys: HashMap<Type, TypeKey>,
    /// Represents the expected return type for the current scope. This should only ever be `Some`
    /// for scopes with kind `FnBody`.
    maybe_ret_type_key: Option<TypeKey>,
}

impl Scope {
    /// Creates a new scope with `args` defined as symbols in the scope and return type set to
    /// `maybe_ret_type_key`.
    pub fn new(kind: ScopeKind, args: Vec<AArg>, maybe_ret_type_key: Option<TypeKey>) -> Scope {
        let mut symbols = HashMap::new();
        symbols.reserve(args.len());
        for arg in args {
            symbols.insert(
                arg.name.clone(),
                ScopedSymbol::new(arg.name.as_str(), arg.type_key, arg.is_mut, true),
            );
        }

        Scope {
            kind,
            symbols,
            type_keys: Default::default(),
            maybe_ret_type_key,
        }
    }

    /// Gets the type key for the given type, if it exists in the scope.
    pub fn get_type_key(&self, typ: &Type) -> Option<TypeKey> {
        match self.type_keys.get(&typ) {
            Some(k) => Some(*k),
            None => None,
        }
    }

    /// Inserts a mapping from `typ` to `key` into the scope so `typ` can be resolved faster inside
    /// this scope in the future using `Scope::get_type_key(typ)`.
    pub fn insert_type_key(&mut self, typ: Type, key: TypeKey) {
        self.type_keys.insert(typ, key);
    }

    // Adds the symbol to the scope. If there was already a symbol with the same name in
    // the scope, returns the old symbol.
    pub fn add_symbol(&mut self, symbol: ScopedSymbol) -> Option<ScopedSymbol> {
        self.symbols.insert(symbol.name.clone(), symbol)
    }

    // Returns the symbol with the given name from the scope, or None if no such symbol
    // exists.
    pub fn get_symbol(&self, name: &str) -> Option<&ScopedSymbol> {
        self.symbols.get(name)
    }

    /// Returns the expected return type for this scope, if one exists. Only function body scopes
    /// should have expected return types.
    pub fn ret_type_key(&self) -> Option<TypeKey> {
        self.maybe_ret_type_key
    }
}
