use crate::analyzer::ast::array::AArrayType;
use crate::analyzer::ast::expr::AExpr;
use crate::analyzer::ast::ext::AExternFn;
use crate::analyzer::ast::func::{AFn, AFnSig};
use crate::analyzer::ast::generic::AGenericType;
use crate::analyzer::ast::params::{AParam, AParams};
use crate::analyzer::ast::pointer::APointerType;
use crate::analyzer::ast::r#const::AConst;
use crate::analyzer::ast::r#enum::AEnumType;
use crate::analyzer::ast::r#impl::AImpl;
use crate::analyzer::ast::r#static::AStatic;
use crate::analyzer::ast::r#struct::AStructType;
use crate::analyzer::ast::r#type::AType;
use crate::analyzer::ast::spec::ASpecType;
use crate::analyzer::ast::tuple::ATupleType;
use crate::analyzer::error::{
    err_expected_params, err_expected_type, err_not_pub, err_undef_mod_alias, err_undef_type,
    err_unexpected_params, AnalyzeError, AnalyzeResult, ErrorKind,
};
use crate::analyzer::ident::{Ident, IdentKind, ModAlias, Usage};
use crate::analyzer::mod_context::ModuleContext;
use crate::analyzer::scope::{Scope, ScopeKind};
use crate::analyzer::type_store::{GetType, TypeKey, TypeStore};
use crate::analyzer::warn::{warn_unused, AnalyzeWarning};
use crate::codegen::program::CodeGenConfig;
use crate::fmt::format_code_vec;
use crate::lexer::pos::{Locatable, Position, Span};
use crate::parser::ast::r#type::Type;
use crate::parser::ast::symbol::{Name, Symbol};
use crate::parser::ast::unresolved::UnresolvedType;
use crate::parser::{FileID, ModID};
use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub struct ReplacedParam {
    pub param_type_key: TypeKey,
    pub replacement_type_key: TypeKey,
}

/// Represents a polymorphic type that was monomorphized, and the set of
/// parameters that were used to monomorphize it.
#[derive(Debug, Clone, Eq)]
pub struct Monomorphization {
    pub poly_type_key: TypeKey,
    pub mono_type_key: TypeKey,
    pub replaced_params: Vec<ReplacedParam>,
}

impl PartialEq for Monomorphization {
    fn eq(&self, other: &Self) -> bool {
        self.poly_type_key == other.poly_type_key && self.replaced_params == other.replaced_params
    }
}

impl Hash for Monomorphization {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.poly_type_key.hash(state);
        self.replaced_params.hash(state);
    }
}

impl Monomorphization {
    pub fn type_mappings(&self) -> HashMap<TypeKey, TypeKey> {
        self.replaced_params
            .iter()
            .map(|rp| (rp.param_type_key, rp.replacement_type_key))
            .collect()
    }
}

/// Contains information about `impl` blocks for a type.
#[derive(Default)]
pub struct TypeImpls {
    /// Maps function name to function type key for all functions declared in default impl blocks
    /// (impl blocks without specs) for the type.
    default_fns: HashMap<String, TypeKey>,
    /// Tracks usage of default member functions. Member functions that are used will appear here.
    used_default_fns: HashSet<TypeKey>,
    /// Maps implemented spec type key to spec impl info.
    spec_impls: HashMap<TypeKey, SpecImpl>,
    /// Contains the type keys of all public member functions for this type.
    pub_fn_tks: HashSet<TypeKey>,
}

/// Contains information about a spec implementation on some type.
#[derive(Clone, Default)]
pub struct SpecImpl {
    /// Maps member function names to their type keys.
    pub member_fns: HashMap<String, TypeKey>,
    /// The span of the impl header.
    pub header_span: Span,
}

impl TypeImpls {
    /// Inserts information about a spec `impl` block for some type.
    fn insert_spec_impl(
        &mut self,
        spec_tk: TypeKey,
        member_fns: HashMap<String, TypeKey>,
        header_span: Span,
    ) {
        let no_conflict = self
            .spec_impls
            .insert(
                spec_tk,
                SpecImpl {
                    member_fns,
                    header_span,
                },
            )
            .is_none();
        assert!(no_conflict);
    }

    /// Inserts information about a default `impl` block for some type.
    fn insert_default_impl(&mut self, member_fns: HashMap<String, TypeKey>) {
        self.default_fns.extend(member_fns);
    }

    /// Inserts the given function info.
    fn insert_fn(&mut self, maybe_spec_tk: Option<TypeKey>, fn_name: String, fn_type_key: TypeKey) {
        match maybe_spec_tk {
            Some(spec_tk) => {
                self.spec_impls
                    .entry(spec_tk)
                    .or_insert(SpecImpl::default())
                    .member_fns
                    .insert(fn_name, fn_type_key);
            }
            None => {
                self.default_fns.insert(fn_name, fn_type_key);
            }
        }
    }

    /// Returns the type key for the spec that the given function implements.
    fn get_spec_type_key(&self, fn_type_key: TypeKey) -> Option<TypeKey> {
        for (spec_tk, spec_impl) in &self.spec_impls {
            for fn_tk in spec_impl.member_fns.values() {
                if *fn_tk == fn_type_key {
                    return Some(*spec_tk);
                }
            }
        }

        None
    }

    /// Marks the given function as public.
    fn mark_fn_pub(&mut self, fn_type_key: TypeKey) {
        self.pub_fn_tks.insert(fn_type_key);
    }

    /// Tries to find a "default" function (i.e. a function declared in a regular `impl` block
    /// without a spec) with the given name.
    fn get_default_fn(&mut self, name: &str) -> Option<TypeKey> {
        match self.default_fns.get(name) {
            Some(&tk) => Some(tk),
            None => None,
        }
    }

    /// Returns the type keys of all unused private default functions.
    fn unused_default_fns(&self) -> Vec<TypeKey> {
        let mut fn_tks = vec![];
        for fn_tk in self.default_fns.values() {
            if !self.pub_fn_tks.contains(fn_tk) && !self.used_default_fns.contains(fn_tk) {
                fn_tks.push(*fn_tk);
            }
        }

        fn_tks
    }

    /// Tries to find the function with the given name that is part of the implementation of the
    /// given spec.
    pub fn get_fn_from_spec_impl(&self, spec_tk: TypeKey, name: &str) -> Option<TypeKey> {
        match self.spec_impls.get(&spec_tk) {
            Some(impls) => impls.member_fns.get(name).cloned(),
            None => None,
        }
    }

    /// Tries to find the member function with the given name. Returns
    ///  - `Ok(None)` if no matching member functions exist
    ///  - `Ok(Some(tk))` if exactly one matching member function exists
    ///  - `Err(())` if multiple matching member functions are found.
    fn get_fns_by_name(&mut self, name: &str) -> Result<Option<TypeKey>, ()> {
        let mut fn_tks = vec![];

        // Find a default function with the same name.
        if let Some(tk) = self.default_fns.get(name) {
            self.used_default_fns.insert(*tk);
            fn_tks.push(*tk);
        }

        // Find any spec functions with the same name.
        for spec_impl in self.spec_impls.values() {
            if let Some(tk) = spec_impl.member_fns.get(name) {
                fn_tks.push(*tk);
            }
        }

        match fn_tks.len() {
            0 => Ok(None),
            1 => Ok(Some(fn_tks[0])),
            _ => Err(()),
        }
    }
}

/// Stores information about the program for reference during semantic analysis.
pub struct ProgramContext {
    pub config: CodeGenConfig,
    /// Stores all types that are successfully analyzed during semantic analysis.
    pub type_store: TypeStore,
    /// Maps polymorphic type keys to their monomorphizations.
    pub monomorphized_types: HashMap<TypeKey, HashSet<Monomorphization>>,
    /// Maps monomorphic type keys to the monomorphizations that were used to derive them.
    pub type_monomorphizations: HashMap<TypeKey, Monomorphization>,
    /// Maps primitive type names to their type keys.
    primitive_type_keys: HashMap<String, TypeKey>,
    /// Contains the type keys of all types declared public.
    pub_type_keys: HashSet<TypeKey>, // TODO: remove

    /// The ID of the module that is currently being analyzed.
    cur_mod_id: ModID,

    /// Maps module path to its context.
    module_contexts: HashMap<ModID, ModuleContext>,

    /// Maps tuple type to tuple type key.
    tuple_type_keys: HashMap<ATupleType, TypeKey>,
    /// Maps array type to array type key.
    array_type_keys: HashMap<AArrayType, TypeKey>,
    /// Maps pointer type to pointer type key.
    pointer_type_keys: HashMap<APointerType, TypeKey>,
    /// Maps generic type to generic type key.
    generic_type_keys: HashMap<AGenericType, TypeKey>,
    /// Maps function types to their type keys.
    fn_type_keys: HashMap<AFnSig, TypeKey>,
    /// Maps type key to its impl blocks.
    pub type_impls: HashMap<TypeKey, TypeImpls>,
    /// Maps struct type key to the set of public field names on that struct type.
    pub_struct_field_names: HashMap<TypeKey, HashSet<String>>,
    /// Maps type keys to the IDs of the modules in which the types are declared.
    type_declaration_mod_ids: HashMap<TypeKey, ModID>,

    /// Collects warnings emitted by the analyzer during analysis.
    pub warnings: HashMap<Position, AnalyzeWarning>,
    /// Collects errors emitted by the analyzer during analysis.
    pub errors: HashMap<Position, AnalyzeError>,
}

impl ProgramContext {
    /// Creates a new program context. The program context will be initialized with stack containing
    /// a single scope representing the global scope and a type store containing primitive types.
    pub fn new(builtins_mod_id: ModID, root_mod_id: ModID, config: CodeGenConfig) -> Self {
        let mut type_store = TypeStore::new();
        let mut primitive_type_keys = HashMap::new();
        let mut type_declaration_mod_ids = HashMap::new();

        // Set up primitive type keys.
        for typ in AType::primitives() {
            let name = typ.name().to_string();
            let type_key = type_store.insert_type(typ);
            primitive_type_keys.insert(name.clone(), type_key);
            type_declaration_mod_ids.insert(type_key, builtins_mod_id);
        }

        ProgramContext {
            config,
            type_store,
            primitive_type_keys,
            pub_type_keys: Default::default(),
            cur_mod_id: root_mod_id,
            module_contexts: Default::default(),
            tuple_type_keys: Default::default(),
            array_type_keys: Default::default(),
            pointer_type_keys: Default::default(),
            generic_type_keys: Default::default(),
            fn_type_keys: Default::default(),
            type_impls: Default::default(),
            pub_struct_field_names: Default::default(),
            type_declaration_mod_ids,
            monomorphized_types: Default::default(),
            type_monomorphizations: Default::default(),
            warnings: Default::default(),
            errors: Default::default(),
        }
    }

    /// Returns the module context corresponding to the module that is currently
    /// being analysed.
    fn cur_mod_ctx(&self) -> &ModuleContext {
        self.module_contexts.get(&self.cur_mod_id).unwrap()
    }

    /// Returns the mutable module context corresponding to the module that is
    /// currently being analysed.
    fn cur_mod_ctx_mut(&mut self) -> &mut ModuleContext {
        self.module_contexts.get_mut(&self.cur_mod_id).unwrap()
    }

    /// Checks that the given type implements the set of specs on the given
    /// generic type. Returns type keys for specs not implemented by the type.
    pub fn get_missing_spec_impls(
        &mut self,
        type_key: TypeKey,
        generic_type_key: TypeKey,
    ) -> Vec<TypeKey> {
        let mut missing_spec_type_keys = vec![];
        let spec_type_keys = &self
            .get_type(generic_type_key)
            .to_generic_type()
            .spec_type_keys;

        for spec_type_key in spec_type_keys.clone() {
            if self.get_spec_impl(type_key, spec_type_key).is_none()
                && !self.type_has_unchecked_spec_impl(type_key, spec_type_key)
            {
                missing_spec_type_keys.push(spec_type_key);
            }
        }

        missing_spec_type_keys
    }

    /// Returns information about the spec impl for the given type, if such a spec impl exists.
    pub fn get_spec_impl(&mut self, impl_tk: TypeKey, spec_type_key: TypeKey) -> Option<&SpecImpl> {
        match self.type_impls.get(&impl_tk) {
            Some(impls) => impls.spec_impls.get(&spec_type_key),
            None => None,
        }
    }

    /// Returns true if type given type has an impl for the given spec that has not yet been
    /// analyzed.
    fn type_has_unchecked_spec_impl(&mut self, type_key: TypeKey, spec_type_key: TypeKey) -> bool {
        // We haven't yet analyzed an impl block on the type for the given spec, so let's see
        // if it appears in the unchecked impls.
        if self.type_declared_in_cur_mod(type_key) || self.type_declared_in_cur_mod(spec_type_key) {
            // TODO: this is expensive, we should only have to do it once. I'm not going to bother
            // fixing it for now, though, because it should be rare that this is needed anyway.
            for (impl_type, maybe_spec_type) in self.cur_mod_ctx().unchecked_impls().clone() {
                if let Some(spec_sym) = maybe_spec_type {
                    let impl_tk = self.resolve_maybe_polymorphic_type(&Type::Unresolved(impl_type));
                    if impl_tk != type_key {
                        continue;
                    }

                    let impl_spec_tk = self.resolve_type(&spec_sym.as_unresolved_type());
                    if impl_spec_tk == spec_type_key {
                        return true;
                    }
                }
            }
        }

        false
    }

    /// Drains all module constants and statics from the program context.
    pub fn drain_mod_consts_and_statics(
        &mut self,
    ) -> (
        HashMap<ModID, HashMap<String, AExpr>>,
        HashMap<ModID, HashMap<String, AExpr>>,
    ) {
        let mut consts = HashMap::new();
        let mut statics = HashMap::new();

        for (mod_id, mod_ctx) in &mut self.module_contexts {
            let (mod_consts, mod_statics) = mod_ctx.drain_consts_and_statics();

            consts.insert(*mod_id, mod_consts);
            statics.insert(*mod_id, mod_statics);
        }

        (consts, statics)
    }

    /// Inserts an error into the program context.
    pub fn insert_err(&mut self, err: AnalyzeError) {
        self.errors.insert(err.span.start_pos, err);
    }

    /// Inserts a warning into the program context.
    pub fn insert_warn(&mut self, warn: AnalyzeWarning) {
        self.warnings.insert(warn.span.start_pos, warn);
    }

    /// Tries to locate the type key associated with the given type and returns it
    /// if found.
    fn get_existing_type_key(&self, typ: &AType) -> Option<TypeKey> {
        match &typ {
            AType::Bool => return Some(self.bool_type_key()),
            AType::U8 => return Some(self.u8_type_key()),
            AType::I8 => return Some(self.i8_type_key()),
            AType::U32 => return Some(self.u32_type_key()),
            AType::I32 => return Some(self.i32_type_key()),
            AType::F32 => return Some(self.f32_type_key()),
            AType::I64 => return Some(self.i64_type_key()),
            AType::U64 => return Some(self.u64_type_key()),
            AType::F64 => return Some(self.f64_type_key()),
            AType::Int => return Some(self.int_type_key()),
            AType::Uint => return Some(self.uint_type_key()),
            AType::Str => return Some(self.str_type_key()),

            AType::Tuple(tuple_type) => {
                if let Some(existing_tuple_tk) = self.tuple_type_keys.get(tuple_type) {
                    return Some(*existing_tuple_tk);
                }
            }

            AType::Array(array_type) => {
                if let Some(existing_array_tk) = self.array_type_keys.get(array_type) {
                    return Some(*existing_array_tk);
                }
            }

            AType::Function(fn_type) => {
                if let Some(existing_fn_tk) = self.fn_type_keys.get(fn_type.as_ref()) {
                    return Some(*existing_fn_tk);
                }
            }

            AType::Pointer(ptr_type) => {
                if let Some(existing_ptr_tk) = self.pointer_type_keys.get(ptr_type) {
                    return Some(*existing_ptr_tk);
                }
            }

            AType::Generic(generic_type) => {
                if let Some(tk) = self.generic_type_keys.get(generic_type) {
                    return Some(*tk);
                }
            }

            _ => {}
        }

        None
    }

    /// Inserts the given analyzed type into the program context. The type will be inserted
    /// regardless of whether there is already a matching type in the type store.
    pub fn force_insert_type(&mut self, typ: AType) -> TypeKey {
        // Store the newly analyzed type.
        let type_key = self.type_store.insert_type(typ);

        // Create an additional mapping to the new type key to avoid type duplication, if necessary.
        let typ = self.get_type(type_key);
        match typ {
            AType::Function(fn_sig) => {
                self.fn_type_keys.insert(*fn_sig.clone(), type_key);
            }

            AType::Tuple(tuple_type) => {
                self.tuple_type_keys.insert(tuple_type.clone(), type_key);
            }

            AType::Array(array_type) => {
                self.array_type_keys.insert(array_type.clone(), type_key);
            }

            AType::Pointer(ptr_type) => {
                self.pointer_type_keys.insert(ptr_type.clone(), type_key);
            }

            AType::Struct(_) | AType::Enum(_) | AType::Spec(_) | AType::Generic(_) => {
                self.type_declaration_mod_ids
                    .insert(type_key, self.cur_mod_id);
            }

            _ => {}
        }

        type_key
    }

    /// Inserts the given analyzed type into the program context. This function will also handle
    /// tracking named types. If another matching type already exists in the current module,
    /// `typ` will not be inserted and the type key for the existing type will be returned.
    pub fn insert_type(&mut self, typ: AType) -> TypeKey {
        // Check if we've already inserted this type. This just prevents us
        // from storing duplicate types in the type store.
        if let Some(existing_tk) = self.get_existing_type_key(&typ) {
            self.replace_type(existing_tk, typ);
            return existing_tk;
        }

        self.force_insert_type(typ)
    }

    /// Tries to map the given un-analyzed type to a type key and return that type key. If there is
    /// no existing mapping for `typ`, performs semantic analysis on `typ`, inserts it into the
    /// type store and returns the resulting type key. An error will be recorded if
    /// the type is parameterized and invalid parameters were provided.
    pub fn resolve_type(&mut self, typ: &Type) -> TypeKey {
        self.resolve_type_helper(typ, false)
    }

    /// Does the same thing as `resolve_type`, except it doesn't require parameters
    /// for polymorphic types.  
    pub fn resolve_maybe_polymorphic_type(&mut self, typ: &Type) -> TypeKey {
        self.resolve_type_helper(typ, true)
    }

    /// Implements the functionality described in `resolve_type`, except that
    /// if `allow_polymorph` is `false` and the resolved type is polymorphic,
    /// an error will be recorded.
    fn resolve_type_helper(&mut self, typ: &Type, allow_polymorph: bool) -> TypeKey {
        let a_type = match typ {
            Type::Unresolved(unresolved_type) => {
                return self.resolve_named_type(unresolved_type, allow_polymorph)
            }

            Type::Function(sig) => AType::from_fn_sig(AFnSig::from(self, &*sig)),

            Type::Tuple(tuple_type) => {
                let a_tuple_type = ATupleType::from(self, tuple_type);
                AType::Tuple(a_tuple_type)
            }

            Type::Array(array_type) => {
                let a_array_type = AArrayType::from(self, array_type);
                AType::Array(a_array_type)
            }

            Type::Pointer(ptr_type) => {
                let a_ptr_type = APointerType::from(self, ptr_type);
                if a_ptr_type.pointee_type_key == self.unknown_type_key() {
                    return self.unknown_type_key();
                }

                AType::Pointer(a_ptr_type)
            }
        };

        if a_type.is_unknown() {
            return self.unknown_type_key();
        }

        let is_polymorphic = a_type.params().is_some();
        let tk = self.insert_type(a_type);

        // It's possible that we just resolved a polymorphic type that was not defined before now.
        // If so, we should try to monomorphize it.
        if is_polymorphic {
            match typ {
                Type::Unresolved(unresolved_type) if !unresolved_type.params.is_empty() => {
                    return self.monomorphize_parameterized_type(tk, &unresolved_type.params, typ);
                }

                _ if !allow_polymorph => {
                    let err = err_expected_params(self, tk, *typ.span());
                    self.insert_err(err);
                    return self.unknown_type_key();
                }

                _ => {}
            }
        }

        tk
    }

    fn resolve_named_type(
        &mut self,
        unresolved_type: &UnresolvedType,
        allow_polymorph: bool,
    ) -> TypeKey {
        let maybe_ident = match &unresolved_type.maybe_mod_name {
            Some(mod_name) => {
                let mod_id = match self.get_mod_alias(mod_name) {
                    Some(alias) => alias.target_mod_id,
                    None => {
                        self.insert_err(err_undef_mod_alias(&mod_name.value, mod_name.span));
                        return self.unknown_type_key();
                    }
                };

                self.get_foreign_ident(mod_id, &unresolved_type.name.value)
            }

            None => {
                // Yucky hack to resolve the special "Self" type, if it's defined.
                if unresolved_type.name.value == "Self" {
                    if let Some(self_tk) = self.get_cur_self_type_key() {
                        return self_tk;
                    }
                }

                self.get_local_ident(&unresolved_type.name.value, Some(Usage::Read))
            }
        };

        let tk = match maybe_ident.cloned() {
            Some(Ident {
                kind:
                    IdentKind::Type {
                        type_key,
                        is_pub,
                        mod_id,
                    },
                ..
            }) => {
                if mod_id.is_some_and(|id| id != self.cur_mod_id) && !is_pub {
                    self.insert_err(err_not_pub(
                        &unresolved_type.name.value,
                        unresolved_type.span,
                    ));
                }

                type_key
            }

            Some(Ident { name, span, .. }) => {
                self.insert_err(err_expected_type(&name, span));
                self.unknown_type_key()
            }

            None => {
                self.insert_err(err_undef_type(unresolved_type));
                self.unknown_type_key()
            }
        };

        if unresolved_type.params.is_empty() {
            // No parameters were provided, so this type should either be monomorphic, or
            // `allow_polymorph` should be `true`.
            let resolved_type = self.get_type(tk);
            if resolved_type.params().is_some() && !allow_polymorph {
                let err = err_expected_params(self, tk, unresolved_type.span);
                self.insert_err(err);
                return self.unknown_type_key();
            }

            tk
        } else {
            // Parameters were provided for the type, so we need to monomorphize it before
            // returning it.
            let mono_tk = self.monomorphize_parameterized_type(
                tk,
                unresolved_type.params.as_ref(),
                unresolved_type,
            );

            mono_tk
        }
    }

    pub fn monomorphize_type(
        &mut self,
        type_key: TypeKey,
        type_mappings: &HashMap<TypeKey, TypeKey>,
        maybe_target_tk: Option<TypeKey>,
    ) -> Option<TypeKey> {
        let typ = self.get_type(type_key);
        match typ {
            AType::Struct(_) => {
                self.monomorphize_struct_type(type_key, type_mappings, maybe_target_tk)
            }
            AType::Enum(_) => self.monomorphize_enum_type(type_key, type_mappings, maybe_target_tk),
            AType::Tuple(_) => {
                self.monomorphize_tuple_type(type_key, type_mappings, maybe_target_tk)
            }
            AType::Array(_) => {
                self.monomorphize_array_type(type_key, type_mappings, maybe_target_tk)
            }
            AType::Function(_) => {
                self.monomorphize_fn_type(type_key, type_mappings, maybe_target_tk)
            }
            AType::Pointer(_) => {
                self.monomorphize_ptr_type(type_key, type_mappings, maybe_target_tk)
            }
            AType::Spec(_) => self.monomorphize_spec_type(type_key, type_mappings, maybe_target_tk),

            // These types can't be monomorphized.
            AType::Bool
            | AType::U8
            | AType::I8
            | AType::U16
            | AType::I16
            | AType::U32
            | AType::I32
            | AType::F32
            | AType::I64
            | AType::U64
            | AType::F64
            | AType::Int
            | AType::Uint
            | AType::Str
            | AType::Char
            | AType::Generic(_)
            | AType::Unknown(_) => None,
        }
    }

    fn monomorphize_struct_type(
        &mut self,
        type_key: TypeKey,
        type_mappings: &HashMap<TypeKey, TypeKey>,
        maybe_target_tk: Option<TypeKey>,
    ) -> Option<TypeKey> {
        let mut struct_type = self.get_type(type_key).to_struct_type().clone();

        // We can't monomorphize struct types that aren't parameterized.
        if struct_type.maybe_params.is_none() {
            return None;
        }

        let mut replaced_tks = false;
        for field in &mut struct_type.fields {
            if self.replace_tks(&mut field.type_key, type_mappings) {
                replaced_tks = true;
            }
        }

        let has_replaced_param = match self.get_type(type_key).params() {
            Some(params) => params
                .params
                .iter()
                .find(|p| type_mappings.contains_key(&p.generic_type_key))
                .is_some(),
            None => false,
        };

        if replaced_tks || has_replaced_param {
            // Remove parameters from the signature now that they're no longer relevant.
            struct_type.maybe_params = None;

            // Define the new type in the program context.
            return match maybe_target_tk {
                Some(target_tk) => {
                    self.replace_type(target_tk, AType::Struct(struct_type));
                    Some(target_tk)
                }
                None => Some(self.insert_type(AType::Struct(struct_type))),
            };
        }

        None
    }

    fn monomorphize_enum_type(
        &mut self,
        type_key: TypeKey,
        type_mappings: &HashMap<TypeKey, TypeKey>,
        maybe_target_tk: Option<TypeKey>,
    ) -> Option<TypeKey> {
        let mut replaced_tks = false;
        let mut enum_type = self.get_type(type_key).to_enum_type().clone();
        for variant in &mut enum_type.variants.values_mut() {
            if let Some(variant_tk) = &mut variant.maybe_type_key {
                if self.replace_tks(variant_tk, type_mappings) {
                    replaced_tks = true;
                }
            }
        }

        if replaced_tks {
            // Remove parameters from the signature now that they're no longer relevant.
            enum_type.maybe_params = None;

            // Define the new type in the program context.
            return match maybe_target_tk {
                Some(target_tk) => {
                    self.replace_type(target_tk, AType::Enum(enum_type));
                    Some(target_tk)
                }
                None => Some(self.insert_type(AType::Enum(enum_type))),
            };
        }

        None
    }

    fn monomorphize_spec_fn(
        &mut self,
        type_key: TypeKey,
        type_mappings: &HashMap<TypeKey, TypeKey>,
    ) -> Option<TypeKey> {
        let mut replaced_tks = false;
        let mut fn_sig = self.get_type(type_key).to_fn_sig().clone();

        #[allow(unused)] // False positive
        let mut new_type_mappings = HashMap::new();

        let type_mappings = if let Some(params) = fn_sig.params {
            new_type_mappings = type_mappings.clone();
            fn_sig.params = None;
            fn_sig.type_key = self.force_insert_type(AType::Function(Box::new(fn_sig.clone())));

            let mut new_params = AParams {
                params: vec![],
                span: params.span,
            };

            for param in params.params {
                let mut generic_type = self
                    .get_type(param.generic_type_key)
                    .to_generic_type()
                    .clone();

                generic_type.poly_type_key = fn_sig.type_key;
                generic_type.spec_type_keys = generic_type
                    .spec_type_keys
                    .iter()
                    .map(|spec_tk| {
                        self.monomorphize_spec_type(*spec_tk, type_mappings, None)
                            .unwrap_or(*spec_tk)
                    })
                    .collect();

                let new_generic_tk = self.insert_type(AType::Generic(generic_type));

                new_type_mappings.insert(param.generic_type_key, new_generic_tk);
                new_params.params.push(AParam {
                    name: param.name,
                    poly_type_key: fn_sig.type_key,
                    generic_type_key: new_generic_tk,
                    span: param.span,
                });
            }

            fn_sig.params = Some(new_params);

            &new_type_mappings
        } else {
            type_mappings
        };

        for arg in &mut fn_sig.args {
            if self.replace_tks(&mut arg.type_key, type_mappings) {
                replaced_tks = true;
            }
        }

        if let Some(ret_type_key) = &mut fn_sig.maybe_ret_type_key {
            if self.replace_tks(ret_type_key, type_mappings) {
                replaced_tks = true;
            }
        }

        if let Some(impl_type_key) = &mut fn_sig.maybe_impl_type_key {
            if self.replace_tks(impl_type_key, type_mappings) {
                replaced_tks = true;
            }
        }

        if fn_sig.params.is_some() {
            let new_tk = fn_sig.type_key;
            self.replace_type(fn_sig.type_key, AType::Function(Box::new(fn_sig)));
            Some(new_tk)
        } else if replaced_tks {
            let new_tk = self.insert_type(AType::Function(Box::new(fn_sig.clone())));
            fn_sig.type_key = new_tk;
            self.replace_type(fn_sig.type_key, AType::Function(Box::new(fn_sig)));
            Some(new_tk)
        } else {
            None
        }
    }

    fn monomorphize_fn_type(
        &mut self,
        type_key: TypeKey,
        type_mappings: &HashMap<TypeKey, TypeKey>,
        maybe_target_tk: Option<TypeKey>,
    ) -> Option<TypeKey> {
        let mut replaced_tks = false;
        let mut fn_sig = self.get_type(type_key).to_fn_sig().clone();

        for arg in &mut fn_sig.args {
            if self.replace_tks(&mut arg.type_key, type_mappings) {
                replaced_tks = true;
            }
        }

        if let Some(ret_type_key) = &mut fn_sig.maybe_ret_type_key {
            if self.replace_tks(ret_type_key, type_mappings) {
                replaced_tks = true;
            }
        }

        if let Some(impl_type_key) = &mut fn_sig.maybe_impl_type_key {
            if self.replace_tks(impl_type_key, type_mappings) {
                replaced_tks = true;
            }
        }

        if let Some(params) = &fn_sig.params {
            for param in &params.params {
                if type_mappings.contains_key(&param.generic_type_key) {
                    replaced_tks = true;
                    break;
                }
            }
        }

        if replaced_tks {
            // Remove parameters from the signature now that they're no longer relevant.
            fn_sig.params = None;

            // Define the new type in the program context.
            return match maybe_target_tk {
                Some(target_tk) => {
                    fn_sig.type_key = target_tk;
                    self.replace_type(target_tk, AType::Function(Box::new(fn_sig)));
                    Some(target_tk)
                }
                None => {
                    let new_fn_type_key =
                        self.insert_type(AType::Function(Box::new(fn_sig.clone())));
                    fn_sig.type_key = new_fn_type_key;
                    self.replace_type(new_fn_type_key, AType::Function(Box::new(fn_sig)));
                    Some(new_fn_type_key)
                }
            };
        }

        None
    }

    fn monomorphize_tuple_type(
        &mut self,
        type_key: TypeKey,
        type_mappings: &HashMap<TypeKey, TypeKey>,
        maybe_target_tk: Option<TypeKey>,
    ) -> Option<TypeKey> {
        let mut tuple_type = self.get_type(type_key).to_tuple_type().clone();
        let mut replaced_tks = false;
        for field in &mut tuple_type.fields {
            if self.replace_tks(&mut field.type_key, type_mappings) {
                replaced_tks = true;
            }
        }

        if replaced_tks {
            return match maybe_target_tk {
                Some(target_tk) => {
                    self.replace_type(target_tk, AType::Tuple(tuple_type));
                    Some(target_tk)
                }
                None => Some(self.insert_type(AType::Tuple(tuple_type))),
            };
        }

        None
    }

    fn monomorphize_array_type(
        &mut self,
        type_key: TypeKey,
        type_mappings: &HashMap<TypeKey, TypeKey>,
        maybe_target_tk: Option<TypeKey>,
    ) -> Option<TypeKey> {
        let mut array_type = self.get_type(type_key).to_array_type().clone();
        if let Some(elem_tk) = &mut array_type.maybe_element_type_key {
            if self.replace_tks(elem_tk, type_mappings) {
                return match maybe_target_tk {
                    Some(target_tk) => {
                        self.replace_type(target_tk, AType::Array(array_type));
                        Some(target_tk)
                    }
                    None => Some(self.insert_type(AType::Array(array_type))),
                };
            }
        }

        None
    }

    fn monomorphize_ptr_type(
        &mut self,
        type_key: TypeKey,
        type_mappings: &HashMap<TypeKey, TypeKey>,
        maybe_target_tk: Option<TypeKey>,
    ) -> Option<TypeKey> {
        let mut ptr_type = self.get_type(type_key).to_ptr_type().clone();
        if self.replace_tks(&mut ptr_type.pointee_type_key, type_mappings) {
            return match maybe_target_tk {
                Some(target_tk) => {
                    self.replace_type(target_tk, AType::Pointer(ptr_type));
                    Some(target_tk)
                }
                None => Some(self.insert_type(AType::Pointer(ptr_type))),
            };
        }

        None
    }

    fn monomorphize_spec_type(
        &mut self,
        type_key: TypeKey,
        type_mappings: &HashMap<TypeKey, TypeKey>,
        maybe_target_tk: Option<TypeKey>,
    ) -> Option<TypeKey> {
        let mut spec_type = self.get_type(type_key).to_spec_type().clone();

        for fn_tk in spec_type.member_fn_type_keys.values_mut() {
            if let Some(new_tk) = self.monomorphize_spec_fn(*fn_tk, type_mappings) {
                *fn_tk = new_tk;
            }
        }

        // Remove parameters from the signature now that they're no longer relevant.
        spec_type.maybe_params = None;

        // Define the new type in the program context.
        match maybe_target_tk {
            Some(target_tk) => {
                self.replace_type(target_tk, AType::Spec(spec_type));
                Some(target_tk)
            }
            None => Some(self.insert_type(AType::Spec(spec_type))),
        }
    }

    /// Replaces type keys inside the given type using `type_mappings`. If any type keys were
    /// replaced, updates `tk`.
    pub fn replace_tks(
        &mut self,
        tk: &mut TypeKey,
        type_mappings: &HashMap<TypeKey, TypeKey>,
    ) -> bool {
        // Check if we can just replace the type key itself based on the provided mapping.
        if let Some(replacement_tk) = type_mappings.get(tk) {
            *tk = *replacement_tk;
            return true;
        }

        let typ = self.get_type(*tk);

        let result = if let Some(params) = typ.params() {
            // The type is polymorphic, so we can use its defined parameters to extract
            // monomorphization info.
            let mut param_tks = vec![];
            for param in &params.params {
                param_tks.push(*type_mappings.get(&param.generic_type_key).unwrap());
            }

            Some((*tk, param_tks))
        } else if let Some(mono) = self.type_monomorphizations.get(tk) {
            let mono = mono.clone();

            // The type is a monomorphization of a polymorphic type. We can find the polymorphic
            // type and use it to extract monomorphization info.
            let mut param_tks = vec![];
            for replaced_param in &mono.replaced_params {
                let mut param_tk = replaced_param.replacement_type_key;
                self.replace_tks(&mut param_tk, type_mappings);
                param_tks.push(param_tk);
            }

            Some((mono.poly_type_key, param_tks))
        } else {
            // The type is just a regular type - not a polymorph or a monomorphization of anything.
            None
        };

        // If we were able to find a polymorphic type, we can now do the monomorphization.
        if let Some((poly_tk, param_tks)) = result {
            let dummy_span = Span::default();
            let dummy_spans: Vec<&Span> = param_tks.iter().map(|_| &dummy_span).collect();
            let mono_tk =
                self.try_execute_monomorphization(poly_tk, param_tks, &dummy_spans, &dummy_span);
            if mono_tk != *tk {
                *tk = mono_tk;
                return true;
            }
            return false;
        }

        // Just try to monomorphize the type the basic way.
        match self.monomorphize_type(*tk, type_mappings, None) {
            Some(mono_tk) => {
                if mono_tk != *tk {
                    *tk = mono_tk;
                    true
                } else {
                    false
                }
            }
            None => false,
        }
    }

    /// Converts the given type from a polymorphic (parameterized) type into a
    /// monomorph by substituting type keys for generic types with those from
    /// the provided parameter types. Returns the type key for the monomorphized
    /// type.
    pub fn monomorphize_parameterized_type(
        &mut self,
        poly_type_key: TypeKey,
        param_types: &Vec<Type>,
        loc: &impl Locatable,
    ) -> TypeKey {
        let param_type_keys: Vec<TypeKey> =
            param_types.iter().map(|t| self.resolve_type(t)).collect();
        let param_locs: Vec<&Type> = param_types.iter().map(|t| t).collect();
        self.try_execute_monomorphization(poly_type_key, param_type_keys, &param_locs, loc)
    }

    /// Re-executes a monomorphization.
    pub fn reexecute_monomorphization(&mut self, mono: Monomorphization) {
        // Temporarily remove the cached monomorphization to force a new one.
        let removed = self
            .type_monomorphizations
            .remove(&mono.mono_type_key)
            .unwrap();

        // Execute the same monomorphization again.
        self.monomorphize_type(mono.poly_type_key, &mono.type_mappings(), None)
            .unwrap();

        // Re-insert the monomorphization.
        self.insert_monomorphization(removed);
    }

    // Tries to monomorphize the given polymorphic type using the given parameter types.
    pub fn try_execute_monomorphization(
        &mut self,
        poly_type_key: TypeKey,
        param_type_keys: Vec<TypeKey>,
        param_locs: &Vec<&impl Locatable>,
        loc: &impl Locatable,
    ) -> TypeKey {
        // Look up the type and make sure it's actually polymorphic.
        let poly_type = self.get_type(poly_type_key);

        // Skip types that already failed analysis.
        if poly_type.is_unknown() {
            return poly_type_key;
        }

        let defined_params = match poly_type.params() {
            Some(params) => params.params.clone(),

            // The type is not polymorphic.
            None => {
                let err = err_unexpected_params(self, poly_type_key, *loc.span());
                self.insert_err(err);
                return poly_type_key;
            }
        };

        // Make sure the right number of params were provided.
        let expected_num_params = defined_params.len();
        let passed_num_params = param_type_keys.len();
        if expected_num_params != passed_num_params {
            self.insert_err(AnalyzeError::new(
                ErrorKind::WrongNumberOfParams,
                format!(
                    "expected {} generic parameter{}, but found {}",
                    expected_num_params,
                    match expected_num_params > 1 {
                        true => "s",
                        false => "",
                    },
                    passed_num_params
                )
                .as_str(),
                *loc.span(),
            ));
            return poly_type_key;
        }

        // Generate a monomorphization for this type. We'll use this to track
        // the fact that this type has been monomorphized.
        let mut mono = Monomorphization {
            poly_type_key,
            // Use a placeholder type for the mono type for now. We'll update it later.
            mono_type_key: self.force_insert_type(poly_type.clone()),
            replaced_params: vec![],
        };
        let mut type_mappings: HashMap<TypeKey, TypeKey> = HashMap::new();
        let mut all_type_keys_match = true;
        let mut param_checks_failed = false;
        let type_display = self.display_type(poly_type_key);

        for (param, (passed_param_tk, param_loc)) in defined_params
            .iter()
            .zip(param_type_keys.iter().zip(param_locs.iter()))
        {
            match self.check_param(*passed_param_tk, *param_loc, param, &type_display) {
                Ok(param_tk) => {
                    mono.replaced_params.push(ReplacedParam {
                        param_type_key: param.generic_type_key,
                        replacement_type_key: param_tk,
                    });

                    type_mappings.insert(param.generic_type_key, param_tk);

                    if param.generic_type_key != param_tk {
                        all_type_keys_match = false;
                    }
                }

                Err(e) => {
                    self.insert_err(e);
                    param_checks_failed = true;
                }
            }
        }

        if param_checks_failed {
            return self.unknown_type_key();
        }

        // Check if we're monomorphizing a type with its own generic parameters. If so, we can just
        // return the original polymorphic type's key.
        if all_type_keys_match {
            return poly_type_key;
        }

        // Check if the type has already been monomorphized. If so, return the
        // existing monomorphic type's key.
        if let Some(monos) = self.monomorphized_types.get(&poly_type_key) {
            if let Some(existing_mono) = monos.get(&mono) {
                return existing_mono.mono_type_key;
            }
        }

        // Before we proceed with monomorphization, we'll preemptively track the monomorphization
        // to prevent infinitely recursive monomorphization. This is important for types that
        // contain references to types that are monomorphizations of themselves.
        self.insert_monomorphization(mono.clone());

        // Monomorphize the type.
        match self.monomorphize_type(poly_type_key, &type_mappings, Some(mono.mono_type_key)) {
            Some(replacement_tk) => {
                let new_type = self.get_type(replacement_tk).clone();
                self.replace_type(mono.mono_type_key, new_type);
            }

            None => {
                panic!("type should have been monomorphized");
            }
        };

        // Mark this new monomorphic type as implementing the specs its polymorphic
        // counterpart implements.
        if let Some(impls) = self.type_impls.get(&poly_type_key) {
            for (spec_tk, impl_info) in impls.spec_impls.clone() {
                self.insert_spec_impl(
                    mono.mono_type_key,
                    spec_tk,
                    HashMap::new(),
                    impl_info.header_span,
                );
            }
        }

        mono.mono_type_key
    }

    /// Analyzes a passed parameter type and checks that it matches the expected
    /// parameter constraints.
    fn check_param<T: Locatable>(
        &mut self,
        param_type_key: TypeKey,
        param_loc: &T,
        expected_param: &AParam,
        type_display: &String,
    ) -> AnalyzeResult<TypeKey> {
        let passed_param_type = self.get_type(param_type_key);

        // Skip further validation if the param value already failed analysis.
        if passed_param_type.is_unknown() {
            return Ok(param_type_key);
        }

        // Make sure the type passed as the parameter is not a spec.
        if passed_param_type.is_spec() {
            return Err(AnalyzeError::new(
                ErrorKind::MismatchedTypes,
                "expected concrete or generic type, but found spec",
                *param_loc.span(),
            )
            .with_detail(
                format_code!(
                    "Expected a concrete or generic type in place of parameter {} on \
                    {}, but found spec {}.",
                    expected_param.name,
                    type_display,
                    passed_param_type.to_spec_type().name,
                )
                .as_str(),
            ));
        }

        // Make sure that the type passed as the parameter value implements
        // the required specs.
        let missing_spec_type_keys =
            self.get_missing_spec_impls(param_type_key, expected_param.generic_type_key);
        let missing_spec_names: Vec<String> = missing_spec_type_keys
            .into_iter()
            .map(|tk| self.display_type(tk))
            .collect();
        if !missing_spec_names.is_empty() {
            let param_type_display = self.display_type(param_type_key);
            return Err(AnalyzeError::new(
                ErrorKind::SpecNotSatisfied,
                format_code!("type {} violates parameter constraints", param_type_display).as_str(),
                *param_loc.span(),
            )
            .with_detail(
                format!(
                    "{} does not implement spec{} {} required \
                    by parameter {} in {}.",
                    format_code!(param_type_display),
                    match missing_spec_names.len() {
                        1 => "",
                        _ => "s",
                    },
                    format_code_vec(&missing_spec_names, ", "),
                    format_code!(expected_param.name),
                    format_code!(type_display),
                )
                .as_str(),
            ));
        }

        Ok(param_type_key)
    }

    /// Inserts the given monomorphization into the program context.
    fn insert_monomorphization(&mut self, mono: Monomorphization) {
        // This is a gross hack, but we'll avoid inserting a type monomorphization in
        // the case where this is a placeholder monomorphization (i.e. the mono type key
        // the same as the poly type key). This prevents a bug where we incorrectly mark
        // the mono type as being the result of a monomorphization of itself.
        if mono.mono_type_key != mono.poly_type_key {
            self.type_monomorphizations
                .insert(mono.mono_type_key, mono.clone());
        }

        match self.monomorphized_types.get_mut(&mono.poly_type_key) {
            Some(set) => {
                set.replace(mono);
            }
            None => {
                self.monomorphized_types
                    .insert(mono.poly_type_key, HashSet::from([mono]));
            }
        };
    }

    /// If `type_key` corresponds to a type that was produced by a monomorphization,
    /// this function returns the type key of its corresponding polymorphic type.
    pub fn get_poly_type_key(&self, mono_tk: TypeKey) -> Option<TypeKey> {
        match self.type_monomorphizations.get(&mono_tk) {
            Some(mono) => Some(mono.poly_type_key),
            None => None,
        }
    }

    /// Returns the type key for the analyzer-internal `<unknown>` type.
    pub fn unknown_type_key(&self) -> TypeKey {
        *self.primitive_type_keys.get("<unknown>").unwrap()
    }

    /// Returns the type key for the analyzer-internal `<none>` type.
    pub fn none_type_key(&self) -> TypeKey {
        *self.primitive_type_keys.get("<none>").unwrap()
    }

    /// Returns the type key for the `bool` type.
    pub fn bool_type_key(&self) -> TypeKey {
        *self.primitive_type_keys.get("bool").unwrap()
    }

    /// Returns the type key for the `i8` type.
    pub fn i8_type_key(&self) -> TypeKey {
        *self.primitive_type_keys.get("i8").unwrap()
    }

    /// Returns the type key for the `u8` type.
    pub fn u8_type_key(&self) -> TypeKey {
        *self.primitive_type_keys.get("u8").unwrap()
    }

    /// Returns the type key for the `i16` type.
    pub fn i16_type_key(&self) -> TypeKey {
        *self.primitive_type_keys.get("i16").unwrap()
    }

    /// Returns the type key for the `u16` type.
    pub fn u16_type_key(&self) -> TypeKey {
        *self.primitive_type_keys.get("u16").unwrap()
    }

    /// Returns the type key for the `i32` type.
    pub fn i32_type_key(&self) -> TypeKey {
        *self.primitive_type_keys.get("i32").unwrap()
    }

    /// Returns the type key for the `u32` type.
    pub fn u32_type_key(&self) -> TypeKey {
        *self.primitive_type_keys.get("u32").unwrap()
    }

    /// Returns the type key for the `f32` type.
    pub fn f32_type_key(&self) -> TypeKey {
        *self.primitive_type_keys.get("f32").unwrap()
    }

    /// Returns the type key for the `i64` type.
    pub fn i64_type_key(&self) -> TypeKey {
        *self.primitive_type_keys.get("i64").unwrap()
    }

    /// Returns the type key for the `u64` type.
    pub fn u64_type_key(&self) -> TypeKey {
        *self.primitive_type_keys.get("u64").unwrap()
    }

    /// Returns the type key for the `f64` type.
    pub fn f64_type_key(&self) -> TypeKey {
        *self.primitive_type_keys.get("f64").unwrap()
    }

    /// Returns the type key for the `int` type.
    pub fn int_type_key(&self) -> TypeKey {
        *self.primitive_type_keys.get("int").unwrap()
    }

    /// Returns the type key for the `uint` type.
    pub fn uint_type_key(&self) -> TypeKey {
        *self.primitive_type_keys.get("uint").unwrap()
    }

    /// Returns the type key for the `str` type.
    pub fn str_type_key(&self) -> TypeKey {
        *self.primitive_type_keys.get("str").unwrap()
    }

    /// Returns the type key for the `char` type.
    pub fn char_type_key(&self) -> TypeKey {
        *self.primitive_type_keys.get("char").unwrap()
    }

    /// Pushes `scope` onto the stack.
    pub fn push_scope(&mut self, scope: Scope) {
        self.cur_mod_ctx_mut().push_scope(scope);
    }

    /// Pops and returns the current scope from the stack.
    pub fn pop_scope(&mut self, check_usage: bool) -> Scope {
        let scope = self.cur_mod_ctx_mut().pop_scope();

        // Warn about unused identifiers.
        if check_usage {
            for ident in scope.unused_idents() {
                self.insert_warn(warn_unused(&ident.name, ident.span));
            }
        }

        scope
    }

    /// Returns the current scope.
    pub fn cur_scope(&self) -> &Scope {
        self.cur_mod_ctx().cur_scope()
    }

    /// Returns all unused imports in the current context.
    pub fn unused_imports(&self) -> (Vec<&Ident>, Vec<&ModAlias>) {
        self.cur_mod_ctx().unused_imports()
    }

    /// Returns the type keys of all non-public functions from default impls that are unused in the
    /// current module.
    pub fn unused_impl_fns(&self) -> Vec<TypeKey> {
        let mut tks = vec![];

        let scope = self.cur_mod_ctx().cur_scope();
        assert_eq!(scope.kind, ScopeKind::TopLevel);

        for tk in scope.get_defined_types() {
            if let Some(impls) = self.type_impls.get(&tk) {
                tks.extend(impls.unused_default_fns())
            }
        }

        tks
    }

    /// Returns the type associated with the given key. Panics if there is no such type.
    pub fn get_type(&self, type_key: TypeKey) -> &AType {
        self.type_store.get_type(type_key)
    }

    /// Replaces the existing type associated with `type_key` with `typ`.
    pub fn replace_type(&mut self, type_key: TypeKey, typ: AType) {
        self.type_store.replace_type(type_key, typ);
    }

    /// Inserts an un-analyzed impl header (the impl type and optional spec being implemented)
    /// into the current module context so we can look it up later to see if that type implements
    /// that spec. That lookup should only be necessary if we're trying to figure out if a type
    /// implements a spec before we've analyzed the impl where the spec is implemented for the type.
    pub fn insert_unchecked_impl(&mut self, impl_type: UnresolvedType, maybe_spec: Option<Symbol>) {
        self.cur_mod_ctx_mut()
            .insert_unchecked_impl(impl_type, maybe_spec);
    }

    /// Sets the type key associated with the current `impl` or `spec` type so it can be retrieved
    /// during analysis of the `impl` or `spec` body.
    pub fn set_cur_self_type_key(&mut self, maybe_type_key: Option<TypeKey>) {
        self.cur_mod_ctx_mut().set_cur_self_type_key(maybe_type_key);
    }

    pub fn set_cur_mod_id(&mut self, mod_id: ModID) {
        if let Entry::Vacant(entry) = self.module_contexts.entry(mod_id) {
            entry.insert(ModuleContext::new(&self.primitive_type_keys));
        }

        self.cur_mod_id = mod_id;
    }

    pub fn cur_mod_id(&self) -> ModID {
        self.cur_mod_id
    }

    pub fn insert_mod_alias(&mut self, alias: ModAlias) -> Result<(), &ModAlias> {
        self.cur_mod_ctx_mut().insert_mod_alias(alias)
    }

    pub fn get_mod_alias(&mut self, mod_name: &Name) -> Option<&ModAlias> {
        self.cur_mod_ctx_mut().get_mod_alias(mod_name)
    }

    /// Returns the type key associated with the current `impl` or `spec` type being analyzed.
    pub fn get_cur_self_type_key(&self) -> Option<TypeKey> {
        self.cur_mod_ctx().cur_self_type_key()
    }

    /// Inserts information about a spec impl block for a type.
    pub fn insert_spec_impl(
        &mut self,
        impl_tk: TypeKey,
        spec_tk: TypeKey,
        member_fns: HashMap<String, TypeKey>,
        header_span: Span,
    ) {
        self.type_impls
            .entry(impl_tk)
            .or_insert(TypeImpls::default())
            .insert_spec_impl(spec_tk, member_fns, header_span);
    }

    /// Inserts information about a default impl block for a type.
    pub fn insert_default_impl(&mut self, impl_tk: TypeKey, member_fns: HashMap<String, TypeKey>) {
        self.type_impls
            .entry(impl_tk)
            .or_insert(TypeImpls::default())
            .insert_default_impl(member_fns);
    }

    /// Returns the type key of the spec that the given function on the given implements.
    pub fn get_spec_impl_by_fn(&self, fn_type_key: TypeKey) -> Option<TypeKey> {
        let func = self.get_type(fn_type_key).to_fn_sig();
        match func.maybe_impl_type_key {
            Some(impl_tk) => match self.type_impls.get(&impl_tk) {
                Some(impls) => impls.get_spec_type_key(fn_type_key),
                // If there is no type impl, then maybe the function's impl type is a spec.
                // This can happen in cases where the function is actually a method on a generic
                // type declared as a parameter that implements a spec.
                None => match self.get_type(impl_tk).is_spec() {
                    true => Some(impl_tk),
                    false => None,
                },
            },
            None => None,
        }
    }

    /// Tries to locate (or generate) the member function with the given name on the given type.
    /// Returns:
    ///  - `Ok(Some(fn_sig))` if we found exactly one matching function on the type
    ///  - `Ok(None)` if we found no matching functions were found on the type
    ///  - `Err(tks)` if we found many matching functions on the type
    pub fn get_or_monomorphize_member_fn(
        &mut self,
        type_key: TypeKey,
        fn_name: &str,
    ) -> Result<Option<AFnSig>, ()> {
        match self.get_member_fns(type_key, fn_name) {
            // We didn't find any member functions for this type, but maybe this type was generated
            // as the result of a monomorphization and we have yet to generate this member function
            // for it. Let's check...
            Ok(None) => self.try_monomorphize_member_fn(type_key, fn_name),

            // Exactly one function by that name was found for the type. This is the ideal case.
            Ok(Some(tk)) => {
                let fn_sig = self.get_type(tk).to_fn_sig();
                Ok(Some(fn_sig.clone()))
            }

            // Many functions were found by that name.
            _ => Err(()),
        }
    }

    /// Tries to locate member functions with the given name on the given type. Returns
    ///  - `Ok(None)` if no matching member functions exist
    ///  - `Ok(Some(tk))` if exactly one matching member function exists
    ///  - `Err(())` if multiple matching member functions are found.
    fn get_member_fns(&mut self, type_key: TypeKey, fn_name: &str) -> Result<Option<TypeKey>, ()> {
        match self.type_impls.get_mut(&type_key) {
            Some(impls) => impls.get_fns_by_name(fn_name),
            None => Ok(None),
        }
    }

    /// Returns the type key of the default function on the given type with the given name, or
    /// None if no such function exists.
    pub fn get_default_member_fn(&mut self, type_key: TypeKey, fn_name: &str) -> Option<TypeKey> {
        match self.type_impls.get_mut(&type_key) {
            Some(impls) => impls.get_default_fn(fn_name),
            None => None,
        }
    }

    /// Tries to find a function named `fn_name` that is a member of the given type that forms
    /// part of the implementation of the given spec.
    pub fn get_member_fn_from_spec_impl(
        &self,
        type_key: TypeKey,
        spec_tk: TypeKey,
        fn_name: &str,
    ) -> Option<TypeKey> {
        let type_impls = match self.type_impls.get(&type_key) {
            Some(impls) => impls,
            None => return None,
        };

        type_impls.get_fn_from_spec_impl(spec_tk, fn_name)
    }

    /// Tries to locate the given member function on the parent polymorphic type and monomorphizes
    /// it, if found.
    fn try_monomorphize_member_fn(
        &mut self,
        type_key: TypeKey,
        fn_name: &str,
    ) -> Result<Option<AFnSig>, ()> {
        // Check if the given type is the result of a monomorphization. If not, then we're not
        // going to find the function so we can abort early.
        let mono = match self.type_monomorphizations.get(&type_key) {
            Some(mono) => mono.clone(),
            None => return Ok(None),
        };

        // Try to find the function by name on the parent polymorphic type.
        let poly_fn_tk = match self.get_member_fns(mono.poly_type_key, fn_name) {
            // No function found.
            Ok(None) => return Ok(None),
            // Exactly one function found. This is what we want.
            Ok(Some(tk)) => tk,
            // Many functions found by that name. We can't proceed because of this ambiguity.
            _ => return Err(()),
        };

        let is_pub = self.member_fn_is_pub(mono.poly_type_key, poly_fn_tk);

        // Monomorphize the function from the polymorphic parent type.
        let type_mappings = mono.type_mappings();
        let mono_fn_sig = match self.monomorphize_fn_type(poly_fn_tk, &type_mappings, None) {
            Some(fn_tk) => self.get_type(fn_tk).to_fn_sig().clone(),
            // Monomorphization failed.
            None => return Ok(None),
        };

        // Figure out if this function was implemented as part of a spec. If so, we need to
        // associate the newly-monomorphized function with that same spec.
        let maybe_spec_tk = self
            .type_impls
            .get(&mono.poly_type_key)
            .unwrap()
            .get_spec_type_key(poly_fn_tk);

        self.insert_member_fn(type_key, maybe_spec_tk, mono_fn_sig.clone());
        if is_pub {
            self.mark_member_fn_pub(type_key, mono_fn_sig.type_key);
        }

        Ok(Some(mono_fn_sig))
    }

    /// Records the given member function as public in the program context.
    pub fn mark_member_fn_pub(&mut self, type_key: TypeKey, fn_type_key: TypeKey) {
        self.type_impls
            .get_mut(&type_key)
            .expect(format!("type with key {type_key} should have impls").as_str())
            .mark_fn_pub(fn_type_key);
    }

    /// Records the given struct field as public in the program context.
    pub fn mark_struct_field_pub(&mut self, type_key: TypeKey, field_name: &str) {
        match self.pub_struct_field_names.get_mut(&type_key) {
            Some(set) => {
                set.insert(field_name.to_string());
            }
            None => {
                self.pub_struct_field_names
                    .insert(type_key, HashSet::from([field_name.to_string()]));
            }
        }
    }

    /// Returns true if the field with the given name on the given struct type is
    /// accessible from the current module. This will be trie if the type is defined
    /// in this module or the field was declared public.
    pub fn struct_field_is_accessible(&self, type_key: TypeKey, field_name: &str) -> bool {
        self.type_declared_in_cur_mod(type_key) || self.struct_field_is_pub(type_key, field_name)
    }

    /// Returns true if the field with the given name on the given struct type is public.
    fn struct_field_is_pub(&self, type_key: TypeKey, field_name: &str) -> bool {
        match self.pub_struct_field_names.get(&type_key) {
            Some(map) => map.contains(field_name),
            None => false,
        }
    }

    /// Returns true if the member function is accessible from the current module.
    /// This will be true if the type is defined in this module or the function was
    /// declared public.
    pub fn member_fn_is_accessible(&self, type_key: TypeKey, fn_type_key: TypeKey) -> bool {
        self.type_declared_in_cur_mod(type_key) || self.member_fn_is_pub(type_key, fn_type_key)
    }

    /// Returns true if the given type was declared in the current module.
    pub fn type_declared_in_cur_mod(&self, type_key: TypeKey) -> bool {
        match self.type_declaration_mod_ids.get(&type_key) {
            Some(mod_path) => mod_path == &self.cur_mod_id,
            None => false,
        }
    }

    /// Returns true if the given type member function is public.
    fn member_fn_is_pub(&self, type_key: TypeKey, fn_type_key: TypeKey) -> bool {
        // Generic types always have public member fns.
        if self.get_type(type_key).is_generic() {
            return true;
        }

        match self.type_impls.get(&type_key) {
            Some(impls) => impls.pub_fn_tks.contains(&fn_type_key),
            None => false,
        }
    }

    /// Inserts `member_fn_sig` as a member function on the type that corresponds to `type_key`.
    pub fn insert_member_fn(
        &mut self,
        type_key: TypeKey,
        maybe_spec_type_key: Option<TypeKey>,
        member_fn_sig: AFnSig,
    ) {
        match self.type_impls.get_mut(&type_key) {
            Some(impls) => {
                impls.insert_fn(
                    maybe_spec_type_key,
                    member_fn_sig.name,
                    member_fn_sig.type_key,
                );
            }
            None => {
                self.insert_default_impl(
                    type_key,
                    HashMap::from([(member_fn_sig.name, member_fn_sig.type_key)]),
                );
            }
        }
    }

    /// Returns true if the current scope is a function body or exists inside a function body.
    pub fn is_in_fn(&self) -> bool {
        self.cur_mod_ctx()
            .get_scope_by_kind(&ScopeKind::FnBody)
            .is_some()
    }

    /// Returns true if the current scope is a `from` body or exists inside a `from` body.
    pub fn is_in_from_block(&self) -> bool {
        self.cur_mod_ctx()
            .get_scope_by_kind(&ScopeKind::FromBody)
            .is_some()
    }

    /// Returns a new name for an anonymous function created inside the current scope. This
    /// also has the side effect of incrementing the anonymous function count for the current
    /// scope.
    pub fn new_anon_fn_name(&mut self) -> String {
        let mod_ctx = self.cur_mod_ctx_mut();
        let scope = mod_ctx.get_scope_by_kind_mut(&ScopeKind::FnBody).unwrap();
        format!("anon_fn::{}", scope.get_and_inc_fn_count())
    }

    /// Returns true if the current scope is a loop body or falls within a loop body.
    pub fn is_in_loop(&self) -> bool {
        self.cur_mod_ctx()
            .get_scope_by_kind(&ScopeKind::LoopBody)
            .is_some()
    }

    pub fn set_cur_file_id(&mut self, file_id: FileID) -> Option<FileID> {
        self.cur_mod_ctx_mut().set_cur_file_id(file_id)
    }

    pub fn insert_ident(&mut self, ident: Ident) -> Result<(), &Ident> {
        if let IdentKind::Type {
            is_pub: true,
            type_key,
            ..
        } = &ident.kind
        {
            self.pub_type_keys.insert(*type_key);
        }

        self.cur_mod_ctx_mut().insert_ident(ident)
    }

    pub fn insert_imported_ident(&mut self, ident: Ident) -> Result<(), &Ident> {
        self.cur_mod_ctx_mut().insert_imported_ident(ident)
    }

    pub fn get_local_ident_unchecked(&self, name: &str) -> Option<&Ident> {
        match self.cur_mod_ctx().get_ident(name) {
            Some(ident) => Some(ident),
            None => None,
        }
    }

    pub fn get_local_ident(&mut self, name: &str, set_usage: Option<Usage>) -> Option<&Ident> {
        match self
            .cur_mod_ctx_mut()
            .get_ident_mut(name, set_usage.clone())
        {
            Some(ident) => {
                // If the identifier refers to something that has not yet been analyzed, analyze it.
                match &ident.kind {
                    IdentKind::UncheckedConst(_)
                    | IdentKind::UncheckedStatic(_)
                    | IdentKind::UncheckedFn(_)
                    | IdentKind::UncheckedExternFn(_)
                    | IdentKind::UncheckedStructType(_)
                    | IdentKind::UncheckedEnumType(_)
                    | IdentKind::UncheckedSpecType(_) => self.analyze_unchecked_ident(&name),
                    _ => {}
                }
            }
            None => return None,
        };

        match self.cur_mod_ctx_mut().get_ident_mut(name, set_usage) {
            Some(ident) => Some(ident),
            None => None,
        }
    }

    fn analyze_unchecked_ident(&mut self, name: &str) {
        // Unwind the stack to the top level of the module before analyzing the unchecked code.
        let old_self_tk = self.get_cur_self_type_key();
        self.set_cur_self_type_key(None);
        let scopes = self.cur_mod_ctx_mut().unwind_to_top_scope();

        let ident = self
            .cur_mod_ctx_mut()
            .remove_unchecked_ident_from_cur_scope(name)
            .unwrap();

        // Temporarily twitch to the identifier's file ID.
        let old_file_id = self.set_cur_file_id(ident.span.file_id);

        match ident.kind {
            IdentKind::UncheckedConst(const_) => {
                AConst::from(self, &const_);
            }

            IdentKind::UncheckedStatic(static_) => {
                AStatic::from(self, &static_);
            }

            IdentKind::UncheckedFn(func) => {
                let a_fn = AFn::from(self, &func);
                self.insert_analyzed_fn(a_fn);
            }

            IdentKind::UncheckedExternFn(func) => {
                let ext_fn = AExternFn::from(self, &func);
                self.insert_analyzed_extern_fn(ext_fn);
            }

            IdentKind::UncheckedStructType(struct_type) => {
                AStructType::from(self, &struct_type);
            }

            IdentKind::UncheckedEnumType(enum_type) => {
                AEnumType::from(self, &enum_type);
            }

            IdentKind::UncheckedSpecType(spec_type) => {
                ASpecType::from(self, &spec_type);
            }

            _ => {
                unreachable!()
            }
        }

        // Return the stack to its previous state before returning.
        self.cur_mod_ctx_mut().push_scopes(scopes);
        self.set_cur_self_type_key(old_self_tk);
        self.set_cur_file_id(old_file_id.unwrap());
    }

    pub fn get_foreign_ident(&self, mod_id: ModID, name: &str) -> Option<&Ident> {
        self.module_contexts
            .get(&mod_id)
            .unwrap()
            .get_top_level_ident(name)
    }

    /// Searches for local identifier only in the current scope.
    pub fn get_ident_in_cur_scope(&self, name: &str) -> Option<&Ident> {
        self.cur_mod_ctx().get_ident_in_cur_scope(name)
    }

    pub fn remove_unchecked_ident_from_cur_scope(&mut self, name: &str) -> Option<Ident> {
        self.cur_mod_ctx_mut()
            .remove_unchecked_ident_from_cur_scope(name)
    }

    /// Returns a mutable reference to the identifier with the given name in the current scope, if
    /// any.
    pub fn get_ident_in_cur_scope_mut(&mut self, name: &str) -> Option<&mut Ident> {
        self.cur_mod_ctx_mut().get_ident_in_cur_scope_mut(name)
    }

    /// Returns the expected return type key for the current function body scope.
    pub fn cur_expected_ret_type_key(&self) -> Option<TypeKey> {
        self.cur_mod_ctx()
            .get_scope_by_kind(&ScopeKind::FnBody)
            .unwrap()
            .ret_type_key()
    }

    /// Returns the expected yield type key for the current from body scope, or
    /// `None` if there isn't one.
    pub fn cur_expected_yield_type_key(&self) -> Option<TypeKey> {
        self.cur_mod_ctx()
            .get_scope_by_kind(&ScopeKind::FromBody)
            .unwrap()
            .yield_type_key()
    }

    /// Sets the expected yield type key for the current do body scope. Panics
    /// if we're not in a `from` scope or the existing `from` scope already has
    /// a yield type key set.
    pub fn set_cur_expected_yield_type_key(&mut self, type_key: TypeKey) {
        let existing = self
            .cur_mod_ctx_mut()
            .get_scope_by_kind_mut(&ScopeKind::FromBody)
            .unwrap()
            .set_yield_type_key(Some(type_key));
        assert!(
            existing.is_none(),
            "existing yield type key was overwritten"
        );
    }

    /// Returns a string containing the human-readable version of the type corresponding to the
    /// given type key.
    pub fn display_type(&self, type_key: TypeKey) -> String {
        let typ = self.get_type(type_key);
        match typ {
            AType::Bool
            | AType::Str
            | AType::Char
            | AType::I8
            | AType::U8
            | AType::I16
            | AType::U16
            | AType::U32
            | AType::I32
            | AType::F32
            | AType::I64
            | AType::U64
            | AType::F64
            | AType::Int
            | AType::Uint => {
                format!("{}", typ)
            }

            AType::Struct(struct_type) => {
                format!("{}{}", struct_type.name, self.display_param_types(type_key))
            }

            AType::Enum(enum_type) => {
                format!("{}{}", enum_type.name, self.display_param_types(type_key))
            }

            AType::Spec(spec_type) => {
                format!("{}{}", spec_type.name, self.display_param_types(type_key))
            }

            AType::Tuple(tuple_type) => {
                let mut s = format!("{{");

                for (i, field) in tuple_type.fields.iter().enumerate() {
                    s += format!("{}", self.display_type(field.type_key)).as_str();

                    if i + 1 < tuple_type.fields.len() {
                        s += format!(", ").as_str();
                    }
                }

                s + format!("}}").as_str()
            }

            AType::Array(array_type) => match &array_type.maybe_element_type_key {
                Some(key) => {
                    format!("[{}; {}]", self.display_type(*key), array_type.len)
                }

                None => "[]".to_string(),
            },

            AType::Function(fn_sig) => fn_sig.display(self),

            AType::Pointer(ptr_type) => format!(
                "*{}{}",
                match ptr_type.is_mut {
                    true => "mut ",
                    false => "",
                },
                self.display_type(ptr_type.pointee_type_key)
            )
            .to_string(),

            AType::Generic(t) => t.name.clone(),

            AType::Unknown(name) => format!("{}", name),
        }
    }

    pub fn push_params(&mut self, params: AParams) {
        self.push_scope(Scope::new(ScopeKind::Params, None));

        for param in params.params {
            self.insert_ident(Ident::new_type(
                param.name,
                false,
                param.generic_type_key,
                Some(self.cur_mod_id),
                param.span,
            ))
            .unwrap();
        }
    }

    pub fn pop_params(&mut self, check_usage: bool) {
        assert_eq!(self.pop_scope(check_usage).kind, ScopeKind::Params);
    }

    pub fn type_is_pub(&self, type_key: TypeKey) -> bool {
        self.pub_type_keys.contains(&type_key)
    }

    pub fn insert_analyzed_fn(&mut self, func: AFn) {
        self.cur_mod_ctx_mut().insert_fn(func);
    }

    pub fn insert_analyzed_impl(&mut self, impl_: AImpl) {
        self.cur_mod_ctx_mut().insert_impl(impl_);
    }

    pub fn insert_analyzed_extern_fn(&mut self, extern_fn: AExternFn) {
        self.cur_mod_ctx_mut().insert_extern_fn(extern_fn);
    }

    pub fn drain_fns(&mut self) -> (Vec<AFn>, Vec<AImpl>, Vec<AExternFn>) {
        self.cur_mod_ctx_mut().drain_fns()
    }

    fn display_param_types(&self, type_key: TypeKey) -> String {
        let mut params = "".to_string();
        if let Some(mono) = self.type_monomorphizations.get(&type_key) {
            params += "[";
            for (i, replaced_param) in mono.replaced_params.iter().enumerate() {
                // Prevent infinite recursion.
                let param_display = if replaced_param.replacement_type_key == type_key {
                    self.display_type(replaced_param.param_type_key)
                } else {
                    self.display_type(replaced_param.replacement_type_key)
                };

                match i {
                    0 => {
                        params += param_display.as_str();
                    }
                    _ => {
                        params += format!(", {}", param_display).as_str();
                    }
                }
            }

            params += "]";
        }

        params
    }
}
