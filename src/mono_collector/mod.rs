use crate::analyzer::analyze::ProgramAnalysis;
use crate::analyzer::ast::expr::{AExpr, AExprKind};
use crate::analyzer::ast::ext::AExternFn;
use crate::analyzer::ast::func::AFn;
use crate::analyzer::ast::r#match::APattern;
use crate::analyzer::ast::r#type::AType;
use crate::analyzer::ast::statement::AStatement;
use crate::analyzer::prog_context::{Monomorphization, ProgramContext, TypeImpls};
use crate::analyzer::type_store::{GetType, TypeKey, TypeStore};
use crate::codegen::program::CodeGenConfig;
use crate::parser::{ModID, SrcInfo};
use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};
use std::hash::{Hash, Hasher};

/// Represents a monomorhic function. This will either be a function that is already
/// monomorphic, or a polymorphic function with type mappings that map its generic parameters
/// to concrete types.  
#[derive(Debug, Eq, Clone)]
pub struct MonoItem {
    /// The type key of the function type (may or may not be polymorphic).
    pub type_key: TypeKey,
    /// The type mappings that map generic function parameter types to their concrete types.
    pub type_mappings: HashMap<TypeKey, TypeKey>,
}

impl PartialEq for MonoItem {
    fn eq(&self, other: &Self) -> bool {
        // Two MonoItems are considered equal if they are the same function with the same
        // type mappings.
        self.type_key == other.type_key && self.type_mappings == other.type_mappings
    }
}

impl Hash for MonoItem {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // MonoItems should hash to the same value if they have the same function type key and
        // type mappings.
        self.type_key.hash(state);
        BTreeMap::from_iter(self.type_mappings.clone()).hash(state);
    }
}

/// Stores information about the monomorphization tree as we traverse it.
struct MonoItemCollector {
    ctx: ProgramContext,
    /// Maps all function type keys to their declarations.
    fns: HashMap<TypeKey, AFn>,
    /// Maps all extern function type keys to their declarations.
    extern_fns: HashMap<TypeKey, AExternFn>,
    /// Tracks the type keys of nested functions (functions that are declared inside other
    /// functions).
    nested_fns: HashSet<TypeKey>,
    /// Tracks used extern functions.
    used_extern_fns: HashSet<TypeKey>,
    /// A queue of items that still need to be checked and collected for monomorphization.
    incomplete_mono_items: VecDeque<MonoItem>,
    /// A vec of items that have been collected for monomorphization.
    complete_mono_items: Vec<MonoItem>,
    /// Tracks items that have already been queued so we don't re-queue them.
    already_queued_items: HashSet<MonoItem>,
}

impl MonoItemCollector {
    /// Creates a new empty context.
    fn new(ctx: ProgramContext) -> MonoItemCollector {
        // Initialize an empty root mono item.
        let root_item = MonoItem {
            type_key: 0,
            type_mappings: Default::default(),
        };

        MonoItemCollector {
            ctx,
            fns: Default::default(),
            extern_fns: Default::default(),
            nested_fns: Default::default(),
            used_extern_fns: Default::default(),
            incomplete_mono_items: Default::default(),
            already_queued_items: HashSet::from([root_item.clone()]),
            complete_mono_items: vec![root_item],
        }
    }

    /// Gets a type by its type key.
    fn get_type(&self, type_key: TypeKey) -> &AType {
        self.ctx.type_store.get_type(type_key)
    }

    /// Inserts a function into the context, so it can be looked up by its type key later.
    fn insert_fn(&mut self, func: AFn, is_nested: bool) {
        if is_nested {
            self.nested_fns.insert(func.signature.type_key);
        }

        self.fns.insert(func.signature.type_key, func);
    }

    /// Collects a monomorphic item. All collected items are functions for which we'll generate
    /// machine code.
    fn collect_item(&mut self, item: MonoItem) {
        self.complete_mono_items.push(item);
    }

    /// Walks the types recursively starting with the given type key looking for generic types.
    /// Any generic type keys that are found will be mapped to their corresponding concrete type
    /// in `type_mapping`.
    fn map_nested_generics(
        &self,
        type_key: TypeKey,
        traversed: &mut HashSet<TypeKey>,
        type_mapping: &mut HashMap<TypeKey, TypeKey>,
    ) {
        if !traversed.insert(type_key) {
            return;
        }

        match self.get_type(type_key) {
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
            | AType::Char => {}

            AType::Struct(struct_type) => {
                for field in &struct_type.fields {
                    self.map_nested_generics(field.type_key, traversed, type_mapping);
                }
            }

            AType::Enum(enum_type) => {
                for variant in enum_type.variants.values() {
                    if let Some(variant_tk) = variant.maybe_type_key {
                        self.map_nested_generics(variant_tk, traversed, type_mapping);
                    }
                }
            }

            AType::Tuple(tuple_type) => {
                for field in &tuple_type.fields {
                    self.map_nested_generics(field.type_key, traversed, type_mapping);
                }
            }

            AType::Array(array_type) => {
                if let Some(elem_tk) = array_type.maybe_element_type_key {
                    self.map_nested_generics(elem_tk, traversed, type_mapping);
                }
            }

            AType::Function(sig) => {
                for arg in &sig.args {
                    self.map_nested_generics(arg.type_key, traversed, type_mapping);
                }

                if let Some(ret_tk) = sig.maybe_ret_type_key {
                    self.map_nested_generics(ret_tk, traversed, type_mapping);
                }
            }

            AType::Pointer(ptr_type) => {
                self.map_nested_generics(ptr_type.pointee_type_key, traversed, type_mapping);
            }

            AType::Spec(_) => {
                panic!("unexpected spec type")
            }

            AType::Generic(_) => {
                type_mapping
                    .entry(type_key)
                    .or_insert_with(|| self.deep_map_type_key(type_key));
            }

            AType::Unknown(_) => {
                panic!("encountered unknown type")
            }
        }
    }

    /// Queues a function for monomorphization.
    fn queue_item(&mut self, type_key: TypeKey, mut type_mapping: HashMap<TypeKey, TypeKey>) {
        // Update mapped values based on existing mappings in parent contexts.
        for v in type_mapping.values_mut() {
            *v = self.map_type_key(*v);
        }

        let parent_item = self.complete_mono_items.last().unwrap();
        let is_nested = self.nested_fns.contains(&type_key);

        // Include type mappings from parent contexts if the item could possibly need them.
        if is_nested {
            for (k, v) in &parent_item.type_mappings {
                // Don't overwrite mappings from child contexts.
                type_mapping.entry(*k).or_insert(*v);
            }
        }

        // For all target types included in the type mapping, make sure that any generic types
        // they contain are also included in the type mapping.
        let mut traversed = HashSet::new();
        for target_tk in type_mapping.values().cloned().collect::<Vec<_>>() {
            self.map_nested_generics(target_tk, &mut traversed, &mut type_mapping);
        }

        let item = MonoItem {
            type_key,
            type_mappings: type_mapping,
        };

        // Don't queue the item if it has already been queued or is identical to its parent (a
        // recursive call).
        if !self.already_queued_items.contains(&item) && &item != parent_item {
            self.already_queued_items.insert(item.clone());
            self.incomplete_mono_items.push_back(item);
        }
    }

    /// Pops the item from the front of the queue of functions that need monomorphization.
    fn pop_queued_item(&mut self) -> bool {
        if let Some(item) = self.incomplete_mono_items.pop_front() {
            self.collect_item(item);
            return true;
        }

        false
    }

    /// Maps the given type key to a new type key based on the type mappings in the current
    /// context (i.e. generic parameter mappings for the current function).
    fn map_type_key(&self, type_key: TypeKey) -> TypeKey {
        let item = self.complete_mono_items.last().unwrap();
        if let Some(tk) = item.type_mappings.get(&type_key) {
            return *tk;
        }

        type_key
    }

    fn deep_map_type_key(&self, type_key: TypeKey) -> TypeKey {
        for item in self.complete_mono_items.iter().rev() {
            if let Some(tk) = item.type_mappings.get(&type_key) {
                return *tk;
            }
        }

        type_key
    }
}

/// Stores information about a monomorphized program.
pub struct MonoProg {
    pub config: CodeGenConfig,
    pub type_store: TypeStore,
    /// Maps monomorphic type keys to the monomorphizations that were used to derive them.
    pub type_monomorphizations: HashMap<TypeKey, Monomorphization>,
    /// Maps type keys to information about their `impl` blocks.
    pub type_impls: HashMap<TypeKey, TypeImpls>,
    /// Maps module IDs to monomorphized functions from those modules.
    pub mono_items: HashMap<ModID, Vec<MonoItem>>,
    /// The type keys of all public functions.
    pub pub_fns: HashSet<TypeKey>,
    /// Maps function type keys to their implementations.
    pub fns: HashMap<TypeKey, AFn>,
    /// Maps module IDs to mappings from extern function type keys to bools indicating whether
    /// they're declared `pub`.
    pub extern_fns: HashMap<ModID, HashMap<TypeKey, AExternFn>>,
    /// Maps module IDs to mappings from `const` names to their values for those modules.
    pub mod_consts: HashMap<ModID, HashMap<String, AExpr>>,
    /// Maps module IDs to mappings from `static` names to their values for those modules.
    pub mod_statics: HashMap<ModID, HashMap<String, AExpr>>,
    /// Stores the type key of the `main` function, if any.
    pub maybe_main_fn_tk: Option<TypeKey>,
    /// The ID of the root module.
    pub root_mod_id: ModID,
}

/// Traverses functions in the program call graph, tracking and monomorphizing each one that
/// we need to generate code for. The basic algorithm is as follows:
/// 1. Find the roots. If there is a main function (i.e. we're generating an executable
///    program), then it will be the only root. If there isn't one (i.e. we're generating
///    code for a library), then all top-level monomorphic functions are considered roots.
/// 2. Push all roots into the queue of un-checked functions.
/// 3. While there are functions in the queue, pop the next function from the front of the queue
///    and walk it to discover which functions it uses. For each function we encounter, push it
///    into the queue with its generic parameter type mappings if it hasn't already been checked.
///
/// This way, we end up building what is essentially a function monomorphization tree that we can
/// traverse during codegen.
pub fn mono_prog(src_info: &SrcInfo, analysis: ProgramAnalysis) -> MonoProg {
    let mut maybe_main_fn_tk = None;
    let mut collector = MonoItemCollector::new(analysis.ctx);

    // Collect all the functions up into a map, so we can look them up easily.
    for (mod_id, module) in analysis.analyzed_mods {
        let is_root_mod = mod_id == analysis.root_mod_id;

        for func in module.module.fns {
            let is_main = maybe_main_fn_tk.is_none()
                && is_root_mod
                && func.signature.name == "main"
                && func.signature.maybe_impl_type_key.is_none();

            if is_main {
                maybe_main_fn_tk = Some(func.signature.type_key);
            }

            track_fn(&mut collector, is_main, func);
        }

        for impl_ in module.module.impls {
            for func in impl_.member_fns {
                track_fn(&mut collector, false, func);
            }
        }

        for extern_fn in module.module.extern_fns {
            collector
                .extern_fns
                .insert(extern_fn.fn_sig.type_key, extern_fn);
        }
    }

    while collector.pop_queued_item() {
        walk_next_item(&mut collector);
    }

    // Filter out unused extern functions.
    let mut pub_fns = HashSet::new();
    let mut extern_fns = HashMap::new();
    for (fn_tk, extern_fn) in collector.extern_fns {
        if !collector.used_extern_fns.contains(&fn_tk) {
            continue;
        }

        if collector.ctx.fn_is_pub(fn_tk) {
            pub_fns.insert(fn_tk);
        }

        let file_id = extern_fn.span.file_id;
        let mod_id = src_info.mod_info.get_id_by_file_id(file_id).unwrap();
        extern_fns
            .entry(mod_id)
            .or_insert(HashMap::new())
            .insert(fn_tk, extern_fn);
    }

    let (mod_consts, mod_statics) = collector.ctx.drain_mod_consts_and_statics();

    // Collect all mono items by mod ID. We skip the root item because it's not meaningful.
    let mut mono_items = HashMap::new();
    let mut iter = collector.complete_mono_items.into_iter();
    iter.next();
    for item in iter {
        if collector.ctx.fn_is_pub(item.type_key) {
            pub_fns.insert(item.type_key);
        }

        let file_id = collector.ctx.get_type(item.type_key).span().file_id;
        let mod_id = src_info.mod_info.get_id_by_file_id(file_id).unwrap();
        mono_items.entry(mod_id).or_insert(vec![]).push(item);
    }

    MonoProg {
        mod_consts,
        mod_statics,
        config: collector.ctx.config,
        type_store: collector.ctx.type_store,
        type_monomorphizations: collector.ctx.type_monomorphizations,
        type_impls: collector.ctx.type_impls,
        mono_items,
        pub_fns,
        fns: collector.fns,
        extern_fns,
        maybe_main_fn_tk,
        root_mod_id: analysis.root_mod_id,
    }
}

fn track_fn(collector: &mut MonoItemCollector, queue: bool, func: AFn) {
    let fn_tk = func.signature.type_key;
    collector.insert_fn(func, false);

    if queue {
        collector.queue_item(fn_tk, HashMap::new());
    }
}

fn walk_next_item(collector: &mut MonoItemCollector) {
    let item = collector.complete_mono_items.last().unwrap();
    let func = collector.fns.get(&item.type_key).unwrap();

    for statement in func.body.statements.clone() {
        walk_statement(collector, statement);
    }
}

fn walk_statement(collector: &mut MonoItemCollector, statement: AStatement) {
    match statement {
        AStatement::VariableDeclaration(var_decl) => {
            walk_expr(collector, var_decl.val);
        }

        AStatement::VariableAssignment(var_assign) => {
            walk_expr(collector, var_assign.val);
            walk_expr(collector, var_assign.target);
        }

        AStatement::FunctionDeclaration(func) => {
            collector.insert_fn(func.clone(), true);

            if !func.signature.is_parameterized() {
                collector.queue_item(func.signature.type_key, HashMap::new());
            }
        }

        AStatement::Closure(closure) => {
            for statement in closure.statements {
                walk_statement(collector, statement);
            }
        }

        AStatement::FunctionCall(call) => {
            for arg in call.args {
                walk_expr(collector, arg);
            }

            walk_expr(collector, call.fn_expr);
        }

        AStatement::Conditional(cond) => {
            for branch in cond.branches {
                if let Some(expr) = branch.cond {
                    walk_expr(collector, expr);
                }

                for statement in branch.body.statements {
                    walk_statement(collector, statement);
                }
            }
        }

        AStatement::Match(match_) => {
            walk_expr(collector, match_.target);

            for case in match_.cases {
                match case.pattern {
                    APattern::Exprs(exprs) => {
                        for expr in exprs {
                            walk_expr(collector, expr);
                        }
                    }
                    APattern::LetEnumVariants(_, _, _, _)
                    | APattern::LetSymbol(_, _)
                    | APattern::Wildcard => {}
                }

                if let Some(cond) = case.maybe_cond {
                    walk_expr(collector, cond);
                }

                for statement in case.body.statements {
                    walk_statement(collector, statement);
                }
            }
        }

        AStatement::Loop(loop_) => {
            if let Some(statement) = loop_.maybe_init {
                walk_statement(collector, statement);
            }

            if let Some(expr) = loop_.maybe_cond {
                walk_expr(collector, expr);
            }

            for statement in loop_.body.statements {
                walk_statement(collector, statement);
            }

            if let Some(statement) = loop_.maybe_update {
                walk_statement(collector, statement);
            }
        }

        // Nothing to do here.
        AStatement::Break(_)
        | AStatement::Continue(_)
        | AStatement::StructTypeDeclaration(_)
        | AStatement::EnumTypeDeclaration(_) => {}

        AStatement::Return(ret) => {
            if let Some(expr) = ret.val {
                walk_expr(collector, expr);
            }
        }

        AStatement::Yield(yield_) => {
            walk_expr(collector, yield_.value);
        }

        AStatement::Const(const_) => {
            walk_expr(collector, const_.value);
        }

        AStatement::Static(static_) => {
            walk_expr(collector, static_.value);
        }
    }
}

fn walk_expr(collector: &mut MonoItemCollector, expr: AExpr) {
    match expr.kind {
        AExprKind::Symbol(sym) => walk_type_key(collector, sym.type_key),
        AExprKind::MemberAccess(access) => {
            walk_expr(collector, access.base_expr);
            walk_type_key(collector, access.member_type_key);
        }
        AExprKind::StructInit(init) => {
            for (_, val) in init.field_values {
                walk_expr(collector, val);
            }
        }
        AExprKind::EnumInit(init) => {
            if let Some(val) = init.maybe_value {
                walk_expr(collector, *val);
            }
        }
        AExprKind::TupleInit(init) => {
            for val in init.values {
                walk_expr(collector, val);
            }
        }
        AExprKind::ArrayInit(init) => {
            for val in init.values {
                walk_expr(collector, val);
            }
        }
        AExprKind::Index(index) => {
            walk_expr(collector, index.index_expr);
            walk_expr(collector, index.collection_expr);
        }
        AExprKind::FunctionCall(call) => {
            for arg in call.args {
                walk_expr(collector, arg);
            }

            walk_expr(collector, call.fn_expr);
        }
        AExprKind::AnonFunction(func) => {
            let fn_tk = func.signature.type_key;
            collector.insert_fn(*func, true);
            collector.queue_item(fn_tk, HashMap::new());
        }
        AExprKind::UnaryOperation(_, operand) => {
            walk_expr(collector, *operand);
        }
        AExprKind::BinaryOperation(left, _, right) => {
            walk_expr(collector, *left);
            walk_expr(collector, *right);
        }
        AExprKind::TypeCast(expr, _) => {
            walk_expr(collector, *expr);
        }
        AExprKind::Sizeof(_) => {}
        AExprKind::From(statement) => {
            walk_statement(collector, *statement);
        }

        // These expressions never contain polymorphic items.
        AExprKind::BoolLiteral(_)
        | AExprKind::I8Literal(_)
        | AExprKind::U8Literal(_)
        | AExprKind::I16Literal(_)
        | AExprKind::U16Literal(_)
        | AExprKind::I32Literal(_)
        | AExprKind::U32Literal(_)
        | AExprKind::F32Literal(_)
        | AExprKind::I64Literal(_)
        | AExprKind::U64Literal(_)
        | AExprKind::F64Literal(_, _)
        | AExprKind::IntLiteral(_, _)
        | AExprKind::UintLiteral(_)
        | AExprKind::StrLiteral(_)
        | AExprKind::CharLiteral(_) => {}

        AExprKind::Unknown => {
            panic!("unknown expression kind")
        }
    }
}

fn walk_type_key(collector: &mut MonoItemCollector, type_key: TypeKey) {
    let type_key = collector.map_type_key(type_key);
    let fn_sig = match collector.get_type(type_key) {
        AType::Function(fn_sig) => fn_sig,
        _ => return,
    };

    let (type_key, mut type_mappings) = match collector.ctx.type_monomorphizations.get(&type_key) {
        Some(mono) => (mono.poly_type_key, mono.type_mappings()),
        None => (type_key, HashMap::new()),
    };

    // Check if we need to find and monomorphize the function.
    match fn_sig.maybe_impl_type_key {
        Some(impl_tk) => {
            // Map the impl type key in case it is generic.
            let mapped_impl_tk = collector.map_type_key(impl_tk);

            // Include type mappings from the monomorphization of the impl type, if any.
            let poly_impl_tk = match collector.ctx.type_monomorphizations.get(&mapped_impl_tk) {
                Some(mono) => {
                    for replaced_param in &mono.replaced_params {
                        let replacement_tk =
                            collector.map_type_key(replaced_param.replacement_type_key);
                        type_mappings.insert(replaced_param.param_type_key, replacement_tk);
                        update_type_mappings(collector, replacement_tk, &mut type_mappings);
                    }

                    mono.poly_type_key
                }

                // Maybe the type is a monomorphization of itself with its own params, in which
                // case the monomorphization won't exist, but we still need to include the params
                // in the type mappings.
                None => {
                    if let Some(params) = collector.get_type(mapped_impl_tk).params() {
                        for param in &params.params {
                            type_mappings.insert(
                                param.generic_type_key,
                                collector.map_type_key(param.generic_type_key),
                            );
                        }
                    }

                    mapped_impl_tk
                }
            };

            // Find the actual method on the original type.
            match collector.ctx.get_spec_impl_by_fn(type_key) {
                Some(spec_tk) => {
                    if let Some(fn_tk) = collector.ctx.get_member_fn_from_spec_impl(
                        poly_impl_tk,
                        spec_tk,
                        fn_sig.name.as_str(),
                    ) {
                        collector.queue_item(fn_tk, type_mappings);
                    } else if let Some(fn_tk) = collector.ctx.get_member_fn_from_spec_impl(
                        mapped_impl_tk,
                        spec_tk,
                        &fn_sig.name,
                    ) {
                        collector.queue_item(fn_tk, type_mappings);
                    } else {
                        panic!(
                            "function `{}` should exist on type {poly_impl_tk} for spec {spec_tk}",
                            fn_sig.name,
                        )
                    }
                }

                None => {
                    // Since the function is not part of a spec implementation, we can
                    // search for it as a default member function. If we don't find it,
                    // it means that the function is actually a field on a struct, in which
                    // case there is nothing to queue.
                    let name = fn_sig.name.clone();
                    if let Some(fn_tk) = collector
                        .ctx
                        .get_default_member_fn(poly_impl_tk, name.as_str())
                    {
                        collector.queue_item(fn_tk, type_mappings);
                    } else if let Some(fn_tk) =
                        collector.ctx.get_default_member_fn(mapped_impl_tk, &name)
                    {
                        collector.queue_item(fn_tk, type_mappings);
                    }
                }
            };
        }

        None => {
            // If the type key already refers to an existing function, we're done.
            if collector.fns.contains_key(&type_key) {
                collector.queue_item(type_key, type_mappings);
            } else if collector.extern_fns.contains_key(&type_key) {
                collector.used_extern_fns.insert(fn_sig.type_key);
            }
        }
    }
}

fn update_type_mappings(
    collector: &MonoItemCollector,
    type_key: TypeKey,
    type_mappings: &mut HashMap<TypeKey, TypeKey>,
) {
    if let Some(mono) = collector.ctx.type_monomorphizations.get(&type_key) {
        for replaced_param in &mono.replaced_params {
            let replacement_tk = collector.map_type_key(replaced_param.replacement_type_key);
            if replacement_tk != replaced_param.replacement_type_key
                && !type_mappings.contains_key(&replaced_param.replacement_type_key)
            {
                type_mappings.insert(replaced_param.replacement_type_key, replacement_tk);
            }

            update_type_mappings(collector, replacement_tk, type_mappings);
        }
    }
}
