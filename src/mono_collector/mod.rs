use std::collections::{HashMap, HashSet, VecDeque};
use std::hash::{Hash, Hasher};

use crate::analyzer::analyze::ProgramAnalysis;
use crate::analyzer::ast::expr::{AExpr, AExprKind};
use crate::analyzer::ast::ext::AExternFn;
use crate::analyzer::ast::func::AFn;
use crate::analyzer::ast::r#const::AConst;
use crate::analyzer::ast::r#type::AType;
use crate::analyzer::ast::statement::AStatement;
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::type_store::{GetType, TypeKey};

/// Represents a monomorhic function. This will either be a function that is already
/// monomorphic, or a polymorphic function with type mappings that map its generic parameters
/// to concrete types.  
#[derive(Debug, Eq, Clone)]
pub struct MonoItem {
    /// The type key of the function type (may or may not be polymorphic).
    pub type_key: TypeKey,
    /// The type mappings that map generic function parameter types to their concrete types.
    pub type_mappings: HashMap<TypeKey, TypeKey>,
    /// The index of the parent MonoItem (the function that calls this one).
    pub parent_index: usize,
    /// The indices of the children MonoItems (the functions that this function calls).
    pub child_indices: Vec<usize>,
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

        let mut mappings: Vec<(TypeKey, TypeKey)> =
            self.type_mappings.iter().map(|(k, v)| (*k, *v)).collect();
        mappings.sort_by(|(k1, _), (k2, _)| k1.cmp(k2));
        mappings.hash(state);
    }
}

/// Stores information about the monomorphization tree as we traverse it.
struct MonoItemCollector {
    ctx: ProgramContext,
    /// Maps all function type keys to their declarations.
    fns: HashMap<TypeKey, AFn>,
    /// Maps all extern function type keys to their declarations.
    extern_fns: HashMap<TypeKey, AExternFn>,
    /// Tracks used extern functions.
    used_extern_fns: HashSet<TypeKey>,
    /// Maps all mangled const names to their declarations.
    consts: HashMap<String, AConst>,
    /// A queue of items that still need to be checked and collected for monomorphization.
    incomplete_mono_items: VecDeque<MonoItem>,
    /// A vec of items that have been collected for monomorphization.
    complete_mono_items: Vec<MonoItem>,
    /// Tracks items that have already been queued so we don't re-queue them.
    already_queued_items: HashSet<MonoItem>,
    /// Tracks the index of the mono item that is currently being traversed.
    cur_item_index: usize,
}

impl MonoItemCollector {
    /// Creates a new empty context.
    fn new(ctx: ProgramContext) -> MonoItemCollector {
        // Initialize an empty root mono item.
        let root_item = MonoItem {
            type_key: 0,
            type_mappings: Default::default(),
            parent_index: 0,
            child_indices: vec![],
        };

        MonoItemCollector {
            ctx,
            fns: Default::default(),
            extern_fns: Default::default(),
            used_extern_fns: Default::default(),
            consts: Default::default(),
            incomplete_mono_items: Default::default(),
            cur_item_index: 0,
            already_queued_items: HashSet::from([root_item.clone()]),
            complete_mono_items: vec![root_item],
        }
    }

    /// Gets a type by its type key.
    fn get_type(&self, type_key: TypeKey) -> &AType {
        self.ctx.type_store.get_type(type_key)
    }

    /// Inserts a function into the context, so it can be looked up by its type key later.
    fn insert_fn(&mut self, func: AFn) {
        self.fns.insert(func.signature.type_key, func);
    }

    /// Collects a monomorphic item. All collected items are functions for which we'll generate
    /// machine code.
    fn collect_item(&mut self, item: MonoItem) -> usize {
        // Update the parent item's children with the collected item's index.
        let new_index = self.complete_mono_items.len();
        let parent = self.complete_mono_items.get_mut(item.parent_index).unwrap();
        parent.child_indices.push(new_index);

        // Insert the collected item and return its index.
        self.complete_mono_items.push(item);
        new_index
    }

    /// Queues a function for monomorphization.
    fn queue_item(&mut self, type_key: TypeKey, mut type_mappings: HashMap<TypeKey, TypeKey>) {
        // Update mapped values based on existing mappings in parent contexts.
        for v in type_mappings.values_mut() {
            *v = self.map_type_key(*v);
        }

        // Include type mappings from parent contexts.
        let parent_item = self.complete_mono_items.get(self.cur_item_index).unwrap();
        for (k, v) in &parent_item.type_mappings {
            // Don't overwrite mappings from child contexts.
            if !type_mappings.contains_key(k) {
                type_mappings.insert(*k, *v);
            }
        }

        let item = MonoItem {
            type_key,
            type_mappings,
            parent_index: self.cur_item_index,
            child_indices: vec![],
        };

        // Don't queue the item if it has already been queued or is identical to its parent (a
        // recursive call).
        if !self.already_queued_items.contains(&item) && &item != parent_item {
            self.already_queued_items.insert(item.clone());
            self.incomplete_mono_items.push_back(item);
        }
    }

    /// Pops the item from the front of the queue of functions that need monomorphization.
    fn pop_queued_item(&mut self) -> Option<usize> {
        match self.incomplete_mono_items.pop_front() {
            Some(item) => {
                self.cur_item_index = self.collect_item(item);
                Some(self.cur_item_index)
            }
            None => None,
        }
    }

    /// Maps the given type key to a new type key based on the type mappings in the current
    /// context (i.e. generic parameter mappings for the current function).
    fn map_type_key(&self, type_key: TypeKey) -> TypeKey {
        let item = self.complete_mono_items.get(self.cur_item_index).unwrap();
        if let Some(tk) = item.type_mappings.get(&type_key) {
            return *tk;
        }

        type_key
    }
}

/// Stores information about a monomorphized program.
pub struct MonoProg {
    pub ctx: ProgramContext,
    /// A list of monomorphized functions.
    pub mono_items: Vec<MonoItem>,
    /// Maps function type keys to their implementations.
    pub fns: HashMap<TypeKey, AFn>,
    /// Maps extern function type keys to their signatures.
    pub extern_fns: HashMap<TypeKey, AExternFn>,
    /// Stores consts by name.
    // TODO: Fix name conflicts here.
    pub consts: HashMap<String, AConst>,
    /// Stores the name of the main function, if there is one.
    pub maybe_main_fn_mangled_name: Option<String>,
}

/// Traverses functions in the program call graph, tracking and monomorphizing each one that
/// we need to generate code for. The basic algorithm is as follows:
///     1. Find the roots. If there is a main function (i.e. we're generating an executable
///        program), then it will be the only root. If there isn't one (i.e. we're generating
///        code for a library), then all top-level monomorphic functions are considered roots.
///     2. Push all roots into the queue of un-checked functions.
///     3. While there are functions in the queue, pop the next function from the front of the queue
///        and walk it to discover which functions it uses. For each function we encounter, push it
///        into the queue with its generic parameter type mappings if it hasn't already been checked.
/// This way, we end up building what is essentially a function monomorphization tree that we can
/// traverse during codegen.
pub fn mono_prog(analysis: ProgramAnalysis) -> MonoProg {
    let mut ctx = MonoItemCollector::new(analysis.ctx);

    // Collect all the functions and consts up into a map, so we can look them up easily.
    for module in analysis.analyzed_modules {
        for statement in module.module.fns {
            match statement {
                AStatement::FunctionDeclaration(func) => {
                    track_fn(&mut ctx, &analysis.maybe_main_fn_mangled_name, func);
                }

                AStatement::Impl(impl_) => {
                    for func in impl_.member_fns {
                        track_fn(&mut ctx, &analysis.maybe_main_fn_mangled_name, func);
                    }
                }

                AStatement::ExternFn(extern_fn) => {
                    ctx.extern_fns.insert(extern_fn.fn_sig.type_key, extern_fn);
                }

                AStatement::Const(const_) => {
                    // TODO: There will be naming conflicts here.
                    ctx.consts.insert(const_.name.clone(), const_);
                }

                _ => {}
            }
        }
    }

    // If there is a main function, we'll start traversing from there. Otherwise, we'll just
    // iterate through all the functions.
    while let Some(index) = ctx.pop_queued_item() {
        walk_item(&mut ctx, index);
    }

    // Filter out unused extern functions.
    let extern_fns = ctx
        .extern_fns
        .into_iter()
        .filter(|(tk, _)| ctx.used_extern_fns.contains(tk))
        .collect();

    MonoProg {
        ctx: ctx.ctx,
        mono_items: ctx.complete_mono_items,
        fns: ctx.fns,
        extern_fns,
        consts: ctx.consts,
        maybe_main_fn_mangled_name: analysis.maybe_main_fn_mangled_name,
    }
}

fn track_fn(ctx: &mut MonoItemCollector, maybe_main_fn_mangled_name: &Option<String>, func: AFn) {
    if let Some(main_fn_name) = maybe_main_fn_mangled_name {
        if ctx.incomplete_mono_items.is_empty() && &func.signature.mangled_name == main_fn_name {
            ctx.queue_item(func.signature.type_key, HashMap::new());
        }
    } else {
        let should_queue = match func.signature.maybe_impl_type_key {
            // Don't queue parameterized functions.
            _ if func.signature.is_parameterized() => false,

            // Only queue monomorphic member functions if they're declared on monomorphic types.
            Some(impl_tk) => ctx.get_type(impl_tk).params().is_none(),

            // The function is not parameterized and is not a member function, so we should
            // queue it.
            None => true,
        };

        if should_queue {
            ctx.queue_item(func.signature.type_key, HashMap::new());
        }
    }

    ctx.insert_fn(func);
}

fn walk_item(ctx: &mut MonoItemCollector, index: usize) {
    let item = ctx.complete_mono_items.get(index).unwrap();
    let func = ctx.fns.get(&item.type_key).unwrap();

    for statement in func.body.statements.clone() {
        walk_statement(ctx, statement);
    }
}

fn walk_statement(ctx: &mut MonoItemCollector, statement: AStatement) {
    match statement {
        AStatement::VariableDeclaration(var_decl) => {
            walk_expr(ctx, var_decl.val);
        }

        AStatement::VariableAssignment(var_assign) => {
            walk_expr(ctx, var_assign.val);
            walk_expr(ctx, var_assign.target);
        }

        AStatement::FunctionDeclaration(func) => {
            if !func.signature.is_parameterized() {
                ctx.queue_item(func.signature.type_key, HashMap::new());
            }

            ctx.insert_fn(func.clone());
        }

        AStatement::Closure(closure) => {
            for statement in closure.statements {
                walk_statement(ctx, statement);
            }
        }

        AStatement::FunctionCall(call) => {
            for arg in call.args {
                walk_expr(ctx, arg);
            }

            walk_expr(ctx, call.fn_expr);
        }

        AStatement::Conditional(cond) => {
            for branch in cond.branches {
                if let Some(expr) = branch.cond {
                    walk_expr(ctx, expr);
                }

                for statement in branch.body.statements {
                    walk_statement(ctx, statement);
                }
            }
        }

        AStatement::Loop(loop_) => {
            if let Some(statement) = loop_.maybe_init {
                walk_statement(ctx, statement);
            }

            if let Some(expr) = loop_.maybe_cond {
                walk_expr(ctx, expr);
            }

            for statement in loop_.body.statements {
                walk_statement(ctx, statement);
            }

            if let Some(statement) = loop_.maybe_update {
                walk_statement(ctx, statement);
            }
        }

        // Nothing to do here.
        AStatement::Break
        | AStatement::Continue
        | AStatement::StructTypeDeclaration(_)
        | AStatement::EnumTypeDeclaration(_) => {}

        AStatement::Return(ret) => {
            if let Some(expr) = ret.val {
                walk_expr(ctx, expr);
            }
        }

        AStatement::Yield(yield_) => {
            walk_expr(ctx, yield_.value);
        }

        AStatement::Const(const_) => {
            walk_expr(ctx, const_.value);
        }

        // These statements are impossible in this context.
        AStatement::ExternFn(_) | AStatement::Impl(_) => {
            panic!("unexpected statement {statement}")
        }
    }
}

fn walk_expr(ctx: &mut MonoItemCollector, expr: AExpr) {
    match expr.kind {
        AExprKind::Symbol(sym) => walk_type_key(ctx, sym.type_key),
        AExprKind::MemberAccess(access) => {
            walk_expr(ctx, access.base_expr);
            walk_type_key(ctx, access.member_type_key);
        }
        AExprKind::StructInit(init) => {
            for (_, val) in init.field_values {
                walk_expr(ctx, val);
            }
        }
        AExprKind::EnumInit(init) => {
            if let Some(val) = init.maybe_value {
                walk_expr(ctx, *val);
            }
        }
        AExprKind::TupleInit(init) => {
            for val in init.values {
                walk_expr(ctx, val);
            }
        }
        AExprKind::ArrayInit(init) => {
            for val in init.values {
                walk_expr(ctx, val);
            }
        }
        AExprKind::Index(index) => {
            walk_expr(ctx, index.index_expr);
            walk_expr(ctx, index.collection_expr);
        }
        AExprKind::FunctionCall(call) => {
            for arg in call.args {
                walk_expr(ctx, arg);
            }

            walk_expr(ctx, call.fn_expr);
        }
        AExprKind::AnonFunction(func) => {
            if !func.signature.is_parameterized() {
                ctx.queue_item(func.signature.type_key, HashMap::new());
            }

            ctx.insert_fn(*func.clone());
        }
        AExprKind::UnaryOperation(_, operand) => {
            walk_expr(ctx, *operand);
        }
        AExprKind::BinaryOperation(left, _, right) => {
            walk_expr(ctx, *left);
            walk_expr(ctx, *right);
        }
        AExprKind::TypeCast(expr, _) => {
            walk_expr(ctx, *expr);
        }
        AExprKind::Sizeof(_) => {}
        AExprKind::From(statement) => {
            walk_statement(ctx, *statement);
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
        | AExprKind::StrLiteral(_) => {}

        AExprKind::Unknown => {
            panic!("unknown expression kind")
        }
    }
}

fn walk_type_key(ctx: &mut MonoItemCollector, type_key: TypeKey) {
    let type_key = ctx.map_type_key(type_key);
    let fn_sig = match ctx.get_type(type_key) {
        AType::Function(fn_sig) => fn_sig,
        _ => return,
    };

    let (type_key, mut type_mappings) = match ctx.ctx.type_monomorphizations.get(&type_key) {
        Some(mono) => (mono.poly_type_key, mono.type_mappings()),
        None => (type_key, HashMap::new()),
    };

    // If the type key already refers to an existing function, we're done.
    if ctx.fns.get(&type_key).is_some() {
        ctx.queue_item(type_key, type_mappings);
        return;
    }

    // Check if we need to find and monomorphize the function.
    match fn_sig.maybe_impl_type_key {
        Some(impl_tk) => {
            // Check if the function is a method on a monomorphized type.
            let impl_tk = ctx.map_type_key(impl_tk);
            let impl_tk = match ctx.ctx.type_monomorphizations.get(&impl_tk) {
                Some(mono) => {
                    for replaced_param in &mono.replaced_params {
                        type_mappings.insert(
                            replaced_param.param_type_key,
                            ctx.map_type_key(replaced_param.replacement_type_key),
                        );
                    }

                    mono.poly_type_key
                }
                None => impl_tk,
            };

            // Nothing to do if this is a method on a primitive type (i.e. intrinsic).
            if ctx.get_type(impl_tk).is_primitive() {
                return;
            }

            // Find the actual method on the original type.
            match ctx.ctx.get_spec_impl_by_fn(type_key) {
                Some(spec_tk) => {
                    let fn_tk = ctx
                        .ctx
                        .get_member_fn_from_spec_impl(impl_tk, spec_tk, fn_sig.name.as_str())
                        .expect(
                            format!(
                                "function `{}` should exist on type {impl_tk} for spec {spec_tk}",
                                fn_sig.name
                            )
                            .as_str(),
                        );
                    ctx.queue_item(fn_tk, type_mappings);
                }
                None => {
                    // Since the function is not part of a spec implementation, we can
                    // search for it as a default member function. If we don't find it,
                    // it means that the function is actually a field on a struct, in which
                    // case there is nothing to queue.
                    if let Some(fn_tk) =
                        ctx.ctx.get_default_member_fn(impl_tk, fn_sig.name.as_str())
                    {
                        ctx.queue_item(fn_tk, type_mappings);
                    }
                }
            };
        }

        None => {
            // This will be the case for extern functions. We'll track them separately.
            ctx.used_extern_fns.insert(fn_sig.type_key);
        }
    }
}
