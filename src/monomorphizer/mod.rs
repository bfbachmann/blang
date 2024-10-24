use std::collections::{HashMap, HashSet, VecDeque};
use std::hash::{Hash, Hasher};

use crate::analyzer::analyze::ProgramAnalysis;
use crate::analyzer::ast::expr::{AExpr, AExprKind};
use crate::analyzer::ast::func::AFn;
use crate::analyzer::ast::r#const::AConst;
use crate::analyzer::ast::r#type::AType;
use crate::analyzer::ast::statement::AStatement;
use crate::analyzer::mangling;
use crate::analyzer::prog_context::Monomorphization;
use crate::analyzer::type_store::{TypeKey, TypeStore};

#[derive(Debug, PartialEq, Eq, Clone)]
struct MonoItem {
    type_key: TypeKey,
    type_mappings: HashMap<TypeKey, TypeKey>,
    parent_index: usize,
    child_indices: Vec<usize>,
}

impl Hash for MonoItem {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.type_key.hash(state);
        self.parent_index.hash(state);

        let mut mappings: Vec<(TypeKey, TypeKey)> =
            self.type_mappings.iter().map(|(k, v)| (*k, *v)).collect();
        mappings.sort_by(|(k1, _), (k2, _)| k1.cmp(k2));
        mappings.hash(state);
    }
}

struct MonoCtx {
    /// Holds information about all types in the program.
    type_store: TypeStore,
    /// Maps all function type keys to their declarations.
    fns: HashMap<TypeKey, AFn>,
    /// Maps mangled function names to their type keys.
    fns_by_mangled_name: HashMap<String, TypeKey>,
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
    /// Maps monomorphic type keys to the monomorphizations that were used to derive them.
    type_monomorphizations: HashMap<TypeKey, Monomorphization>,
}

impl MonoCtx {
    fn new(
        type_store: TypeStore,
        type_monomorphizations: HashMap<TypeKey, Monomorphization>,
    ) -> MonoCtx {
        // Initialize an empty root mono item.
        let root_item = MonoItem {
            type_key: 0,
            type_mappings: Default::default(),
            parent_index: 0,
            child_indices: vec![],
        };

        MonoCtx {
            type_store,
            fns: Default::default(),
            fns_by_mangled_name: Default::default(),
            consts: Default::default(),
            incomplete_mono_items: Default::default(),
            cur_item_index: 0,
            type_monomorphizations,
            already_queued_items: HashSet::from([root_item.clone()]),
            complete_mono_items: vec![root_item],
        }
    }

    fn insert_fn(&mut self, func: AFn) {
        self.fns_by_mangled_name
            .insert(func.signature.mangled_name.clone(), func.signature.type_key);
        self.fns.insert(func.signature.type_key, func);
    }

    fn get_fn_type_key_by_mangled_name(&mut self, name: &str) -> Option<TypeKey> {
        self.fns_by_mangled_name.get(name).cloned()
    }

    fn collect_item(&mut self, item: MonoItem) -> usize {
        // Update the parent item's children with the collected item's index.
        let new_index = self.complete_mono_items.len();
        let parent = self.complete_mono_items.get_mut(item.parent_index).unwrap();
        parent.child_indices.push(new_index);

        // Insert the collected item and return its index.
        self.complete_mono_items.push(item);
        new_index
    }

    fn queue_item(&mut self, type_key: TypeKey, mut type_mappings: HashMap<TypeKey, TypeKey>) {
        println!("queueing {type_key}");
        let item = MonoItem {
            type_key,
            type_mappings,
            parent_index: self.cur_item_index,
            child_indices: vec![],
        };

        if !self.already_queued_items.contains(&item) {
            self.incomplete_mono_items.push_back(item);
        }
    }

    fn pop_queued_item(&mut self) -> Option<usize> {
        match self.incomplete_mono_items.pop_front() {
            Some(item) => {
                self.cur_item_index = self.collect_item(item);
                Some(self.cur_item_index)
            }
            None => None,
        }
    }

    fn map_type_key(&self, type_key: TypeKey) -> TypeKey {
        let mut index = self.cur_item_index;
        while index != 0 {
            let item = self.complete_mono_items.get(index).unwrap();
            match item.type_mappings.get(&type_key) {
                Some(tk) => return *tk,
                None => {
                    index = item.parent_index;
                }
            }
        }

        type_key
    }
}

pub struct MonoProg {
    pub type_store: TypeStore,
    pub fns: HashMap<TypeKey, AFn>,
    pub monomorphized_types: HashMap<TypeKey, HashSet<Monomorphization>>,
    pub type_monomorphizations: HashMap<TypeKey, Monomorphization>,
    pub maybe_main_fn_mangled_name: Option<String>,
}

pub fn mono_prog(analysis: ProgramAnalysis) -> MonoProg {
    let mut ctx = MonoCtx::new(analysis.type_store, analysis.type_monomorphizations);

    // Collect all the functions and consts up into a map, so we can look them up easily.
    for module in analysis.analyzed_modules {
        for statement in module.module.statements {
            match statement {
                AStatement::FunctionDeclaration(func) => {
                    track_fn(&mut ctx, &analysis.maybe_main_fn_mangled_name, func);
                }

                AStatement::Impl(impl_) => {
                    for func in impl_.member_fns {
                        track_fn(&mut ctx, &analysis.maybe_main_fn_mangled_name, func);
                    }
                }

                AStatement::Const(const_) => {
                    // TODO: Not sure the mangling here makes any sense.
                    ctx.consts
                        .insert(format!("{}::{}", module.module.path, const_.name), const_);
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

    MonoProg {
        type_store: ctx.type_store,
        fns: ctx.fns,
        monomorphized_types: analysis.monomorphized_types,
        type_monomorphizations: ctx.type_monomorphizations,
        maybe_main_fn_mangled_name: analysis.maybe_main_fn_mangled_name,
    }
}

fn track_fn(ctx: &mut MonoCtx, maybe_main_fn_mangled_name: &Option<String>, func: AFn) {
    if let Some(main_fn_name) = maybe_main_fn_mangled_name {
        if &func.signature.mangled_name == main_fn_name {
            ctx.queue_item(func.signature.type_key, HashMap::new());
        }
    } else {
        let should_queue = match func.signature.maybe_impl_type_key {
            // Don't queue parameterized functions.
            _ if func.signature.is_parameterized() => false,

            // Only queue monomorphic member functions if they're declared on monomorphic types.
            Some(impl_tk) => ctx.type_store.must_get(impl_tk).params().is_none(),

            // The function is not parameterized and is not a member function, so we should
            // queue it.
            None => true,
        };

        if should_queue {
            ctx.queue_item(func.signature.type_key, HashMap::new());
        }
    }

    println!("inserting {}: {func}", func.signature.type_key);
    ctx.insert_fn(func);
}

fn walk_item(ctx: &mut MonoCtx, index: usize) {
    let item = ctx.complete_mono_items.get(index).unwrap();
    let typ = ctx.type_store.must_get(item.type_key);
    match typ {
        AType::Function(_) => {
            let func = match ctx.fns.get(&item.type_key) {
                Some(func) => func,
                None => {
                    // It's just a function type, not an actual function.
                    todo!()
                }
            };

            println!("walking {}: {func}", item.type_key);
            for statement in func.body.statements.clone() {
                walk_statement(ctx, statement);
            }
        }

        AType::Struct(_) => {
            todo!()
        }
        AType::Enum(_) => {
            todo!()
        }
        AType::Tuple(_) => {
            todo!()
        }
        AType::Array(_) => {
            todo!()
        }
        AType::Pointer(_) => {
            todo!()
        }

        // These types are already monomorphic.
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
        | AType::Str => {}

        AType::Spec(s) => {
            panic!("unexpected spec type {s}")
        }

        AType::Generic(g) => {
            panic!("unexpected generic type {g}")
        }

        AType::Unknown(name) => {
            panic!("found unknown type {name}")
        }
    }
}

fn walk_statement(ctx: &mut MonoCtx, statement: AStatement) {
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

            println!("inserting {}: {func}", func.signature.type_key);
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

fn walk_expr(ctx: &mut MonoCtx, expr: AExpr) {
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

            println!("inserting {}: {func}", func.signature.type_key);
            ctx.insert_fn(*func.clone());
        }
        AExprKind::UnaryOperation(_, operand) => {
            walk_expr(ctx, *operand);
        }
        AExprKind::BinaryOperation(left, _, right) => {
            walk_expr(ctx, *left);
            walk_expr(ctx, *right);
        }
        AExprKind::TypeCast(_, _) => {}
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

fn walk_type_key(ctx: &mut MonoCtx, type_key: TypeKey) {
    let type_key = ctx.map_type_key(type_key);
    let fn_sig = match ctx.type_store.must_get(type_key) {
        AType::Function(fn_sig) => fn_sig,
        _ => return,
    };

    let (type_key, type_mappings) = match ctx.type_monomorphizations.get(&type_key) {
        Some(mono) => (mono.poly_type_key, mono.type_mappings()),
        None => (type_key, HashMap::new()),
    };

    // If the type key already refers to an existing function, we're done.
    if ctx.fns.get(&type_key).is_some() {
        ctx.queue_item(type_key, type_mappings);
        return;
    }

    // We need to find and monomorphize the function.
    match fn_sig.maybe_impl_type_key {
        Some(impl_tk) => {
            let mono_impl_tk = ctx.map_type_key(impl_tk);
            let concrete_fn_name = mangling::remangle_name(
                &ctx.type_store,
                fn_sig.mangled_name.as_str(),
                mono_impl_tk,
            );

            if let Some(concrete_fn_tk) = ctx.get_fn_type_key_by_mangled_name(&concrete_fn_name) {
                ctx.queue_item(concrete_fn_tk, type_mappings);
            }
        }

        None => {
            // Nothing to do at this point because the function is just a type - it has no body.
            // This will be the case for extern functions.
        }
    }
}
