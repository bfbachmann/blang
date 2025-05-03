use crate::analyzer::ast::ext::AExternFn;
use crate::analyzer::ast::func::{AFn, AFnSig};
use crate::analyzer::ast::r#const::AConst;
use crate::analyzer::ast::r#enum::AEnumType;
use crate::analyzer::ast::r#impl::{is_legal_impl, AImpl};
use crate::analyzer::ast::r#struct::AStructType;
use crate::analyzer::ast::r#type::AType;
use crate::analyzer::ast::spec::ASpecType;
use crate::analyzer::error::{
    err_dup_ident, err_dup_impl_fn, err_dup_import_alias, err_dup_imported_mod, err_dup_mem_fn,
    err_expected_spec, err_invalid_mod_path, err_invalid_statement, err_not_pub,
    err_type_already_implements_spec, err_undef_foreign_symbol,
};
use crate::analyzer::ident::{Ident, IdentKind, ModAlias, Usage};
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::type_containment::{check_enum_containment, check_struct_containment};
use crate::analyzer::warn::{warn_unused, AnalyzeWarning};
use crate::lexer::pos::Locatable;
use crate::parser::ast::r#impl::Impl;
use crate::parser::ast::r#type::Type;
use crate::parser::ast::statement::Statement;
use crate::parser::src_file::SrcFile;
use crate::parser::{ModID, SrcInfo};
use std::collections::{HashMap, HashSet};

/// Represents a semantically analyzed source file.
#[derive(Debug)]
pub struct AModule {
    pub fns: Vec<AFn>,
    pub impls: Vec<AImpl>,
    pub extern_fns: Vec<AExternFn>,
}

impl AModule {
    pub fn new_empty() -> AModule {
        AModule {
            fns: vec![],
            impls: vec![],
            extern_fns: vec![],
        }
    }

    /// Performs semantic analysis on the given module and returns a type-rich version of it.
    pub fn from(ctx: &mut ProgramContext, mod_id: ModID, src_info: &SrcInfo) -> AModule {
        ctx.set_cur_mod_id(mod_id);
        let src_files = src_info.get_src_files(mod_id);

        // First pass: define identifiers in the module without analyzing their values yet.
        for src_file in &src_files {
            ctx.set_cur_file_id(src_file.id);
            define_imported_idents(ctx, src_file, src_info);
            define_local_idents(ctx, src_file);
        }

        // Second pass: define `impl` blocks so we know what types implement which methods.
        for src_file in &src_files {
            ctx.set_cur_file_id(src_file.id);

            for statement in &src_file.statements {
                if let Statement::Impl(impl_) = statement {
                    define_impl(ctx, impl_);
                }
            }
        }

        let mut invalid_statement_spans = vec![];

        // Third pass: fully analyze all program statements.
        for src_file in src_files {
            ctx.set_cur_file_id(src_file.id);

            for statement in &src_file.statements {
                match statement {
                    Statement::FunctionDeclaration(func) => {
                        if let Some(ident) =
                            ctx.remove_unchecked_ident_from_cur_scope(&func.signature.name)
                        {
                            let a_fn = AFn::from(ctx, ident.kind.as_unchecked_fn());
                            ctx.insert_analyzed_fn(a_fn);
                        }
                    }

                    Statement::ExternFn(extern_fn) => {
                        if let Some(ident) =
                            ctx.remove_unchecked_ident_from_cur_scope(&extern_fn.signature.name)
                        {
                            let ext_fn = AExternFn::from(ctx, ident.kind.as_unchecked_extern_fn());
                            ctx.insert_analyzed_extern_fn(ext_fn);
                        }
                    }

                    Statement::ConstDeclaration(const_) => {
                        if let Some(ident) = ctx.remove_unchecked_ident_from_cur_scope(&const_.name)
                        {
                            AConst::from(ctx, ident.kind.as_unchecked_const());
                        }
                    }

                    Statement::StructDeclaration(struct_type) => {
                        if let Some(ident) =
                            ctx.remove_unchecked_ident_from_cur_scope(&struct_type.name)
                        {
                            AStructType::from(ctx, ident.kind.as_unchecked_struct_type());
                        }
                    }

                    Statement::EnumDeclaration(enum_type) => {
                        if let Some(ident) =
                            ctx.remove_unchecked_ident_from_cur_scope(&enum_type.name)
                        {
                            AEnumType::from(ctx, ident.kind.as_unchecked_enum_type());
                        }
                    }

                    Statement::SpecDeclaration(spec_type) => {
                        if let Some(ident) =
                            ctx.remove_unchecked_ident_from_cur_scope(&spec_type.name)
                        {
                            ASpecType::from(ctx, ident.kind.as_unchecked_spec_type());
                        }
                    }

                    Statement::Impl(impl_) => {
                        let a_impl = AImpl::from(ctx, impl_);
                        ctx.insert_analyzed_impl(a_impl);
                    }

                    Statement::Use(_) => {}

                    other => {
                        invalid_statement_spans.push(*other.span());
                    }
                }
            }
        }

        for span in invalid_statement_spans {
            ctx.insert_err(err_invalid_statement(span));
        }

        // Warn about unused top-level idents.
        let scope = ctx.cur_scope();
        let warns: Vec<AnalyzeWarning> = scope
            .unused_top_level_idents()
            .iter()
            .map(|ident| warn_unused(&ident.name, ident.span))
            .collect();
        for warn in warns {
            ctx.insert_warn(warn);
        }

        // Warn about unused imports.
        let (unused_idents, unused_aliases) = ctx.unused_imports();
        let mut warns: Vec<AnalyzeWarning> = unused_idents
            .into_iter()
            .map(|ident| warn_unused(&ident.name, ident.span))
            .collect();

        warns.extend(
            unused_aliases
                .into_iter()
                .map(|alias| warn_unused(&alias.name, alias.span)),
        );

        for warn in warns {
            ctx.insert_warn(warn);
        }

        let (fns, impls, extern_fns) = ctx.drain_fns();

        AModule {
            fns,
            impls,
            extern_fns,
        }
    }
}

fn define_imported_idents(ctx: &mut ProgramContext, src_file: &SrcFile, src_info: &SrcInfo) {
    let mut imported_mod_ids = HashMap::new();

    for used_mod in &src_file.used_mods {
        let target_mod_id = match src_info.mod_info.get_id_by_path(&used_mod.path.raw) {
            Some(mod_id) => mod_id,
            None => {
                ctx.insert_err(err_invalid_mod_path(&used_mod.path.raw, used_mod.path.span));
                continue;
            }
        };

        // Record an error if this module was already imported.
        if let Some(existing_span) = imported_mod_ids.insert(target_mod_id, used_mod.path.span) {
            ctx.insert_err(err_dup_imported_mod(used_mod, existing_span));
        }

        if let Some(alias) = &used_mod.maybe_alias {
            if let Err(existing) = ctx.insert_mod_alias(ModAlias::new(
                alias.to_owned(),
                target_mod_id,
                used_mod.span, // TODO: use name span
            )) {
                // TODO: use name span
                let err = err_dup_import_alias(alias, used_mod.span, existing.span);
                ctx.insert_err(err);
            }
        }

        for symbol in &used_mod.symbols {
            match ctx.get_foreign_ident(target_mod_id, &symbol.name) {
                Some(ident) => {
                    let mut ident = ident.clone();

                    let is_pub = match &ident.kind {
                        IdentKind::Type { is_pub, .. } => *is_pub,
                        IdentKind::Fn { is_pub, .. } => *is_pub,
                        IdentKind::ExternFn { is_pub, .. } => *is_pub,
                        IdentKind::Const { is_pub, .. } => *is_pub,
                        other => panic!("unexpected ident kind {other:?}"),
                    };

                    if !is_pub {
                        ctx.insert_err(err_not_pub(&symbol.name, symbol.span));
                    }

                    ident.span = symbol.span;
                    ident.usage = Usage::Unused;

                    if let Err(existing) = ctx.insert_imported_ident(ident) {
                        let err = err_dup_ident(&symbol.name, symbol.span, existing.span);
                        ctx.insert_err(err);
                    }
                }

                None => {
                    let mod_path = &src_info.mod_info.get_by_id(target_mod_id).path;
                    ctx.insert_err(err_undef_foreign_symbol(
                        &symbol.name,
                        mod_path,
                        symbol.span,
                    ));
                }
            }
        }
    }
}

fn define_local_idents(ctx: &mut ProgramContext, src_file: &SrcFile) {
    // First pass: just insert symbols with un-analyzed values. We'll analyze them later.
    let mut containment_check_names = vec![];

    for statement in &src_file.statements {
        match statement {
            Statement::StructDeclaration(struct_type) => {
                if let Err(existing) =
                    ctx.insert_ident(Ident::new_unchecked_struct_type(struct_type.clone()))
                {
                    let err = err_dup_ident(&struct_type.name, struct_type.span, existing.span);
                    ctx.insert_err(err);
                } else {
                    containment_check_names.push(&struct_type.name);
                }
            }

            Statement::EnumDeclaration(enum_type) => {
                if let Err(existing) =
                    ctx.insert_ident(Ident::new_unchecked_enum_type(enum_type.clone()))
                {
                    let err = err_dup_ident(&enum_type.name, enum_type.span, existing.span);
                    ctx.insert_err(err);
                } else {
                    containment_check_names.push(&enum_type.name);
                }
            }

            Statement::SpecDeclaration(spec_type) => {
                if let Err(existing) =
                    ctx.insert_ident(Ident::new_unchecked_spec_type(spec_type.clone()))
                {
                    let err = err_dup_ident(&spec_type.name, spec_type.span, existing.span);
                    ctx.insert_err(err);
                }
            }

            Statement::ConstDeclaration(const_) => {
                if let Err(existing) = ctx.insert_ident(Ident::new_unchecked_const(const_.clone()))
                {
                    let err = err_dup_ident(&const_.name, const_.span, existing.span);
                    ctx.insert_err(err);
                }
            }

            Statement::FunctionDeclaration(func) => {
                if let Err(existing) = ctx.insert_ident(Ident::new_unchecked_fn(func.clone())) {
                    let err =
                        err_dup_ident(&func.signature.name, func.signature.span, existing.span);
                    ctx.insert_err(err);
                };
            }

            Statement::ExternFn(func) => {
                if let Err(existing) =
                    ctx.insert_ident(Ident::new_unchecked_extern_fn(func.clone()))
                {
                    let err =
                        err_dup_ident(&func.signature.name, func.signature.span, existing.span);
                    ctx.insert_err(err);
                };
            }

            Statement::Impl(impl_) => {
                ctx.insert_unchecked_impl(impl_.typ.clone(), impl_.maybe_spec.clone())
            }

            _ => {}
        };
    }

    // Second pass: Check for type containment cycles. Any types with containment cycles will have
    // their identifiers mapped to the `<unknown>` type.
    for name in containment_check_names {
        let ident = ctx.get_ident_in_cur_scope(name).unwrap();
        let result = match &ident.kind {
            IdentKind::UncheckedStructType(struct_type) => {
                check_struct_containment(ctx, struct_type, &mut vec![])
            }

            IdentKind::UncheckedEnumType(enum_type) => {
                check_enum_containment(ctx, enum_type, &mut vec![])
            }

            _ => unreachable!(),
        };

        if let Err(err) = result {
            ctx.insert_err(err);

            let unknown_tk = ctx.unknown_type_key();
            let cur_mod_id = ctx.cur_mod_id();
            let ident = ctx.get_ident_in_cur_scope_mut(name).unwrap();
            ident.kind = IdentKind::Type {
                type_key: unknown_tk,
                is_pub: false,
                mod_id: Some(cur_mod_id),
            };
        }
    }
}

fn define_impl(ctx: &mut ProgramContext, impl_: &Impl) {
    // Set the current impl type key on the program context so we can access it when
    // resolving type `Self`.
    let impl_type_key = ctx.resolve_maybe_polymorphic_type(&Type::Unresolved(impl_.typ.clone()));

    // If there are parameters for this impl, push them to the program context
    // so we can resolve them when we're analyzing member functions.
    let typ = ctx.get_type(impl_type_key);
    let has_params = match typ.params() {
        Some(params) => {
            ctx.push_params(params.clone());
            true
        }
        None => false,
    };

    // Check if this is an implementation of a spec. If so, try to resolve the spec and track
    // its type key in the program context while we analyze its functions.
    let is_default_impl = impl_.maybe_spec.is_none();
    let maybe_spec_tk = match &impl_.maybe_spec {
        Some(spec) => {
            // Try to find the analyzed spec type. It might not be there if it has not
            // yet been analyzed.
            let spec_tk = ctx.resolve_type(&spec.as_unresolved_type());
            let spec_type = ctx.get_type(spec_tk);
            match spec_type {
                AType::Spec(_) => {
                    // Make sure there isn't already an impl defined for this spec on this type.
                    if ctx.type_has_spec_impl(impl_type_key, spec_tk) {
                        let err = err_type_already_implements_spec(
                            ctx,
                            impl_type_key,
                            spec_tk,
                            spec.span,
                        );
                        ctx.insert_err(err);
                        None
                    } else {
                        Some(spec_tk)
                    }
                }

                AType::Unknown(_) => None,

                _ => {
                    let err = err_expected_spec(ctx, spec_tk, spec.span);
                    ctx.insert_err(err);
                    None
                }
            }
        }

        None => None,
    };

    // Skip the impl if it's illegal.
    if !is_legal_impl(ctx, impl_type_key, maybe_spec_tk) {
        return;
    }

    // Check if the spec being implemented is public.
    let is_pub_spec = maybe_spec_tk.is_some_and(|tk| ctx.type_is_pub(tk));

    ctx.set_cur_self_type_key(Some(impl_type_key));

    // Analyze each member function signature.
    let mut fn_type_keys = HashMap::new();
    let mut pub_fn_tks = HashSet::new();
    for member_fn in &impl_.member_fns {
        let fn_sig = AFnSig::from(ctx, &member_fn.signature);

        // Make sure there are no other functions in this impl block that share the same name.
        if fn_type_keys.contains_key(fn_sig.name.as_str()) {
            let err = err_dup_impl_fn(&member_fn.signature.name, member_fn.signature.span);
            ctx.insert_err(err);

            // Skip invalid func.
            continue;
        }

        // If this is a default impl (i.e. it's not implementing a spec), then we need to
        // make sure that function names don't collide with those of existing functions from
        // other default impls on this type.
        if is_default_impl {
            let has_matching_default_fn = ctx
                .get_default_member_fn(impl_type_key, fn_sig.name.as_str())
                .is_some();
            if has_matching_default_fn {
                let err =
                    err_dup_mem_fn(ctx, &fn_sig.name, impl_type_key, member_fn.signature.span);
                ctx.insert_err(err);

                // Skip invalid func.
                continue;
            }
        }

        fn_type_keys.insert(fn_sig.name.clone(), fn_sig.type_key);

        // Mark the member function as pub if necessary.
        if member_fn.is_pub || is_pub_spec {
            pub_fn_tks.insert(fn_sig.type_key);
        }
    }

    ctx.set_cur_self_type_key(None);

    if has_params {
        ctx.pop_params(false);
    }

    // Regardless of errors, we'll mark this `impl` as implementing the
    // spec it claims it does. This is just to prevent redundant error
    // messages when the corresponding type gets used.
    ctx.insert_impl(impl_type_key, maybe_spec_tk, fn_type_keys);

    // Record public member functions, so we can check whether they're accessible
    // whenever they're used. We'll also consider the member function public if
    // it is an implementation of a function from a public spec.
    for fn_tk in pub_fn_tks {
        ctx.mark_member_fn_pub(impl_type_key, fn_tk);
    }
}
