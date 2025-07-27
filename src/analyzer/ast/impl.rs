use std::collections::{HashMap, HashSet};

use crate::analyzer::ast::func::AFn;
use crate::analyzer::ast::r#type::AType;
use crate::analyzer::error::{
    err_expected_spec, err_illegal_foreign_spec_impl, err_illegal_foreign_type_impl,
    err_incorrect_spec_fn, err_invalid_statement, err_non_spec_impl, err_spec_impl_conflict,
    err_spec_impl_missing_fns, AnalyzeError, AnalyzeResult,
};
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::type_store::TypeKey;
use crate::lexer::pos::Span;
use crate::parser::ast::func::Function;
use crate::parser::ast::r#impl::Impl;
use crate::parser::ast::r#type::Type;
use crate::parser::ast::symbol::Symbol;

/// Represents a semantically valid `impl` block that declares member functions for a type.
#[derive(Debug)]
pub struct AImpl {
    pub member_fns: Vec<AFn>,
}

impl AImpl {
    /// Performs semantic analysis on an `impl` block and returns the analyzed
    /// result.
    pub fn from(ctx: &mut ProgramContext, impl_: &Impl) -> AImpl {
        let placeholder = AImpl { member_fns: vec![] };

        // Make sure the `impl` block is not being defined inside a function.
        if ctx.is_in_fn() {
            ctx.insert_err(err_invalid_statement(impl_.span));
            return placeholder;
        }

        // Get the type key of the type for this impl.
        let type_key = ctx.resolve_maybe_polymorphic_type(&Type::Unresolved(impl_.typ.clone()));
        let parent_tk = ctx.get_poly_type_key(type_key).unwrap_or(type_key);

        // Abort early if the type failed analysis.
        let typ = ctx.get_type(type_key);
        if typ.is_unknown() {
            return placeholder;
        }

        // If there are parameters for this impl, push them to the program context
        // so we can resolve them when we're analyzing member functions.
        let has_params = match typ.params() {
            Some(params) => {
                ctx.push_params(params.clone());
                true
            }
            None => false,
        };

        // Set the impl type key in the program context so we can use it when resolving type `Self`.
        ctx.set_cur_self_type_key(Some(type_key));

        // Pops params and unsets the current `Self` type key before returning.
        fn finish(ctx: &mut ProgramContext, has_params: bool, impl_: AImpl) -> AImpl {
            if has_params {
                ctx.pop_params(false);
            }

            ctx.set_cur_self_type_key(None);
            impl_
        }

        // If this block implements a spec, resolve it and track it in the program context while
        // we analyze its functions.
        let maybe_spec_tk = match &impl_.maybe_spec {
            Some(spec) => {
                let spec_tk = ctx.resolve_type(&spec.as_unresolved_type());
                match ctx.get_type(spec_tk) {
                    AType::Spec(_) => {
                        // Return early if the spec impl conflicts with another impl. No point
                        // analyzing it further. No need to record the error here because it would
                        // have already been done in `analyze_impl`.
                        if check_spec_impl_conflicts(
                            ctx,
                            type_key,
                            spec_tk,
                            impl_.header_span(),
                            false,
                        )
                        .is_err()
                        {
                            return finish(ctx, has_params, placeholder);
                        }
                        Some(spec_tk)
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

        // Return early if this is an illegal impl.
        if check_legal_impl(ctx, parent_tk, maybe_spec_tk, impl_).is_err() {
            // No need to record the error here because it would have been recorded in
            // `define_impl`.
            return finish(ctx, has_params, placeholder);
        }

        // Analyze member functions.
        let mut member_fns: HashMap<String, (AFn, &Function)> = HashMap::new();
        for mem_fn in &impl_.member_fns {
            // Locate the already-analyzed function signature.
            let mem_fn_tk = match maybe_spec_tk {
                Some(spec_tk) => ctx
                    .get_member_fn_from_spec_impl(type_key, spec_tk, &mem_fn.signature.name.value)
                    .unwrap(),
                None => ctx
                    .get_default_member_fn(type_key, &mem_fn.signature.name.value)
                    .unwrap(),
            };

            let mem_fn_sig = ctx.get_type(mem_fn_tk).to_fn_sig();
            let a_fn = AFn::from_parts(ctx, mem_fn, mem_fn_sig.clone());
            member_fns.insert(a_fn.signature.name.clone(), (a_fn, mem_fn));
        }

        // Check that this `impl` actually implements the spec it claims to.
        let spec_impl_errs = match maybe_spec_tk {
            Some(spec_tk) => check_spec_impl(
                ctx,
                type_key,
                impl_.maybe_spec.as_ref().unwrap(),
                spec_tk,
                &member_fns,
            ),
            None => vec![],
        };

        for err in spec_impl_errs {
            ctx.insert_err(err);
        }

        finish(
            ctx,
            has_params,
            AImpl {
                member_fns: member_fns.into_values().map(|(func, _)| func).collect(),
            },
        )
    }
}

/// Checks that `member_fns` declared in an impl for the given type properly implement `spec`.
/// Returns errors from failed checks.
fn check_spec_impl(
    ctx: &mut ProgramContext,
    type_key: TypeKey,
    spec: &Symbol,
    spec_tk: TypeKey,
    member_fns: &HashMap<String, (AFn, &Function)>,
) -> Vec<AnalyzeError> {
    // Find the spec being referred to.
    let spec_type = match ctx.get_type(spec_tk) {
        AType::Spec(spec_type) => spec_type.clone(),
        _ => return vec![err_expected_spec(ctx, spec_tk, spec.span)],
    };

    // Collect the names of all the functions that aren't implemented
    // from this spec and check that spec functions were implemented correctly.
    let mut spec_impl_errs = vec![];
    let mut missing_fn_names = vec![];
    let mut extra_fn_names: HashSet<String> = HashSet::from_iter(member_fns.keys().cloned());
    for fn_type_key in spec_type.member_fn_type_keys.values() {
        let spec_fn_sig = ctx.get_type(*fn_type_key).to_fn_sig().clone();

        // Check if this impl has a function with the same name.
        match member_fns.get(spec_fn_sig.name.as_str()) {
            Some((a_fn, raw_fn)) => {
                // Make sure the function was defined correctly.
                if !a_fn.signature.implements(ctx, &spec_fn_sig) {
                    spec_impl_errs.push(err_incorrect_spec_fn(
                        ctx,
                        spec_tk,
                        &spec_fn_sig,
                        raw_fn.signature.span,
                    ));
                }

                // Remove the function name from the set of "extra" functions. Any
                // functions left in the set at the end of this loop should appear in an
                // error because they're not part of the spec.
                extra_fn_names.remove(a_fn.signature.name.as_str());
            }

            None => {
                missing_fn_names.push(spec_fn_sig.name.clone());
            }
        }
    }

    // Record an error if this impl is missing functions defined in the spec.
    if !missing_fn_names.is_empty() {
        spec_impl_errs.push(err_spec_impl_missing_fns(
            &spec.name.value,
            &missing_fn_names,
            spec.name.span,
        ));
    }

    // Record an error for each function in this impl that is not part of the spec.
    for fn_name in extra_fn_names {
        let raw_func = member_fns.get(fn_name.as_str()).unwrap().1;
        spec_impl_errs.push(err_non_spec_impl(
            ctx,
            &spec.name.value,
            &fn_name,
            type_key,
            raw_func.signature.span,
        ));
    }

    spec_impl_errs
}

/// Returns an error if the `impl` block for type `impl_tk` (optionally for spec `maybe_spec_tk`)
/// is illegal. The impl would be considered legal if at least one of the `impl` type and the spec
/// type is defined in the current module.
pub fn check_legal_impl(
    ctx: &mut ProgramContext,
    impl_tk: TypeKey,
    maybe_spec_tk: Option<TypeKey>,
    impl_: &Impl,
) -> AnalyzeResult<()> {
    match maybe_spec_tk {
        Some(spec_tk) => check_legal_spec_impl(ctx, impl_tk, spec_tk, impl_),
        None => {
            if !ctx.type_declared_in_cur_mod(impl_tk) {
                let err = err_illegal_foreign_type_impl(ctx, impl_tk, impl_.typ.span);
                return Err(err);
            }

            Ok(())
        }
    }
}

/// Returns an error if the given spec cannot be implemented for the given type. Spec `S` can be
/// implemented for type `T` only if `S` and/or `T` were defined in the current module. In other
/// words, the `impl` is illegal if both `S` and `T` are foreign types.
fn check_legal_spec_impl(
    ctx: &mut ProgramContext,
    impl_tk: TypeKey,
    spec_tk: TypeKey,
    impl_: &Impl,
) -> AnalyzeResult<()> {
    if !ctx.type_declared_in_cur_mod(impl_tk) {
        let poly_spec_tk = match ctx.type_monomorphizations.get(&spec_tk) {
            Some(mono) => mono.poly_type_key,
            None => spec_tk,
        };

        if !ctx.type_declared_in_cur_mod(poly_spec_tk) {
            let err = err_illegal_foreign_spec_impl(ctx, spec_tk, impl_tk, impl_.typ.span);
            return Err(err);
        }
    }

    Ok(())
}

/// Returns an error if the impl for the given type and spec is illegal (i.e. it conflicts with
/// some other existing spec impl).
pub fn check_spec_impl_conflicts(
    ctx: &mut ProgramContext,
    impl_tk: TypeKey,
    spec_tk: TypeKey,
    spec_span: Span,
    check_self: bool,
) -> AnalyzeResult<()> {
    // Make sure there are no conflicting spec impls for the polymorphic parent
    // type, if one exists.
    if let Some(mono) = ctx.type_monomorphizations.get(&impl_tk) {
        let poly_tk = mono.poly_type_key;
        if let Some(spec_impl) = ctx.get_spec_impl(poly_tk, spec_tk) {
            let header_span = spec_impl.header_span;
            let err = err_spec_impl_conflict(ctx, poly_tk, spec_tk, spec_span, header_span);
            return Err(err);
        }
    }

    if check_self {
        // Make sure there are no conflicting spec impls for this exact type.
        if let Some(spec_impl) = ctx.get_spec_impl(impl_tk, spec_tk) {
            let header_span = spec_impl.header_span;
            let err = err_spec_impl_conflict(ctx, impl_tk, spec_tk, spec_span, header_span);
            return Err(err);
        }
    }

    Ok(())
}
