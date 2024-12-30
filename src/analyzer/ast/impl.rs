use std::collections::{HashMap, HashSet};

use crate::analyzer::ast::func::AFn;
use crate::analyzer::ast::r#type::AType;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::type_store::TypeKey;
use crate::fmt::format_code_vec;
use crate::parser::ast::func::Function;
use crate::parser::ast::r#impl::Impl;
use crate::parser::ast::r#type::Type;
use crate::parser::ast::symbol::Symbol;
use crate::{format_code, util};

/// Represents a semantically valid `impl` block that declares member functions for a type.
#[derive(Debug, Clone)]
pub struct AImpl {
    pub type_key: TypeKey,
    pub member_fns: Vec<AFn>,
}

impl PartialEq for AImpl {
    fn eq(&self, other: &Self) -> bool {
        self.type_key == other.type_key && util::vecs_eq(&self.member_fns, &other.member_fns)
    }
}

impl AImpl {
    /// Performs semantic analysis on an `impl` block and returns the analyzed
    /// result.
    pub fn from(ctx: &mut ProgramContext, impl_: &Impl) -> AImpl {
        let placeholder = AImpl {
            type_key: ctx.unknown_type_key(),
            member_fns: vec![],
        };

        // Make sure the `impl` block is not being defined inside a function.
        if ctx.is_in_fn() {
            ctx.insert_err(AnalyzeError::new(
                ErrorKind::InvalidStatement,
                format_code!("cannot declare {} inside function", "impl").as_str(),
                impl_,
            ));

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

        // If this block implements a spec, resolve it and track it in the program context while
        // we analyze its functions.
        let maybe_spec_tk = match &impl_.maybe_spec {
            Some(spec) => {
                let spec_tk = ctx.resolve_type(&spec.as_unresolved_type());
                match ctx.get_type(spec_tk) {
                    AType::Spec(_) => {
                        ctx.set_cur_spec_type_key(Some(spec_tk));
                        Some(spec_tk)
                    }

                    AType::Unknown(_) => None,

                    _ => {
                        ctx.insert_err(AnalyzeError::new(
                            ErrorKind::ExpectedSpec,
                            format_code!(
                                "type {} is not a spec",
                                ctx.display_type(spec_tk).as_str()
                            )
                            .as_str(),
                            spec,
                        ));

                        None
                    }
                }
            }

            None => None,
        };

        // Record an error and return early if the type was not defined in this module.
        match maybe_spec_tk {
            Some(spec_tk) => {
                if !is_legal_spec_impl(ctx, parent_tk, spec_tk) {
                    ctx.insert_err(
                        AnalyzeError::new(
                            ErrorKind::IllegalImpl,
                            format_code!(
                                "cannot implement foreign spec {} for foreign type {}",
                                ctx.display_type(spec_tk),
                                ctx.display_type(type_key)
                            )
                            .as_str(),
                            &impl_.typ,
                        )
                        .with_detail(
                            "Either the type or the spec being implemented must be \
                                defined in this module.",
                        ),
                    );

                    return placeholder;
                }
            }

            None => {
                if !is_legal_impl(ctx, parent_tk, None) {
                    ctx.insert_err(AnalyzeError::new(
                        ErrorKind::IllegalImpl,
                        format_code!(
                            "cannot define {} for foreign type {}",
                            "impl",
                            ctx.display_type(type_key)
                        )
                        .as_str(),
                        &impl_.typ,
                    ));

                    return placeholder;
                }
            }
        }

        // Analyze member functions.
        let mut member_fns: HashMap<String, (AFn, &Function)> = HashMap::new();
        for mem_fn in &impl_.member_fns {
            let a_fn = AFn::from(ctx, mem_fn);
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

        // We can pop the params and the current `Self` type key from the program
        // context now that we're done analyzing this `impl`.
        if has_params {
            ctx.pop_params();
        }

        ctx.set_cur_spec_type_key(None);
        ctx.set_cur_self_type_key(None);

        AImpl {
            type_key,
            member_fns: member_fns.into_values().map(|(func, _)| func).collect(),
        }
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
        _ => {
            return vec![AnalyzeError::new(
                ErrorKind::ExpectedSpec,
                format_code!("{} is not a spec", ctx.display_type(spec_tk)).as_str(),
                spec,
            )]
        }
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
                    spec_impl_errs.push(
                        AnalyzeError::new(
                            ErrorKind::IncorrectSpecFnInImpl,
                            format_code!(
                                "function {} not implemented according to spec {}",
                                a_fn.signature.name,
                                spec.name
                            )
                            .as_str(),
                            &raw_fn.signature,
                        )
                        .with_detail(
                            format_code!(
                                "Spec {} defines the function as {}.",
                                ctx.display_type(spec_tk),
                                spec_fn_sig.display(ctx),
                            )
                            .as_str(),
                        ),
                    );
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
        spec_impl_errs.push(
            AnalyzeError::new(
                ErrorKind::SpecImplMissingFns,
                format_code!("spec {} not fully implemented", spec.name).as_str(),
                spec,
            )
            .with_detail(
                format!(
                    "The following functions from spec {} are missing: {}.",
                    format_code!(spec),
                    format_code_vec(&missing_fn_names, ", "),
                )
                .as_str(),
            ),
        );
    }

    // Record an error for each function in this impl that is not part of the spec.
    for fn_name in extra_fn_names {
        let raw_func = member_fns.get(fn_name.as_str()).unwrap().1;

        spec_impl_errs.push(
            AnalyzeError::new(
                ErrorKind::NonSpecFnInImpl,
                format_code!("function {} is not defined in spec {}", fn_name, spec.name).as_str(),
                &raw_func.signature,
            )
            .with_detail(
                format_code!(
                    "Spec {} does not contain a function named {}, so it should not appear \
                            in this {} block.",
                    spec.name,
                    fn_name,
                    "impl",
                )
                .as_str(),
            )
            .with_help(
                format_code!(
                    "Consider moving function {} to a default {} block.",
                    fn_name,
                    format!("impl {}", ctx.display_type(type_key))
                )
                .as_str(),
            ),
        );
    }

    spec_impl_errs
}

/// Returns whether the `impl` block for type `impl_tk` (optionally for spec `maybe_spec_tk`) is
/// legal. The impl would be considered legal if any of the following are true
/// - `maybe_spec_tk` is `None` (i.e. it's a default `impl`), and `impl_tk` refers to a local type
/// - neither the impl type or the spec type are foreign.
pub fn is_legal_impl(
    ctx: &mut ProgramContext,
    impl_tk: TypeKey,
    maybe_spec_tk: Option<TypeKey>,
) -> bool {
    match maybe_spec_tk {
        Some(spec_tk) => is_legal_spec_impl(ctx, impl_tk, spec_tk),
        None => ctx.type_declared_in_cur_mod(impl_tk),
    }
}

/// Returns whether the given spec can be implemented for the given type. Spec `S` can be
/// implemented for type `T` only if `S` and/or `T` were defined in the current module. In other
/// words, the `impl` is illegal if both `S` and `T` are foreign types.
pub fn is_legal_spec_impl(ctx: &mut ProgramContext, impl_tk: TypeKey, spec_tk: TypeKey) -> bool {
    if !ctx.type_declared_in_cur_mod(impl_tk) {
        let poly_spec_tk = match ctx.type_monomorphizations.get(&spec_tk) {
            Some(mono) => mono.poly_type_key,
            None => spec_tk,
        };

        if !ctx.type_declared_in_cur_mod(poly_spec_tk) {
            return false;
        }
    }

    true
}
