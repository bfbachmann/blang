use crate::analyzer::ast::func::AFn;
use crate::analyzer::ast::r#type::AType;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::type_store::TypeKey;
use crate::fmt::format_code_vec;
use crate::parser::ast::r#impl::Impl;
use crate::parser::ast::r#type::Type;
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
        // Make sure the `impl` block is not being defined inside a function.
        if ctx.is_in_fn() {
            ctx.insert_err(AnalyzeError::new(
                ErrorKind::InvalidStatement,
                format_code!("cannot declare {} inside function", "impl").as_str(),
                impl_,
            ));

            return AImpl {
                type_key: ctx.unknown_type_key(),
                member_fns: vec![],
            };
        }

        // Get the type key of the type for this impl.
        let type_key = ctx.resolve_maybe_polymorphic_type(&Type::Unresolved(impl_.typ.clone()));
        let parent_tk = ctx.get_poly_type_key(type_key).unwrap_or(type_key);

        // Abort early if the type failed analysis.
        let typ = ctx.must_get_type(type_key);
        if typ.is_unknown() {
            return AImpl {
                type_key: ctx.unknown_type_key(),
                member_fns: vec![],
            };
        }

        // Record an error and return early if the type was not defined in this module.
        if !ctx.type_declared_in_cur_mod(parent_tk) {
            ctx.insert_err(AnalyzeError::new(
                ErrorKind::IllegalImpl,
                format_code!(
                    "cannot define impl for foreign type {}",
                    ctx.display_type(type_key)
                )
                .as_str(),
                &impl_.typ,
            ));

            return AImpl {
                type_key: ctx.unknown_type_key(),
                member_fns: vec![],
            };
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

        // Set the impl type key in the program context so we can use it when resolving type `This`.
        ctx.set_cur_self_type_key(Some(type_key));

        // Analyze member functions.
        let mut member_fns = vec![];
        for mem_fn in &impl_.member_fns {
            let a_fn = AFn::from(ctx, mem_fn);

            // Record public member functions, so we can check whether they're accessible
            // whenever they're used.
            if mem_fn.is_pub {
                ctx.mark_member_fn_pub(type_key, mem_fn.signature.name.as_str());
            }

            member_fns.push(a_fn);
        }

        // Check that this `impl` actually implements all the specs it claims to.
        let mut spec_impl_errs = vec![];
        for spec in &impl_.specs {
            // Find the spec being referred to.
            let a_spec = {
                let spec_type =
                    match ctx.get_type_key_by_type_name(spec.maybe_mod_name.as_ref(), &spec.name) {
                        Some(tk) => match ctx.must_get_type(tk) {
                            AType::Spec(spec_type) => Some(spec_type),
                            _ => None,
                        },
                        _ => None,
                    };

                if spec_type.is_none() {
                    spec_impl_errs.push(AnalyzeError::new(
                        ErrorKind::UndefSpec,
                        format_code!("spec {} is not defined", spec).as_str(),
                        spec,
                    ));
                    continue;
                }

                spec_type.unwrap()
            };

            // Collect the names of all the functions that aren't implemented
            // from this spec.
            let mut missing_fn_names = vec![];
            'next_fn: for fn_type_key in a_spec.member_fn_type_keys.values() {
                let spec_fn_sig = ctx.must_get_type(*fn_type_key).to_fn_sig();
                for member_fn in &member_fns {
                    if member_fn.signature.is_same_as(ctx, &spec_fn_sig) {
                        continue 'next_fn;
                    }
                }

                missing_fn_names.push(spec_fn_sig.name.clone());
            }

            if !missing_fn_names.is_empty() {
                spec_impl_errs.push(
                    AnalyzeError::new(
                        ErrorKind::SpecNotImplemented,
                        format_code!("spec {} not implemented", spec).as_str(),
                        spec,
                    )
                    .with_detail(
                        format!(
                            "Missing adequate implementations for the following \
                            functions from spec {}: {}.",
                            format_code!(spec),
                            format_code_vec(&missing_fn_names, ", "),
                        )
                        .as_str(),
                    ),
                )
            }
        }

        for err in spec_impl_errs {
            ctx.insert_err(err);
        }

        // We can pop the params and the current `Self` type key from the program
        // context now that we're done analyzing this `impl`.
        if has_params {
            ctx.pop_params();
        }

        ctx.set_cur_self_type_key(None);

        AImpl {
            type_key,
            member_fns,
        }
    }
}
