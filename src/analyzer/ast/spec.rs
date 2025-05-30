use std::collections::HashMap;
use std::fmt::{Display, Formatter};

use crate::analyzer::ast::func::AFnSig;
use crate::analyzer::ast::params::AParams;
use crate::analyzer::ast::r#type::AType;
use crate::analyzer::error::err_dup_ident;
use crate::analyzer::ident::Ident;
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::type_store::TypeKey;
use crate::lexer::pos::Span;
use crate::parser::ast::spec::SpecType;

/// Represents a set of functions that are associated with a type (i.e. a set
/// of things one can do with a type).
#[derive(PartialEq, Clone, Debug)]
pub struct ASpecType {
    pub name: String,
    pub maybe_params: Option<AParams>,
    /// Maps member function name to the function type key.
    pub member_fn_type_keys: HashMap<String, TypeKey>,
    pub span: Span,
}

impl Display for ASpecType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "spec {} {{ ... }}", self.name)
    }
}

impl ASpecType {
    /// Performs semantic analysis on the given spec.
    pub fn from(ctx: &mut ProgramContext, spec_type: &SpecType) -> ASpecType {
        // Insert the empty spec type so we have a type key for it. We'll update it when we're
        // done analyzing.
        let mut a_spec_type = ASpecType {
            name: spec_type.name.value.clone(),
            maybe_params: None,
            member_fn_type_keys: Default::default(),
            span: spec_type.name.span,
        };
        let type_key = ctx.insert_type(AType::Spec(a_spec_type.clone()));

        // Define a symbol that maps to the spec type.
        if let Err(existing) = ctx.insert_ident(Ident::new_type(
            spec_type.name.value.clone(),
            spec_type.is_pub,
            type_key,
            Some(ctx.cur_mod_id()),
            spec_type.name.span,
        )) {
            let err = err_dup_ident(&spec_type.name.value, spec_type.span, existing.span);
            ctx.insert_err(err);
        }

        // Analyze generic params, if any and push them to the program context.
        let maybe_params = match &spec_type.maybe_params {
            Some(params) => {
                let params = AParams::from(ctx, params, type_key);
                ctx.push_params(params.clone());
                Some(params)
            }
            None => None,
        };

        // Update the stored type with the resolved parameters. It's important that we do this
        // before analyzing any member fns because the field types may reference this type, in
        // which case it's important that we know what parameters it expects.
        a_spec_type.maybe_params = maybe_params.clone();
        ctx.replace_type(type_key, AType::Spec(a_spec_type));

        ctx.set_cur_self_type_key(Some(type_key));

        // Analyze all the function signatures in the spec.
        let mut fn_sigs = vec![];
        let mut member_fn_type_keys = HashMap::new();
        for fn_sig in &spec_type.fn_sigs {
            let a_fn_sig = AFnSig::from(ctx, fn_sig);
            member_fn_type_keys.insert(a_fn_sig.name.clone(), a_fn_sig.type_key);
            fn_sigs.push(a_fn_sig);
        }

        // Unset the "Self" and spec type keys now that we're done analyzing the spec.
        ctx.set_cur_self_type_key(None);

        // Update the type in the type store now that we've analyzed its fields.
        let a_spec_type = ASpecType {
            name: spec_type.name.value.clone(),
            maybe_params,
            member_fn_type_keys,
            span: spec_type.span,
        };
        ctx.replace_type(type_key, AType::Spec(a_spec_type.clone()));

        if a_spec_type.maybe_params.is_some() {
            // We've analyzed all the functions in this spec, but it's possible that some of the
            // functions had types that were monomorphizations of this spec type. For example, in
            // this spec
            //
            //      spec Thing[T] { fn thing[P: Thing[T]](ptr: *P) }
            //
            // the constraint on parameter `P` references a monomorphization of the `Thing` spec.
            // If this happens, the monomorphization would actually not be correct at this point
            // because it happened before any of the functions on this type had been analyzed and
            // written back to the type store. In other words, the monomorphization would have
            // happened on an empty type, so we need to redo it on the analyzed type.
            if let Some(monos) = ctx.monomorphized_types.remove(&type_key) {
                for mono in monos {
                    ctx.reexecute_monomorphization(mono);
                }
            }

            // Pop generic parameters now that we're done analyzing the type.
            ctx.pop_params(true);
        }

        a_spec_type
    }

    /// Returns true only if this spec type has all the same member functions as `other`.
    pub fn is_same_as(&self, other: &ASpecType) -> bool {
        self.member_fn_type_keys == other.member_fn_type_keys
    }
}
