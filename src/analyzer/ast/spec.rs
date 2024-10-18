use std::collections::HashMap;
use std::fmt::{Display, Formatter};

use crate::analyzer::ast::func::AFnSig;
use crate::analyzer::ast::r#type::AType;
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::type_store::TypeKey;
use crate::parser::ast::spec::Spec;

/// Represents a set of functions that are associated with a type (i.e. a set
/// of things one can do with a type).
#[derive(PartialEq, Clone, Debug)]
pub struct ASpecType {
    pub name: String,
    /// Maps member function name to the function type key.
    pub member_fn_type_keys: HashMap<String, TypeKey>,
}

impl Display for ASpecType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "spec {} {{ ... }}", self.name)
    }
}

impl ASpecType {
    /// Performs semantic analysis on the given spec.
    pub fn from(ctx: &mut ProgramContext, spec: &Spec) -> ASpecType {
        // Insert the empty spec type so we have a type key for it. We'll update it when we're
        // done analyzing.
        let type_key = ctx.force_insert_type(AType::Spec(ASpecType {
            name: spec.name.clone(),
            member_fn_type_keys: Default::default(),
        }));
        ctx.set_cur_self_type_key(Some(type_key));
        ctx.set_cur_spec_type_key(Some(type_key));

        // Analyze all the function signatures in the spec.
        let mut fn_sigs = vec![];
        let mut member_fn_type_keys = HashMap::new();
        for fn_sig in &spec.fn_sigs {
            let a_fn_sig = AFnSig::from(ctx, fn_sig);
            member_fn_type_keys.insert(a_fn_sig.name.clone(), a_fn_sig.type_key);
            fn_sigs.push(a_fn_sig);
        }

        // Unset the "Self" and spec type keys now that we're done analyzing the spec.
        ctx.set_cur_spec_type_key(None);
        ctx.set_cur_self_type_key(None);

        let spec_type = ASpecType {
            name: spec.name.clone(),
            member_fn_type_keys,
        };

        // Add the new spec to the program context so we can reference it by name later.
        ctx.replace_type(type_key, AType::Spec(spec_type.clone()));

        // Record the type name as public in the current module if necessary.
        if spec.is_pub {
            ctx.mark_type_pub(type_key);
        }

        spec_type
    }
}
