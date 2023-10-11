use colored::Colorize;

use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::func_sig::RichFnSig;
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::r#type::TypeId;
use crate::format_code;
use crate::parser::r#type::Type;
use crate::parser::spec::Spec;
use crate::parser::unresolved::UnresolvedType;

/// Represents a semantically valid spec declaration.
#[derive(PartialEq, Clone, Debug)]
pub struct RichSpec {
    pub name: String,
    pub fn_sigs: Vec<RichFnSig>,
}

impl RichSpec {
    /// Performs semantic analysis on the given spec.
    pub fn from(ctx: &mut ProgramContext, spec_: &Spec) -> Self {
        // Make sure this spec name is not a duplicate.
        if ctx.get_spec(spec_.name.as_str()).is_some() {
            // Record the error and return a placeholder value.
            ctx.add_err(AnalyzeError::new(
                ErrorKind::SpecAlreadyDefined,
                format_code!("another spec named {} already exists", spec_.name).as_str(),
                spec_,
            ));

            return RichSpec {
                name: spec_.name.clone(),
                fn_sigs: vec![],
            };
        }

        // Set the current spec type ID in the program context so instances of the type `This` in
        // the spec methods can be resolved to this spec type.
        ctx.set_this_type_id(Some(TypeId::from(Type::new_unknown(spec_.name.as_str()))));

        // Analyze all the function signatures in the spec.
        let mut fn_sigs = vec![];
        for fn_sig in &spec_.fn_sigs {
            fn_sigs.push(RichFnSig::from(ctx, fn_sig));
        }

        // Unset the current spec type ID since we're done analyzing the spec.
        ctx.set_this_type_id(None);

        let rich_spec = RichSpec {
            name: spec_.name.clone(),
            fn_sigs,
        };

        // Add the new spec to the program context so we can reference it by name later.
        ctx.add_spec(rich_spec.clone());
        rich_spec
    }

    /// Returns the type ID that corresponds to this spec type.
    pub fn type_id(&self) -> TypeId {
        TypeId::from(Type::Unresolved(UnresolvedType::new_with_default_pos(
            self.name.as_str(),
        )))
    }
}
