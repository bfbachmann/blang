use colored::Colorize;

use crate::analyzer::ast::func::AFnSig;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::prog_context::ProgramContext;
use crate::parser::spec::Spec;

/// Represents a semantically valid spec declaration.
#[derive(PartialEq, Clone, Debug)]
pub struct ASpec {
    pub name: String,
    pub fn_sigs: Vec<AFnSig>,
}

impl ASpec {
    /// Performs semantic analysis on the given spec.
    pub fn from(ctx: &mut ProgramContext, spec: &Spec) -> ASpec {
        // Make sure this spec name is not a duplicate.
        if ctx.get_spec(spec.name.as_str()).is_some() {
            // Record the error and return a placeholder value.
            ctx.insert_err(AnalyzeError::new(
                ErrorKind::DuplicateSpec,
                format_code!("another spec named {} already exists", spec.name).as_str(),
                spec,
            ));

            return ASpec {
                name: spec.name.clone(),
                fn_sigs: vec![],
            };
        }

        // Set the unknown type "This" as the current type of "this" so it can be resolved when
        // we analyzed methods in this spec.
        ctx.set_cur_this_type_key(Some(ctx.this_type_key()));

        // Analyze all the function signatures in the spec.
        let mut fn_sigs = vec![];
        for fn_sig in &spec.fn_sigs {
            fn_sigs.push(AFnSig::from(ctx, fn_sig));
        }

        // Unset the "This" type now that we're done analyzing the spec.
        ctx.set_cur_this_type_key(None);

        let a_spec = ASpec {
            name: spec.name.clone(),
            fn_sigs,
        };

        // Add the new spec to the program context so we can reference it by name later.
        ctx.insert_spec(a_spec.clone());
        a_spec
    }
}
