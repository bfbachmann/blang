use colored::Colorize;

use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::func::RichFn;
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::r#type::{RichType, TypeId};
use crate::parser::r#impl::Impl;
use crate::{format_code, util};

/// Represents a semantically valid `impl` block that declares member functions for a type.
#[derive(Debug, Clone)]
pub struct RichImpl {
    pub type_id: TypeId,
    pub member_fns: Vec<RichFn>,
}

impl PartialEq for RichImpl {
    fn eq(&self, other: &Self) -> bool {
        self.type_id == other.type_id && util::vecs_eq(&self.member_fns, &other.member_fns)
    }
}

impl RichImpl {
    pub fn from(ctx: &mut ProgramContext, impl_: &Impl) -> Self {
        // Make sure the `impl` block is not being defined inside a function.
        if ctx.is_in_fn() {
            ctx.add_err(AnalyzeError::new(
                ErrorKind::InvalidStatement,
                format_code!("cannot declare {} inside function", "impl").as_str(),
                impl_,
            ))
        }

        // Get the type ID of the type for this impl.
        let type_id = RichType::analyze(ctx, &impl_.typ);

        // Set the impl type ID in the program context so we can use it when resolving type `This`.
        ctx.set_this_type_id(Some(type_id.clone()));

        // Analyze member functions.
        let mut member_fns = vec![];
        for mem_fn in &impl_.member_fns {
            let rich_fn = RichFn::from(ctx, mem_fn.clone());

            // Only add the member function if it's not templated.
            if !rich_fn.signature.is_templated() {
                member_fns.push(rich_fn);
            }
        }

        // Remove the impl type ID from the program context now that we're done analyzing the impl.
        ctx.set_this_type_id(None);

        RichImpl {
            type_id,
            member_fns,
        }
    }
}
