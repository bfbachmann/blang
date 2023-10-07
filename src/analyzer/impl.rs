use colored::Colorize;

use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::func::RichFn;
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::r#type::{RichType, TypeId};
use crate::parser::r#impl::Impl;
use crate::{format_code, util};

/// Represents a semantically valid `impl` block that declares member functions for a type.
#[derive(Debug)]
pub struct RichImpl {
    pub type_id: TypeId,
    pub member_fns: Vec<RichFn>,
}

impl Clone for RichImpl {
    fn clone(&self) -> Self {
        RichImpl {
            type_id: self.type_id.clone(),
            member_fns: self.member_fns.iter().map(|f| f.clone()).collect(),
        }
    }
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
        let member_fns = impl_
            .member_fns
            .iter()
            .map(|f| RichFn::from(ctx, f.clone()))
            .collect();

        // Remove the impl type ID from the program context now that we're done analyzing the impl.
        ctx.set_this_type_id(None);

        RichImpl {
            type_id,
            member_fns,
        }
    }
}
