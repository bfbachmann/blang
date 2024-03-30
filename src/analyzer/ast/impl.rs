use crate::analyzer::ast::func::AFn;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::type_store::TypeKey;
use crate::parser::ast::r#impl::Impl;
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
        let type_key = ctx.resolve_type(&impl_.typ);

        // Set the impl type key in the program context so we can use it when resolving type `This`.
        ctx.set_cur_self_type_key(Some(type_key));

        // Analyze member functions.
        let mut member_fns = vec![];
        for mem_fn in &impl_.member_fns {
            let a_fn = AFn::from(ctx, mem_fn);

            // Only add the member function if it's not templated.
            if !a_fn.signature.is_templated() {
                member_fns.push(a_fn);
            }
        }

        ctx.set_cur_self_type_key(None);

        AImpl {
            type_key,
            member_fns,
        }
    }
}
