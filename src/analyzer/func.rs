use std::fmt;
use std::fmt::Formatter;

use crate::analyzer::closure::{check_closure_returns, RichClosure};
use crate::analyzer::func_sig::RichFnSig;
use crate::analyzer::prog_context::{ProgramContext, ScopeKind};
use crate::analyzer::r#type::RichType;
use crate::parser::func::Function;

/// Represents a semantically valid and type-rich function.
#[derive(PartialEq, Debug, Clone)]
pub struct RichFn {
    pub signature: RichFnSig,
    pub body: RichClosure,
}

impl fmt::Display for RichFn {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{} {{...}}", &self.signature)
    }
}

impl RichFn {
    /// Performs semantic analysis on the given function and returns a type-rich version of it.
    pub fn from(ctx: &mut ProgramContext, func: Function) -> Self {
        let signature = RichFnSig::from(ctx, &func.signature);

        // Templated functions will be rendered and analyzed when we analyze statements or
        // expressions where they're used. This way, we can use information from the context in
        // which they're used to render and check templated values.
        if func.signature.tmpl_params.is_some() {
            return RichFn {
                signature,
                body: RichClosure::new_empty(),
            };
        }

        // Analyze the function body.
        let rich_closure = RichClosure::from(
            ctx,
            func.body.clone(),
            ScopeKind::FnBody,
            func.signature.args.clone(),
            func.signature.return_type.clone(),
        );

        // Make sure the function return conditions are satisfied by the closure.
        if let Some(ret_type) = &func.signature.return_type {
            let rich_ret_type = RichType::analyze(ctx, &ret_type);
            check_closure_returns(ctx, &rich_closure, &rich_ret_type, &ScopeKind::FnBody);
        }

        RichFn {
            signature,
            body: rich_closure,
        }
    }
}
