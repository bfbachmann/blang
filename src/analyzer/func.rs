use std::fmt;
use std::fmt::Formatter;

use crate::analyzer::closure::{check_closure_returns, RichClosure};
use crate::analyzer::error::{AnalyzeError, ErrorKind};
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
        // Make sure we are not already inside a function. For now, functions cannot be defined
        // within other functions.
        if ctx.is_in_fn() {
            ctx.add_err(AnalyzeError::new(
                ErrorKind::InvalidStatement,
                "cannot declare functions inside other functions",
                &func,
            ));
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
            signature: RichFnSig::from(ctx, &func.signature),
            body: rich_closure,
        }
    }
}
