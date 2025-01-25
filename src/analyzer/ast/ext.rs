use std::fmt::{Display, Formatter};

use crate::analyzer::ast::func::AFnSig;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::prog_context::ProgramContext;
use crate::lexer::pos::Span;
use crate::parser::ast::r#extern::ExternFn;

/// An analyzed extern function declaration.
#[derive(PartialEq, Clone, Debug)]
pub struct AExternFn {
    pub fn_sig: AFnSig,
    pub maybe_link_name: Option<String>,
    pub span: Span,
}

impl Display for AExternFn {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}{}",
            match &self.maybe_link_name {
                Some(name) => format!("\"{name}\" "),
                None => "".to_string(),
            },
            self.fn_sig
        )
    }
}

impl AExternFn {
    /// Performs semantic analysis on an extern function declaration and returns the result.
    pub fn from(ctx: &mut ProgramContext, ext: &ExternFn) -> AExternFn {
        // Make sure we are not already inside a function. Extern functions cannot be
        // defined within other functions.
        if ctx.is_in_fn() {
            ctx.insert_err(AnalyzeError::new(
                ErrorKind::InvalidStatement,
                "cannot declare external functions inside other functions",
                ext,
            ));
        }

        // Analyze the function signature in the `extern` block.
        AExternFn {
            fn_sig: AFnSig::from(ctx, &ext.fn_sig),
            maybe_link_name: ext.maybe_link_name.clone(),
            span: ext.span,
        }
    }
}
