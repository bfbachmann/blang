use std::fmt::{Display, Formatter};

use crate::analyzer::ast::func::AFnSig;
use crate::analyzer::error::{err_dup_ident, err_invalid_extern, err_invalid_statement};
use crate::analyzer::ident::{Ident, IdentKind};
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
            ctx.insert_err(err_invalid_statement(ext.span));
        }

        if let Some(params) = &ext.signature.params {
            ctx.insert_err(err_invalid_extern(params.span));
        }

        let fn_sig = AFnSig::from(ctx, &ext.signature);

        if let Err(existing) = ctx.insert_ident(Ident {
            name: ext.signature.name.clone(),
            kind: IdentKind::ExternFn {
                is_pub: ext.is_pub,
                type_key: fn_sig.type_key,
                mod_id: Some(ctx.cur_mod_id()),
            },
            span: ext.span, // TODO: use name span
        }) {
            let err = err_dup_ident(&existing.name, ext.span, existing.span);
            ctx.insert_err(err);
        }

        let a_ext_fn = AExternFn {
            fn_sig,
            maybe_link_name: ext.maybe_link_name.clone(),
            span: ext.span,
        };

        // TODO: don't clone.
        ctx.insert_analyzed_extern_fn(a_ext_fn.clone());

        a_ext_fn
    }
}
