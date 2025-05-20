use std::fmt::{Display, Formatter};

use crate::analyzer::ast::closure::AClosure;
use crate::analyzer::ast::expr::AExpr;
use crate::analyzer::ast::statement::AStatement;
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::scope::ScopeKind;
use crate::lexer::pos::Span;
use crate::parser::ast::r#loop::Loop;

/// Represents an analyzed loop statement.
#[derive(Clone, Debug, PartialEq)]
pub struct ALoop {
    pub maybe_init: Option<AStatement>,
    pub maybe_cond: Option<AExpr>,
    pub maybe_update: Option<AStatement>,
    pub body: AClosure,
    pub span: Span,
}

impl Display for ALoop {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "for {}; {}; {}; {{ ... }}",
            match &self.maybe_init {
                Some(init) => format!("{}", init),
                None => "".into(),
            },
            match &self.maybe_cond {
                Some(cond) => format!("{}", cond),
                None => "".into(),
            },
            match &self.maybe_update {
                Some(update) => format!("{}", update),
                None => "".into(),
            },
        )
    }
}

impl ALoop {
    pub fn from(ctx: &mut ProgramContext, loop_: &Loop) -> ALoop {
        // Analyze the optional initialization statement.
        let maybe_init = loop_.maybe_init.as_ref().map(|init_statement| AStatement::from(ctx, init_statement));

        // Analyze the optional initialization loop condition, making sure
        // it results in a `bool` value.
        let maybe_cond = loop_.maybe_cond.as_ref().map(|cond_expr| AExpr::from(
                ctx,
                cond_expr.clone(),
                Some(ctx.bool_type_key()),
                false,
                false,
            ));

        // Analyze the optional update statement.
        let maybe_update = loop_.maybe_update.as_ref().map(|update_statement| AStatement::from(ctx, update_statement));

        ALoop {
            maybe_init,
            maybe_cond,
            maybe_update,
            body: AClosure::from(ctx, &loop_.body, ScopeKind::LoopBody, vec![], None),
            span: loop_.span,
        }
    }
}
