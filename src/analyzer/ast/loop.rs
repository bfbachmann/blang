use std::fmt::{Display, Formatter};

use crate::analyzer::ast::closure::AClosure;
use crate::analyzer::ast::expr::AExpr;
use crate::analyzer::ast::statement::AStatement;
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::scope::ScopeKind;
use crate::parser::ast::r#loop::Loop;

/// Represents an analyzed loop statement.
#[derive(Clone, Debug, PartialEq)]
pub struct ALoop {
    pub maybe_init: Option<AStatement>,
    pub maybe_cond: Option<AExpr>,
    pub maybe_update: Option<AStatement>,
    pub body: AClosure,
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
        let maybe_init = match &loop_.maybe_init {
            Some(init_statement) => Some(AStatement::from(ctx, init_statement)),
            _ => None,
        };

        // Analyze the optional initialization loop condition, making sure
        // it results in a `bool` value.
        let maybe_cond = match &loop_.maybe_cond {
            Some(cond_expr) => Some(AExpr::from(
                ctx,
                cond_expr.clone(),
                Some(ctx.bool_type_key()),
                false,
                false,
                false,
            )),
            _ => None,
        };

        // Analyze the optional update statement.
        let maybe_update = match &loop_.maybe_update {
            Some(update_statement) => Some(AStatement::from(ctx, update_statement)),
            _ => None,
        };

        ALoop {
            maybe_init,
            maybe_cond,
            maybe_update,
            body: AClosure::from(ctx, &loop_.body, ScopeKind::LoopBody, vec![], None),
        }
    }
}
