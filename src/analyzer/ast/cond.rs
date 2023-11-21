use std::fmt;
use std::fmt::Formatter;

use crate::analyzer::ast::closure::AClosure;
use crate::analyzer::ast::expr::AExpr;
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::scope::ScopeKind;
use crate::analyzer::type_store::TypeKey;
use crate::lexer::pos::{Locatable, Position};
use crate::parser::ast::cond::Conditional;
use crate::{locatable_impl, util};

/// Represents a semantically valid and type-rich branch.
#[derive(Clone, Debug)]
pub struct ABranch {
    pub cond: Option<AExpr>,
    pub body: AClosure,
    start_pos: Position,
    end_pos: Position,
}

impl PartialEq for ABranch {
    fn eq(&self, other: &Self) -> bool {
        util::opts_eq(&self.cond, &other.cond) && self.body == other.body
    }
}

locatable_impl!(ABranch);

/// Represents a semantically valid and type-rich conditional.
#[derive(Clone, Debug)]
pub struct ACond {
    pub branches: Vec<ABranch>,
    pub ret_type_key: Option<TypeKey>,
}

impl fmt::Display for ACond {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        // TODO
        write!(f, "conditional")
    }
}

impl PartialEq for ACond {
    fn eq(&self, other: &Self) -> bool {
        util::vecs_eq(&self.branches, &other.branches)
            && util::opts_eq(&self.ret_type_key, &other.ret_type_key)
    }
}

impl Locatable for ACond {
    fn start_pos(&self) -> &Position {
        self.branches.first().unwrap().start_pos()
    }

    fn end_pos(&self) -> &Position {
        self.branches.last().unwrap().end_pos()
    }
}

impl ACond {
    /// Performs semantic analysis on the given conditional and returns a type-rich version of it.
    pub fn from(ctx: &mut ProgramContext, cond: &Conditional) -> Self {
        let mut rich_branches = vec![];
        for branch in &cond.branches {
            // Check that the branch expression evaluates to a bool, if one exists.
            let rich_expr = match &branch.condition {
                Some(branch_cond) => {
                    let rich_expr =
                        AExpr::from(ctx, branch_cond.clone(), Some(ctx.bool_type_key()), false);
                    Some(rich_expr)
                }
                None => None,
            };

            // Analyze the branch body and record the return type if the body is guaranteed to end in a
            // return statement.
            let rich_closure =
                AClosure::from(ctx, &branch.body, ScopeKind::BranchBody, vec![], None);

            rich_branches.push(ABranch {
                cond: rich_expr,
                body: rich_closure,
                start_pos: branch.start_pos,
                end_pos: branch.end_pos,
            });
        }

        // If any of the branch bodies doesn't have a guaranteed return, we set the condition return
        // type to None. Otherwise, we set it to the guaranteed return type.
        let mut ret_type = None;
        for branch in &rich_branches {
            if branch.body.ret_type_key.is_none() {
                ret_type = None;
                break;
            }

            ret_type = branch.body.ret_type_key.clone();
        }

        ACond {
            branches: rich_branches,
            ret_type_key: ret_type,
        }
    }

    /// Returns true if the conditional is exhaustive (i.e. if it has an else case).
    pub fn is_exhaustive(&self) -> bool {
        if let Some(branch) = self.branches.last() {
            return branch.cond.is_none();
        }

        false
    }
}
