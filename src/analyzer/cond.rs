use std::fmt;
use std::fmt::Formatter;

use crate::analyzer::closure::RichClosure;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::expr::RichExpr;
use crate::analyzer::prog_context::{ProgramContext, ScopeKind};
use crate::analyzer::AnalyzeResult;
use crate::parser::cond::Conditional;
use crate::parser::r#type::Type;
use crate::util;

/// Represents a semantically valid and type-rich branch.
#[derive(Debug)]
pub struct RichBranch {
    pub cond: Option<RichExpr>,
    pub body: RichClosure,
}

impl PartialEq for RichBranch {
    fn eq(&self, other: &Self) -> bool {
        util::optionals_are_equal(&self.cond, &other.cond) && self.body == other.body
    }
}

/// Represents a semantically valid and type-rich conditional.
#[derive(Debug)]
pub struct RichCond {
    pub branches: Vec<RichBranch>,
    pub ret_type: Option<Type>,
}

impl fmt::Display for RichCond {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        // TODO
        write!(f, "conditional")
    }
}

impl PartialEq for RichCond {
    fn eq(&self, other: &Self) -> bool {
        util::vectors_are_equal(&self.branches, &other.branches)
            && util::optionals_are_equal(&self.ret_type, &other.ret_type)
    }
}

impl RichCond {
    /// Performs semantic analysis on the given conditional and returns a type-rich version of it,
    /// or an error if the conditional is semantically invalid.
    pub fn from(ctx: &mut ProgramContext, cond: Conditional) -> AnalyzeResult<Self> {
        let mut rich_branches = vec![];
        for branch in cond.branches {
            // Check that the branch expression evaluates to a bool, if one exists.
            let rich_expr = match &branch.condition {
                Some(branch_cond) => {
                    let rich_expr = RichExpr::from(ctx, branch_cond.clone())?;
                    if rich_expr.typ != Type::Bool {
                        return Err(AnalyzeError::new(
                            ErrorKind::IncompatibleTypes,
                            format!(
                                "expected branch condition to have type bool, but found type {}",
                                &rich_expr.typ
                            )
                            .as_str(),
                        ));
                    }

                    Some(rich_expr)
                }
                None => None,
            };

            // Analyze the branch body and record the return type if the body is guaranteed to end in a
            // return statement.
            let rich_closure =
                RichClosure::from(ctx, branch.body, ScopeKind::Branch, vec![], None)?;

            rich_branches.push(RichBranch {
                cond: rich_expr,
                body: rich_closure,
            });
        }

        // If any of the branch bodies doesn't have a guaranteed return, we set the condition return
        // type to None. Otherwise, we set it to the guaranteed return type.
        let mut ret_type = None;
        for branch in &rich_branches {
            if branch.body.ret_type.is_none() {
                ret_type = None;
                break;
            }

            ret_type = branch.body.ret_type.clone();
        }

        Ok(RichCond {
            branches: rich_branches,
            ret_type,
        })
    }

    /// Returns true if the conditional is exhaustive (i.e. if it has an else case).
    pub fn is_exhaustive(&self) -> bool {
        if let Some(branch) = self.branches.last() {
            return branch.cond.is_none();
        }

        false
    }
}
