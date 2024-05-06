use std::fmt::{Display, Formatter};

use crate::analyzer::ast::expr::{AExpr, AExprKind};
use crate::analyzer::ast::r#type::AType;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::type_store::TypeKey;
use crate::lexer::pos::{Locatable, Position};
use crate::locatable_impl;
use crate::parser::ast::member::MemberAccess;

/// Represents access to a member or field on a type or an instance of a type.
#[derive(Debug, Clone)]
pub struct AMemberAccess {
    pub base_expr: AExpr,
    pub member_name: String,
    pub member_type_key: TypeKey,
    pub is_method: bool,
    start_pos: Position,
    end_pos: Position,
}

locatable_impl!(AMemberAccess);

impl Display for AMemberAccess {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}.{}", self.base_expr, self.member_name)
    }
}

impl AMemberAccess {
    /// Performs semantic analysis on the given member access expression.
    pub fn from(ctx: &mut ProgramContext, access: &MemberAccess) -> AMemberAccess {
        // Analyze the expression whose member is being accessed.
        let base_expr = AExpr::from(ctx, access.expr.clone(), None, false, true, false);

        // Abort early if the expression failed analysis.
        let base_type = ctx.must_get_type(base_expr.type_key);
        let base_type_string = base_type.display(ctx);
        if base_type.is_unknown() {
            return AMemberAccess {
                base_expr,
                member_name: access.member_name.clone(),
                member_type_key: ctx.unknown_type_key(),
                is_method: false,
                start_pos: access.start_pos().clone(),
                end_pos: access.end_pos().clone(),
            };
        }

        // Check if the member access is accessing a field on a struct type.
        let maybe_field_type_key = match base_type {
            // Only match struct field types if the base expression is not a type.
            // If it is a type, then we should only be trying to resolve member
            // functions on it.
            AType::Struct(struct_type) if !base_expr.kind.is_type() => {
                struct_type.get_field_type_key(access.member_name.as_str())
            }
            _ => None,
        };

        // Only allow access to the struct field if the struct type is
        // local to this module or if the field is public.
        if maybe_field_type_key.is_some()
            && !ctx.struct_field_is_accessible(base_expr.type_key, access.member_name.as_str())
        {
            ctx.insert_err(AnalyzeError::new(
                ErrorKind::UseOfPrivateValue,
                format_code!("{} is not public", access).as_str(),
                access,
            ));
        }

        // If we failed to find a field on this type with a matching name, check for a member
        // function with a matching name.
        let mut is_method = false;
        let member_type_key = match maybe_field_type_key {
            Some(type_key) => type_key,

            None => {
                match ctx.get_member_fn(base_expr.type_key, access.member_name.as_str()) {
                    Some(member_fn_sig) => {
                        is_method = true;
                        let member_type_key = member_fn_sig.type_key;

                        // Only allow access to the member if it is public or local
                        // to the current module.
                        if !ctx.member_fn_is_accessible(
                            base_expr.type_key,
                            access.member_name.as_str(),
                        ) {
                            ctx.insert_err(AnalyzeError::new(
                                ErrorKind::UseOfPrivateValue,
                                format_code!("{} is not public", access).as_str(),
                                access,
                            ))
                        }

                        member_type_key
                    }

                    None => {
                        // Error and return a placeholder value since we couldn't
                        // locate the member being accessed.
                        ctx.insert_err(AnalyzeError::new(
                            ErrorKind::UndefMember,
                            format_code!(
                                "type {} has no member {}",
                                base_type_string,
                                access.member_name
                            )
                            .as_str(),
                            access,
                        ));
                        ctx.unknown_type_key()
                    }
                }
            }
        };

        AMemberAccess {
            base_expr,
            member_name: access.member_name.clone(),
            member_type_key,
            is_method,
            start_pos: access.start_pos().clone(),
            end_pos: access.end_pos().clone(),
        }
    }

    /// Returns the expression at the base of the member access chain. Note that this is not necessarily the same as
    /// `self.base_expr`, as the parent expression may itself be a member access.
    pub fn get_base_expr(&self) -> &AExpr {
        match &self.base_expr.kind {
            AExprKind::MemberAccess(access) => access.get_base_expr(),
            _ => &self.base_expr,
        }
    }
}
