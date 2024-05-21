use std::fmt::{Display, Formatter};

use crate::analyzer::ast::expr::{AExpr, AExprKind};
use crate::analyzer::ast::r#type::AType;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::type_store::TypeKey;
use crate::lexer::pos::{Locatable, Position, Span};
use crate::locatable_impl;
use crate::parser::ast::member::MemberAccess;
use crate::parser::ast::op::Operator;

/// Represents access to a member or field on a type or an instance of a type.
#[derive(Debug, Clone)]
pub struct AMemberAccess {
    pub base_expr: AExpr,
    pub member_name: String,
    pub member_type_key: TypeKey,
    pub is_method: bool,
    span: Span,
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
        let mut base_expr = AExpr::from(ctx, access.expr.clone(), None, false, true, false);

        // Abort early if the expression failed analysis.
        let base_type = ctx.must_get_type(base_expr.type_key);
        let base_type_string = base_type.display(ctx);

        let placeholder = AMemberAccess {
            base_expr: base_expr.clone(),
            member_name: access.member_name.clone(),
            member_type_key: ctx.unknown_type_key(),
            is_method: false,
            span: access.span().clone(),
        };
        if base_type.is_unknown() {
            return placeholder;
        }

        // Check if the member access is accessing a field on a struct type or
        // a member function or method on a type.
        let (maybe_field_type_key, base_type_key, base_expr_is_ptr) = match base_type {
            // Only match struct field types if the base expression is not a type.
            // If it is a type, then we should only be trying to resolve member
            // functions on it.
            AType::Struct(struct_type) if !base_expr.kind.is_type() => {
                let maybe_field_type_key =
                    struct_type.get_field_type_key(access.member_name.as_str());

                // Only allow access to the struct field if the struct type is
                // local to this module or if the field is public.
                if maybe_field_type_key.is_some()
                    && !ctx
                        .struct_field_is_accessible(base_expr.type_key, access.member_name.as_str())
                {
                    ctx.insert_err(AnalyzeError::new(
                        ErrorKind::UseOfPrivateValue,
                        format_code!("{} is not public", access).as_str(),
                        access,
                    ));
                }

                (maybe_field_type_key, base_expr.type_key, false)
            }

            // For pointer types, we'll try to use the pointee type to resolve methods
            // or member functions.
            AType::Pointer(ptr_type) => (None, ptr_type.pointee_type_key, true),

            _ => (None, base_expr.type_key, false),
        };

        // If we failed to find a field on this type with a matching name, check for a member
        // function with a matching name.
        let (member_type_key, is_method) = if let Some(tk) = maybe_field_type_key {
            (tk, false)
        } else {
            match ctx.get_member_fn(base_type_key, access.member_name.as_str()) {
                Some(member_fn_sig) => {
                    let called_via_type = base_expr.kind.is_type();
                    let (takes_self, maybe_self_type_key) = match member_fn_sig.args.first() {
                        Some(arg) => (arg.name == "self", Some(arg.type_key)),
                        None => (false, None),
                    };
                    let member_type_key = member_fn_sig.type_key;

                    // Only allow access to the member if it is public or local
                    // to the current module.
                    if !ctx.member_fn_is_accessible(base_type_key, access.member_name.as_str()) {
                        ctx.insert_err(AnalyzeError::new(
                            ErrorKind::UseOfPrivateValue,
                            format_code!("{} is not public", access).as_str(),
                            access,
                        ))
                    }

                    // If the base expression is a value rather than a type,
                    // we need to make sure the member function being accessed
                    // takes `self` as its first argument.
                    if !called_via_type {
                        if !takes_self {
                            ctx.insert_err(
                                AnalyzeError::new(
                                    ErrorKind::UndefMember,
                                    format_code!("{} is not a method", access.member_name).as_str(),
                                    access,
                                )
                                .with_help(
                                    format_code!(
                                        "Consider accessing this function via its type ({}), \
                                        or add {} as the first argument to make it a method.",
                                        format!(
                                            "{}.{}",
                                            ctx.display_type_for_key(base_type_key),
                                            access.member_name
                                        ),
                                        "self"
                                    )
                                    .as_str(),
                                ),
                            );

                            return placeholder;
                        }

                        // At this point we know it's a valid method call on a
                        // concrete value. If the value is not a pointer, but the
                        // method requires a pointer, then we need to implicitly
                        // take a reference to the value.
                        let self_arg_type_key = maybe_self_type_key.unwrap();
                        let self_arg_type = ctx.must_get_type(self_arg_type_key);
                        if !base_expr_is_ptr && self_arg_type.is_ptr() {
                            let op = match self_arg_type.is_mut_pointer() {
                                true => {
                                    // Record an error if we're not allowed to get a
                                    // `&mut` to the base expression.
                                    base_expr.check_referencable_as_mut(ctx, &base_expr);
                                    Operator::MutReference
                                }
                                false => Operator::Reference,
                            };

                            let span = base_expr.span().clone();
                            base_expr = AExpr::new(
                                AExprKind::UnaryOperation(op, Box::new(base_expr)),
                                self_arg_type_key,
                                span,
                            );
                        } else if self_arg_type.is_mut_pointer() {
                            // Record an error here because we're trying to call
                            // a method that requires `*mut T` with only a `*T`.
                            base_expr.check_referencable_as_mut(ctx, &base_expr);
                        }
                    }

                    (member_type_key, true)
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

                    (ctx.unknown_type_key(), false)
                }
            }
        };

        AMemberAccess {
            base_expr,
            member_name: access.member_name.clone(),
            member_type_key,
            is_method,
            span: access.span().clone(),
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
