use std::fmt::{Display, Formatter};

use crate::analyzer::ast::expr::{AExpr, AExprKind};
use crate::analyzer::ast::generic::AGenericType;
use crate::analyzer::ast::r#type::AType;
use crate::analyzer::error::{
    err_ambiguous_access, err_ambiguous_generic_member_access, err_member_not_method,
    err_mismatched_types, err_not_pub, err_spec_member_access, err_undef_member,
    err_unexpected_params, err_unresolved_params, AnalyzeResult, ErrorKind,
};
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::type_store::TypeKey;
use crate::lexer::pos::Span;
use crate::locatable_impl;
use crate::parser::ast::member::MemberAccess;
use crate::parser::ast::op::Operator;
use crate::Locatable;

/// Represents access to a member or field on a type or an instance of a type.
#[derive(Debug, Clone)]
pub struct AMemberAccess {
    pub base_expr: AExpr,
    pub member_name: String,
    pub member_type_key: TypeKey,
    pub is_method: bool,
    pub span: Span,
}

locatable_impl!(AMemberAccess);

impl Display for AMemberAccess {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}.{}", self.base_expr, self.member_name)
    }
}

impl AMemberAccess {
    /// Performs semantic analysis on the given member access expression.
    /// If `prefer_method` is set to true, and the member access could refer to either a field
    /// or a method by the same name, the method will be chosen.
    pub fn from(
        ctx: &mut ProgramContext,
        access: &MemberAccess,
        prefer_method: bool,
        allow_polymorph: bool,
    ) -> AMemberAccess {
        let member_name = &access.member_symbol.name;

        // Analyze the expression whose member is being accessed.
        let mut base_expr = AExpr::from(ctx, access.base_expr.clone(), None, true, false);
        let base_type = ctx.get_type(base_expr.type_key).clone();

        // Abort early if the expression failed analysis.
        let placeholder = AMemberAccess {
            base_expr: base_expr.clone(),
            member_name: member_name.value.clone(),
            member_type_key: ctx.unknown_type_key(),
            is_method: false,
            span: *access.span(),
        };
        if base_type.is_unknown() {
            return placeholder;
        }

        // Abort early if the base type is a spec. It's illegal to access member functions on
        // specs because they're not real functions.
        if let AType::Spec(spec_type) = base_type {
            let err = err_spec_member_access(&spec_type.name, access.span);
            ctx.insert_err(err);
            return placeholder;
        }

        // Try to resolve the member on the base expression type.
        let mut member_type_key = match try_resolve_member(
            ctx,
            access,
            &mut base_expr,
            &member_name.value,
            prefer_method,
        ) {
            Ok(values) => values,
            Err(err) => {
                ctx.insert_err(err);
                return placeholder;
            }
        };

        let member_type = ctx.get_type(member_type_key);
        let (maybe_mem_fn_sig, is_method) = match member_type {
            AType::Function(fn_sig) if fn_sig.maybe_impl_type_key.is_some() => (Some(fn_sig), true),
            _ => (None, false),
        };

        // Handle polymorphic methods.
        if let Some(fn_sig) = maybe_mem_fn_sig {
            let missing_params = access.member_symbol.params.is_empty();

            match &fn_sig.params {
                Some(expected_params) => {
                    member_type_key = if missing_params {
                        if !allow_polymorph {
                            // The method is polymorphic, but no params were provided. Record an
                            // error and set the member type to unknown.
                            let param_names =
                                expected_params.params.iter().map(|p| &p.name).collect();
                            let err = err_unresolved_params(
                                ctx,
                                &access.member_symbol,
                                member_type_key,
                                param_names,
                            );
                            ctx.insert_err(err);
                        }

                        member_type_key
                    } else {
                        // Monomorphize the method and update the method type key.
                        ctx.monomorphize_parameterized_type(
                            member_type_key,
                            &access.member_symbol.params,
                            &access.member_symbol,
                        )
                    }
                }

                None => {
                    if !missing_params {
                        // The method is monomorphic, but params where provided.
                        let err =
                            err_unexpected_params(ctx, member_type_key, access.member_symbol.span);
                        ctx.insert_err(err);
                    }
                }
            }
        }

        AMemberAccess {
            base_expr,
            member_name: member_name.value.clone(),
            member_type_key,
            is_method,
            span: *access.span(),
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

/// Tries to resolve the member on the given base expression.
fn try_resolve_member(
    ctx: &mut ProgramContext,
    access: &MemberAccess,
    base_expr: &mut AExpr,
    member_name: &str,
    prefer_method: bool,
) -> AnalyzeResult<TypeKey> {
    let not_found_err = err_undef_member(
        ctx,
        base_expr.type_key,
        member_name,
        access.member_symbol.span,
    );

    if base_expr.kind.is_type() {
        return match ctx.get_type(base_expr.type_key) {
            AType::Generic(generic_type) => {
                match resolve_generic_method(
                    ctx,
                    &generic_type.clone(),
                    member_name,
                    base_expr,
                    access,
                ) {
                    Some(fn_tk) => Ok(fn_tk),
                    None => Err(not_found_err),
                }
            }

            _ => resolve_concrete_method(ctx, access, base_expr, member_name),
        };
    }

    if prefer_method {
        // First try resolve the member as a method. If no such method exists, then fall back to
        // searching for struct fields.
        return match resolve_concrete_method(ctx, access, base_expr, member_name) {
            // We found it!
            Ok(member_tk) => Ok(member_tk),

            Err(err) => match &err.kind {
                // No matching method was found.
                ErrorKind::UndefMember => match resolve_struct_field(ctx, base_expr, member_name) {
                    // We found a matching struct field.
                    Ok(field_tk) => Ok(field_tk),

                    // We found a matching struct field, but it's private.
                    Err(Some(private_field_tk)) => {
                        ctx.insert_err(err_not_pub(member_name, access.member_symbol.span));
                        Ok(private_field_tk)
                    }

                    // No matching struct field was found.
                    Err(None) => Err(err),
                },

                // One or more matching methods was found, but the method use is invalid.
                _ => Err(err),
            },
        };
    }

    // First try resolve the member as a struct field. If no such field exists, then fall back
    // to searching for matching methods.
    match resolve_struct_field(ctx, base_expr, member_name) {
        // We found a matching struct field.
        Ok(field_tk) => Ok(field_tk),

        // We found a matching struct field that can't be accessed in this context (it's private).
        Err(Some(private_field_tk)) => {
            match resolve_concrete_method(ctx, access, base_expr, member_name) {
                // We found a matching method, so we'll use that.
                Ok(member_tk) => Ok(member_tk),

                Err(err) => match &err.kind {
                    // We didn't find a matching method, so we'll return the field type and record
                    // an error indicating that it can't be accessed in this context.
                    ErrorKind::UndefMember => {
                        ctx.insert_err(err_not_pub(member_name, access.member_symbol.span));
                        Ok(private_field_tk)
                    }

                    // We found at least one method, but the way it's used is invalid.
                    _ => Err(err),
                },
            }
        }

        // We found no matching struct fields. Just search for matching methods.
        Err(None) => resolve_concrete_method(ctx, access, base_expr, member_name),
    }
}

/// Tries to resolve the member as a struct field.
/// Returns
/// - `Ok(field_tk)` if the field was resolved successfully
/// - `Err(Some(field_tk))` if the field was resolved but is not accessible in this context
/// - `Err(None)` if no such field exists.
fn resolve_struct_field(
    ctx: &mut ProgramContext,
    base_expr: &mut AExpr,
    member_name: &str,
) -> Result<TypeKey, Option<TypeKey>> {
    let base_type = ctx.get_type(base_expr.type_key);
    let (struct_type, struct_tk, needs_deref) = match base_type {
        AType::Struct(struct_type) => (struct_type, base_expr.type_key, false),
        AType::Pointer(ptr_type) => match ctx.get_type(ptr_type.pointee_type_key) {
            AType::Struct(struct_type) => (struct_type, ptr_type.pointee_type_key, true),
            _ => return Err(None),
        },
        _ => {
            return Err(None);
        }
    };

    match struct_type.get_field_type_key(member_name) {
        Some(field_tk) => {
            // Only allow access to the struct field if the struct type is
            // local to this module or if the field is public.
            match ctx.struct_field_is_accessible(struct_tk, member_name) {
                true => {
                    if needs_deref {
                        *base_expr = AExpr::new(
                            AExprKind::UnaryOperation(
                                Operator::Defererence,
                                Box::new(base_expr.clone()),
                            ),
                            struct_tk,
                            *base_expr.span(),
                        );
                    }
                    Ok(field_tk)
                }
                false => Err(Some(field_tk)),
            }
        }

        None => Err(None),
    }
}

/// Tries to resolve the member as a method on a generic type.
fn resolve_generic_method(
    ctx: &mut ProgramContext,
    generic_type: &AGenericType,
    member_name: &str,
    base_expr: &AExpr,
    access: &MemberAccess,
) -> Option<TypeKey> {
    // We need to locate the member function by searching the spec
    // constraints for this generic type.
    let mut matching_fns = vec![];
    let mut matching_spec_names = vec![];
    'next_spec: for spec_tk in &generic_type.spec_type_keys {
        let spec = ctx.get_type(*spec_tk).to_spec_type();
        for (fn_name, fn_tk) in &spec.member_fn_type_keys {
            if fn_name == member_name {
                let fn_type = ctx.get_type(*fn_tk).to_fn_sig();
                matching_fns.push(fn_type);
                matching_spec_names.push(spec.name.as_str());
                continue 'next_spec;
            }
        }
    }

    // There may be multiple specs that have functions with matching names,
    // or none at all.
    match matching_fns.len() {
        0 => {
            let err = err_undef_member(
                ctx,
                base_expr.type_key,
                member_name,
                access.member_symbol.span,
            );
            ctx.insert_err(err);
            None
        }

        1 => {
            // We found a matching member function. We just need to
            // change any spec type keys into type keys that match
            // the base generic type the function is being called on.
            let mut fn_sig = matching_fns[0].clone();
            fn_sig.replace_type_and_define(
                ctx,
                fn_sig.maybe_impl_type_key.unwrap(),
                base_expr.type_key,
            );

            Some(fn_sig.type_key)
        }

        _ => {
            let err = err_ambiguous_generic_member_access(
                access,
                &generic_type.name,
                matching_spec_names,
                member_name,
                access.member_symbol.span,
            );
            ctx.insert_err(err);
            None
        }
    }
}

/// Tries to resolve the member on a concrete (non-generic) type.
fn resolve_concrete_method(
    ctx: &mut ProgramContext,
    access: &MemberAccess,
    base_expr: &mut AExpr,
    member_name: &str,
) -> AnalyzeResult<TypeKey> {
    // If the base expression type is a pointer, then we'll try resolving the method on the pointee
    // type.
    let (base_type_key, base_expr_is_ptr) = match ctx.get_type(base_expr.type_key) {
        AType::Pointer(ptr_type) => (ptr_type.pointee_type_key, true),
        _ => (base_expr.type_key, false),
    };

    match ctx.get_or_monomorphize_member_fn(base_type_key, member_name) {
        // We found a single matching member function. We just need to check that it's being used
        // correctly.
        Ok(Some(member_fn_sig)) => {
            let called_via_type = base_expr.kind.is_type();
            let (takes_self, maybe_self_type_key) = match member_fn_sig.args.first() {
                Some(arg) => (arg.name == "self", Some(arg.type_key)),
                None => (false, None),
            };
            let member_type_key = member_fn_sig.type_key;

            // Only allow access to the member if it is public or local
            // to the current module.
            if !ctx.member_fn_is_accessible(
                member_fn_sig.maybe_impl_type_key.unwrap(),
                member_fn_sig.type_key,
            ) {
                ctx.insert_err(err_not_pub(member_name, access.member_symbol.span));
            }

            if called_via_type {
                return Ok(member_type_key);
            }

            // If the base expression is a value rather than a type,
            // we need to make sure the member function being accessed
            // takes `self` as its first argument.
            if !takes_self {
                return Err(err_member_not_method(
                    ctx,
                    base_type_key,
                    member_name,
                    access.member_symbol.span,
                ));
            }

            // At this point we know it's a valid method call on a
            // concrete value. If the value is not a pointer, but the
            // method requires a pointer, then we need to implicitly
            // take a reference to the value.
            let self_arg_type_key = maybe_self_type_key.unwrap();
            let self_arg_type = ctx.get_type(self_arg_type_key);
            if self_arg_type.is_any_ptr() && !base_expr_is_ptr {
                let op = match self_arg_type.is_mut_ptr() {
                    true => {
                        // Record an error if we're not allowed to get a
                        // `&mut` to the base expression.
                        base_expr.check_referencable_as_mut(ctx, base_expr);
                        Operator::MutReference
                    }
                    false => Operator::Reference,
                };

                let span = *base_expr.span();
                *base_expr = AExpr::new(
                    AExprKind::UnaryOperation(op, Box::new(base_expr.clone())),
                    self_arg_type_key,
                    span,
                );
            } else if self_arg_type.is_mut_ptr() && !ctx.get_type(base_expr.type_key).is_mut_ptr() {
                // Record an error here because we're trying to call
                // a method that requires `*mut T` with only a `*T`.
                let err = err_mismatched_types(
                    ctx,
                    self_arg_type_key,
                    base_expr.type_key,
                    *access.base_expr.span(),
                );
                ctx.insert_err(err);
            }

            Ok(member_type_key)
        }

        // Error and return a placeholder value since we couldn't
        // locate the member being accessed.
        Ok(None) => Err(err_undef_member(
            ctx,
            base_expr.type_key,
            member_name,
            access.member_symbol.span,
        )),

        // Many matching member functions were found by the given name, so this
        // reference is ambiguous.
        Err(_) => Err(err_ambiguous_access(
            ctx,
            base_expr.type_key,
            member_name,
            access.member_symbol.span,
        )),
    }
}
