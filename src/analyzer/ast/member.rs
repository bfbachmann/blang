use std::fmt::{Display, Formatter};

use crate::analyzer::ast::expr::{AExpr, AExprKind};
use crate::analyzer::ast::r#type::AType;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::type_store::TypeKey;
use crate::fmt::format_code_vec;
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
    /// If `prefer_method` is set to true, and the member access could refer to either a field
    /// or a method by the same name, the method will be chosen.
    pub fn from(
        ctx: &mut ProgramContext,
        access: &MemberAccess,
        prefer_method: bool,
    ) -> AMemberAccess {
        let member_name = &access.member_symbol.name;

        // Analyze the expression whose member is being accessed.
        let mut base_expr = AExpr::from(ctx, access.base_expr.clone(), None, true, false);
        let base_type = ctx.must_get_type(base_expr.type_key).clone();
        let base_type_string = ctx.display_type(base_expr.type_key);

        // Abort early if the expression failed analysis.
        let placeholder = AMemberAccess {
            base_expr: base_expr.clone(),
            member_name: member_name.clone(),
            member_type_key: ctx.unknown_type_key(),
            is_method: false,
            span: access.span().clone(),
        };
        if base_type.is_unknown() {
            return placeholder;
        }

        // Abort early if the base type is a spec. It's illegal to access member functions on
        // specs because they're not real functions.
        if let AType::Spec(spec_type) = base_type {
            ctx.insert_err(
                AnalyzeError::new(
                    ErrorKind::SpecMemberAccess,
                    "cannot access members on spec types",
                    access,
                )
                .with_detail(
                    format_code!(
                        "Spec types like {} contain don't have real member functions, so \
                        it's impossible to access their members this way.",
                        spec_type.name
                    )
                    .as_str(),
                ),
            );
            return placeholder;
        }

        // Try to resolve the member on the base expression type.
        let (maybe_field_type_key, base_type_key, base_expr_is_ptr) = match try_resolve_member(
            ctx,
            access,
            &base_expr,
            &base_type,
            member_name,
            prefer_method,
            &base_type_string,
        ) {
            Ok(values) => values,
            Err(_) => {
                return placeholder;
            }
        };

        // If we failed to find a field on this type with a matching name, check for a member
        // function with a matching name.
        let (member_type_key, is_method) = match maybe_field_type_key {
            Some(tk) => (tk, false),
            None => {
                match try_resolve_method(
                    ctx,
                    access,
                    base_expr,
                    base_type_key,
                    member_name,
                    base_expr_is_ptr,
                    &base_type_string,
                ) {
                    Ok((base, member_tk, is_method)) => {
                        base_expr = base;
                        (member_tk, is_method)
                    }
                    Err(_) => return placeholder,
                }
            }
        };

        AMemberAccess {
            base_expr,
            member_name: member_name.clone(),
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

fn try_resolve_member(
    ctx: &mut ProgramContext,
    access: &MemberAccess,
    base_expr: &AExpr,
    base_type: &AType,
    member_name: &String,
    prefer_method: bool,
    base_type_string: &String,
) -> Result<(Option<TypeKey>, TypeKey, bool), ()> {
    // Check if the member access is accessing a field on a struct type or
    // a member function or method on a type.
    let (maybe_field_type_key, base_type_key, base_expr_is_ptr) = match base_type {
        // Only match struct field types if the base expression is not a type. We'll also avoid
        // matching struct fields if there is already a method with a matching name and
        // `prefer_methods` is `true`.
        AType::Struct(struct_type) => {
            let base_expr_is_type = base_expr.kind.is_type();
            let found_method =
                match ctx.get_or_monomorphize_member_fn(base_expr.type_key, member_name.as_str()) {
                    // There are no matching methods on this type.
                    Ok(None) => false,
                    // There is at least one matching method on this type.
                    _ => true,
                };
            let use_method = prefer_method && found_method;

            // Only try to locate the member as a struct field if we're not looking for a
            // method.
            if base_expr_is_type || use_method {
                (None, base_expr.type_key, false)
            } else {
                let maybe_field_type_key = struct_type.get_field_type_key(member_name.as_str());

                // Only allow access to the struct field if the struct type is
                // local to this module or if the field is public.
                if maybe_field_type_key.is_some()
                    && !ctx.struct_field_is_accessible(base_expr.type_key, member_name.as_str())
                {
                    ctx.insert_err(AnalyzeError::new(
                        ErrorKind::UseOfPrivateValue,
                        format_code!("field {} is not public", member_name).as_str(),
                        access,
                    ));
                }

                (maybe_field_type_key, base_expr.type_key, false)
            }
        }

        // For pointer types, we'll try to use the pointee type to resolve methods
        // or member functions.
        AType::Pointer(ptr_type) => (None, ptr_type.pointee_type_key, true),

        // If the base expression type is generic, it means we're accessing a
        // method defined via a generic constraint (spec).
        AType::Generic(generic_type) => {
            // We need to locate the member function by searching the spec
            // constraints for this generic type.
            let mut matching_fns = vec![];
            let mut matching_specs_names = vec![];
            'next_spec: for spec_tk in &generic_type.spec_type_keys {
                let spec = ctx.must_get_type(*spec_tk).to_spec_type();
                for (fn_name, fn_tk) in &spec.member_fn_type_keys {
                    if fn_name == member_name.as_str() {
                        let fn_type = ctx.must_get_type(*fn_tk).to_fn_sig();
                        matching_fns.push(fn_type);
                        matching_specs_names.push(spec.name.as_str());
                        continue 'next_spec;
                    }
                }
            }

            // There may be multiple specs that have functions with matching names,
            // or none at all.
            match matching_fns.len() {
                0 => {
                    ctx.insert_err(AnalyzeError::new(
                        ErrorKind::UndefMember,
                        format_code!("type {} has no member {}", base_type_string, member_name)
                            .as_str(),
                        access,
                    ));

                    return Err(());
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
                    (None, base_expr.type_key, false)
                }

                _ => {
                    ctx.insert_err(
                        AnalyzeError::new(
                            ErrorKind::AmbiguousAccess,
                            "ambiguous member access",
                            access,
                        )
                        .with_detail(
                            format!(
                                "{} is ambiguous because all of the following \
                                specs used in constraints for generic type {} contain \
                                functions named {}: {}.",
                                format_code!(access),
                                format_code!(generic_type.name),
                                format_code!(member_name),
                                format_code_vec(&matching_specs_names, ", "),
                            )
                            .as_str(),
                        )
                        .with_help(
                            format_code!(
                                "Consider calling the function via its type like this: {}.",
                                format!("{}.{}", matching_specs_names[0], member_name)
                            )
                            .as_str(),
                        ),
                    );

                    return Err(());
                }
            }
        }

        _ => (None, base_expr.type_key, false),
    };

    Ok((maybe_field_type_key, base_type_key, base_expr_is_ptr))
}

fn try_resolve_method(
    ctx: &mut ProgramContext,
    access: &MemberAccess,
    mut base_expr: AExpr,
    base_type_key: TypeKey,
    member_name: &String,
    base_expr_is_ptr: bool,
    base_type_string: &String,
) -> Result<(AExpr, TypeKey, bool), ()> {
    match ctx.get_or_monomorphize_member_fn(base_type_key, member_name.as_str()) {
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
                ctx.insert_err(AnalyzeError::new(
                    ErrorKind::UseOfPrivateValue,
                    format_code!("function {} is not public", member_name).as_str(),
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
                            format_code!("{} is not a method", member_name).as_str(),
                            access,
                        )
                        .with_help(
                            format_code!(
                                "Consider accessing this function via its type ({}), \
                                or add {} as the first argument to make it a method.",
                                format!("{}.{}", ctx.display_type(base_type_key), member_name),
                                "self"
                            )
                            .as_str(),
                        ),
                    );

                    return Err(());
                }

                // At this point we know it's a valid method call on a
                // concrete value. If the value is not a pointer, but the
                // method requires a pointer, then we need to implicitly
                // take a reference to the value.
                let self_arg_type_key = maybe_self_type_key.unwrap();
                let self_arg_type = ctx.must_get_type(self_arg_type_key);
                if !base_expr_is_ptr && self_arg_type.is_ptr() {
                    let op = match self_arg_type.is_mut_ptr() {
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
                } else if self_arg_type.is_mut_ptr() {
                    // Record an error here because we're trying to call
                    // a method that requires `*mut T` with only a `*T`.
                    base_expr.check_referencable_as_mut(ctx, &base_expr);
                }
            }

            Ok((base_expr, member_type_key, true))
        }

        Ok(None) => {
            // Error and return a placeholder value since we couldn't
            // locate the member being accessed.
            ctx.insert_err(AnalyzeError::new(
                ErrorKind::UndefMember,
                format_code!("type {} has no member {}", base_type_string, member_name).as_str(),
                access,
            ));

            Ok((base_expr, ctx.unknown_type_key(), false))
        }

        Err(_) => {
            // Many matching member functions were found by the given name, so this
            // reference is ambiguous.
            ctx.insert_err(
                AnalyzeError::new(
                    ErrorKind::AmbiguousAccess,
                    format_code!(
                        "ambiguous access to member {} on type {}",
                        member_name,
                        base_type_string,
                    )
                    .as_str(),
                    access,
                )
                .with_detail(
                    format_code!(
                        "There are multiple methods named {} on type {}.",
                        member_name,
                        base_type_string
                    )
                    .as_str(),
                )
                .with_help("Consider referring to the method via its type or spec."),
            );

            Ok((base_expr, ctx.unknown_type_key(), false))
        }
    }
}
