use crate::analyzer::ast::closure::AClosure;
use crate::analyzer::ast::expr::{check_operand_types, AExpr, AExprKind};
use crate::analyzer::ast::pointer::APointerType;
use crate::analyzer::ast::r#type::AType;
use crate::analyzer::error::{
    err_conflicting_patterns, err_dup_ident, err_dup_pattern, err_enum_pattern_missing_value,
    err_enum_variant_has_no_value, err_expected_enum_pattern, err_illegal_pattern_binding,
    err_inconsistent_binding_types, err_inconsistent_pattern_binding_names, err_inexhaustive_match,
    err_invalid_enum_pattern, err_invalid_pattern_expr, err_mismatched_pattern_types,
    err_type_not_struct, err_undef_enum_variant,
};
use crate::analyzer::ident::Ident;
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::scope::{Scope, ScopeKind};
use crate::analyzer::type_store::TypeKey;
use crate::analyzer::warn::warn_unreachable_case;
use crate::fmt::format_code_vec;
use crate::lexer::pos::{Locatable, Span};
use crate::parser::ast::expr::Expression;
use crate::parser::ast::op::Operator;
use crate::parser::ast::r#match::{Match, MatchCase, PatternKind};
use crate::parser::ast::r#type::Type;
use std::collections::HashSet;
use std::fmt::{Display, Formatter};

/// A pattern that appears in a `match` case.
#[derive(Debug, Clone, PartialEq)]
pub enum APattern {
    Exprs(Vec<AExpr>),
    LetEnumVariants(bool, String, TypeKey, HashSet<usize>),
    LetSymbol(bool, String),
    Wildcard,
}

impl APattern {
    fn from(
        ctx: &mut ProgramContext,
        pattern_kind: &PatternKind,
        match_target: &AExpr,
    ) -> APattern {
        match &pattern_kind {
            // Wildcard pattern `_`.
            PatternKind::Wildcard => APattern::Wildcard,

            // Arbitrary expression (to check for equality against the target).
            PatternKind::Exprs(exprs) => {
                let mut a_exprs = vec![];
                for expr in exprs {
                    let a_expr =
                        AExpr::from(ctx, expr.clone(), Some(match_target.type_key), false, false);

                    // Skip further checks if the expression already failed analysis.
                    if a_expr.type_key != ctx.unknown_type_key() {
                        // Make sure that this expression can be compared with the target for equality.
                        if let Err(errs) =
                            check_operand_types(ctx, match_target, &Operator::EqualTo, &a_expr)
                        {
                            for err in errs {
                                ctx.insert_err(err);
                            }
                        }
                    }

                    a_exprs.push(a_expr);
                }

                APattern::Exprs(a_exprs)
            }

            PatternKind::LetBinding(is_mut, exprs) => match exprs.first().unwrap() {
                Expression::Symbol(sym) if sym.is_name_only() => {
                    let mut exprs_iter = exprs.iter();
                    exprs_iter.next();

                    for expr in exprs_iter {
                        let err = err_conflicting_patterns(*expr.span());
                        ctx.insert_err(err);
                    }

                    if sym.is_wildcard() {
                        APattern::Wildcard
                    } else {
                        APattern::LetSymbol(*is_mut, sym.name.value.clone())
                    }
                }

                Expression::EnumInit(_) => {
                    let mut var_name = None;
                    let mut var_tk = None;
                    let mut variant_nums = HashSet::new();

                    for (i, expr) in exprs.iter().enumerate() {
                        analyze_enum_binding(
                            ctx,
                            expr,
                            match_target,
                            &mut var_name,
                            &mut var_tk,
                            &mut variant_nums,
                            i == 0,
                        );
                    }

                    APattern::LetEnumVariants(
                        *is_mut,
                        var_name.unwrap_or("".to_string()),
                        var_tk.unwrap_or(ctx.none_type_key()),
                        variant_nums,
                    )
                }

                expr => {
                    let err = err_invalid_pattern_expr(*expr.span());
                    ctx.insert_err(err);
                    APattern::Exprs(vec![])
                }
            },
        }
    }
}

fn analyze_enum_binding(
    ctx: &mut ProgramContext,
    binding_expr: &Expression,
    match_target: &AExpr,
    maybe_expected_var_name: &mut Option<String>,
    maybe_expected_var_tk: &mut Option<TypeKey>,
    used_variant_nums: &mut HashSet<usize>,
    is_first_pattern: bool,
) {
    let binding = match &binding_expr {
        Expression::EnumInit(binding) => binding,
        _ => {
            let err = err_expected_enum_pattern(*binding_expr.span());
            ctx.insert_err(err);
            return;
        }
    };

    let enum_tk = ctx.resolve_type(&Type::Unresolved(binding.typ.clone()));

    // Figure out how we're supposed to bind variables inside enum patterns based on
    // the target type.
    let target_type = ctx.get_type(match_target.type_key);
    let (target_tk, bind_as_ref, bind_ref_mut) = match target_type {
        AType::Pointer(ptr_type) => (ptr_type.pointee_type_key, true, ptr_type.is_mut),
        _ => (match_target.type_key, false, false),
    };

    // Make sure the enum type matches the target type.
    if enum_tk != target_tk
        && enum_tk != ctx.unknown_type_key()
        && target_tk != ctx.unknown_type_key()
    {
        let err = err_mismatched_pattern_types(ctx, enum_tk, target_tk, binding.span);
        ctx.insert_err(err);
        return;
    }

    // Resolve the enum variant.
    let enum_variant = match ctx.get_type(enum_tk) {
        AType::Enum(enum_type) => match enum_type.variants.get(&binding.variant_name) {
            Some(variant) => variant.clone(),
            None => {
                let err = err_undef_enum_variant(ctx, &binding.variant_name, enum_tk, binding.span);
                ctx.insert_err(err);
                return;
            }
        },

        _ => {
            let err = err_type_not_struct(ctx, enum_tk, binding.span);
            ctx.insert_err(err);
            return;
        }
    };

    // Make sure the variant isn't already used.
    if !used_variant_nums.insert(enum_variant.number) {
        let err = err_dup_pattern(ctx, &enum_variant, *binding_expr.span());
        ctx.insert_err(err);
        return;
    }

    // Make sure the variant type matches the match target type.
    let (expr, inner_tk) = match (&binding.maybe_value, enum_variant.maybe_type_key) {
        (Some(var), Some(variant_inner_tk)) => (var, variant_inner_tk),

        (Some(var), None) => {
            let err = err_enum_variant_has_no_value(ctx, enum_tk, &enum_variant, *var.span());
            ctx.insert_err(err);
            return;
        }

        (None, maybe_inner_tk) => {
            if maybe_inner_tk.is_some() {
                let err = err_enum_pattern_missing_value(ctx, &enum_variant, binding.span);
                ctx.insert_err(err);
            }

            return;
        }
    };

    // If the match target has a pointer type, then the bound variable should also be
    // a pointer with the same mutability. Otherwise, just use the enum inner type.
    let binding_tk = match bind_as_ref {
        true => {
            let binding_type = AType::Pointer(APointerType {
                pointee_type_key: inner_tk,
                is_mut: bind_ref_mut,
            });
            ctx.insert_type(binding_type)
        }
        false => inner_tk,
    };

    // Make sure the match variable is declared correctly.
    // TODO: Support recursive pattern matching.
    match expr.as_ref() {
        Expression::Symbol(sym) if sym.is_name_only() => {
            // No need to check anything if this is the first pattern in the match case.
            if is_first_pattern {
                if !sym.is_wildcard() {
                    *maybe_expected_var_name = Some(sym.name.value.clone());
                    *maybe_expected_var_tk = Some(binding_tk);
                }
                return;
            }

            // Make sure the variable name matches what's expected.
            match maybe_expected_var_name {
                Some(expected_var_name) if expected_var_name != &sym.name.value => {
                    let err = err_inconsistent_pattern_binding_names(expected_var_name, sym.span);
                    ctx.insert_err(err);
                    return;
                }

                None if sym.is_wildcard() => {
                    return;
                }

                None => {
                    let err = err_illegal_pattern_binding(&sym.name.value, sym.span);
                    ctx.insert_err(err);
                    return;
                }

                _ => {}
            }

            // Make sure the variable type matches what's expected.
            if maybe_expected_var_tk.unwrap() != binding_tk {
                let err = err_inconsistent_binding_types(
                    ctx,
                    &sym.name.value,
                    maybe_expected_var_tk.unwrap(),
                    binding_tk,
                    sym.name.span,
                );
                ctx.insert_err(err);
            }
        }

        other => {
            let err = err_invalid_enum_pattern(*other.span());
            ctx.insert_err(err);
        }
    }
}

/// An analyzed `match` case.
#[derive(Debug, Clone, PartialEq)]
pub struct AMatchCase {
    pub pattern: APattern,
    pub maybe_cond: Option<AExpr>,
    pub body: AClosure,
    pub ret_type_key: Option<TypeKey>,
    pub span: Span,
}

impl AMatchCase {
    fn from(ctx: &mut ProgramContext, case: &MatchCase, match_target: &AExpr) -> AMatchCase {
        // Analyze the pattern.
        let pattern = APattern::from(ctx, &case.pattern.kind, match_target);

        // Create a new scope for the rest of the case. If there's a pattern binding, we'll define
        // that as a variable in this scope.
        ctx.push_scope(Scope::new(ScopeKind::BranchBody, None));
        let maybe_ident = match &pattern {
            APattern::LetEnumVariants(is_mut, var_name, var_tk, _) if !var_name.is_empty() => Some(
                Ident::new_var(var_name.clone(), *is_mut, *var_tk, case.pattern.span),
            ),

            APattern::LetSymbol(is_mut, var_name) => Some(Ident::new_var(
                var_name.clone(),
                *is_mut,
                match_target.type_key,
                case.pattern.span,
            )),

            _ => None,
        };

        if let Some(ident) = maybe_ident {
            if let Err(existing) = ctx.insert_ident(ident) {
                let err = err_dup_ident(&existing.name, case.pattern.span, existing.span);
                ctx.insert_err(err);
            }
        }

        // Analyze the condition, if there is one.
        let maybe_cond = case.maybe_cond.as_ref().map(|cond| AExpr::from(
                ctx,
                cond.clone(),
                Some(ctx.bool_type_key()),
                false,
                false,
            ));

        // Analyze the statement.
        let body = AClosure::from(ctx, &case.body, ScopeKind::BranchBody, vec![], None);

        // Pop the scope now that we're done analyzing this match case.
        let ret_type_key = ctx.pop_scope(true).ret_type_key();

        AMatchCase {
            pattern,
            maybe_cond,
            body,
            ret_type_key,
            span: case.span,
        }
    }
}

/// An analyzed `match` statement.
#[derive(Debug, Clone)]
pub struct AMatch {
    pub target: AExpr,
    pub cases: Vec<AMatchCase>,
    pub ret_type_key: Option<TypeKey>,
    pub span: Span,
}

impl PartialEq for AMatch {
    fn eq(&self, other: &Self) -> bool {
        self.target == other.target
            && self.cases == other.cases
            && self.ret_type_key == other.ret_type_key
    }
}

impl Display for AMatch {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "match ...")
    }
}

impl AMatch {
    /// Performs semantic analysis on the given match statement.
    pub fn from(ctx: &mut ProgramContext, match_: &Match) -> AMatch {
        let target = AExpr::from(ctx, match_.target.clone(), None, false, false);
        let target_type = ctx.get_type(target.type_key).clone();

        let mut cases = vec![];
        let mut exhaustive = false;
        let mut ret_type_key = None;
        let (enum_tk, mut unmatched_variants, matching_enum) = get_variants(ctx, target.type_key);
        let mut warns = vec![];

        for case in &match_.cases {
            // If the case is unreachable, so insert a warning.
            if exhaustive {
                warns.push(warn_unreachable_case(case.span));
            }

            // Analyze the case.
            let a_case = AMatchCase::from(ctx, case, &target);

            // Update exhaustiveness info.
            match (&a_case.pattern, &a_case.maybe_cond) {
                (APattern::Wildcard, None) | (APattern::LetSymbol(_, _), None) => {
                    exhaustive = true;
                }

                (APattern::LetEnumVariants(_, _, _, variant_nums), None) => {
                    for num in variant_nums {
                        unmatched_variants.remove(num);
                    }
                    exhaustive = unmatched_variants.is_empty() && matching_enum;
                }

                (APattern::Exprs(exprs), None) if target_type.is_bool() => {
                    for expr in exprs {
                        match &expr.kind {
                            AExprKind::BoolLiteral(true) => {
                                unmatched_variants.remove(&1);
                                exhaustive = unmatched_variants.is_empty();
                            }
                            AExprKind::BoolLiteral(false) => {
                                unmatched_variants.remove(&0);
                                exhaustive = unmatched_variants.is_empty();
                            }
                            _ => {}
                        }
                    }
                }

                _ => {}
            };

            if ret_type_key.is_none() {
                ret_type_key = a_case.ret_type_key;
            }
            cases.push(a_case);
        }

        for warn in warns {
            ctx.insert_warn(warn);
        }

        if !exhaustive {
            let mut err = err_inexhaustive_match(match_.span);

            if !unmatched_variants.is_empty() && matching_enum {
                let mut variant_names = vec![];
                let enum_type = ctx.get_type(enum_tk).to_enum_type();
                for (variant_name, variant) in &enum_type.variants {
                    if unmatched_variants.contains(&variant.number) {
                        variant_names.push(variant_name.clone());
                    }
                }

                err = err.with_detail(
                    format!(
                        "The following {} variants are not fully covered: {}.",
                        format_code!(ctx.display_type(target.type_key)),
                        format_code_vec(&variant_names, ", "),
                    )
                    .as_str(),
                );
            }

            ctx.insert_err(err);
        }

        AMatch {
            target,
            cases,
            ret_type_key,
            span: match_.span,
        }
    }
}

fn get_variants(ctx: &mut ProgramContext, type_key: TypeKey) -> (TypeKey, HashSet<usize>, bool) {
    match ctx.get_type(type_key) {
        AType::Enum(enum_type) => {
            let nums =
                HashSet::from_iter(enum_type.variants.values().map(|variant| variant.number));
            (type_key, nums, true)
        }
        AType::Pointer(ptr_type) => get_variants(ctx, ptr_type.pointee_type_key),
        AType::Bool => (type_key, HashSet::from([0, 1]), false),
        _ => (type_key, HashSet::new(), false),
    }
}
