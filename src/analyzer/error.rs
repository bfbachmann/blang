use crate::analyzer::ast::expr::{AExpr, AExprKind};
use crate::analyzer::ast::fn_call::AFnCall;
use crate::analyzer::ast::func::AFnSig;
use crate::analyzer::ast::pointer::APointerType;
use crate::analyzer::ast::r#enum::AEnumTypeVariant;
use crate::analyzer::ast::symbol::ASymbol;
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::type_store::TypeKey;
use crate::fmt::{format_code_vec, hierarchy_to_string};
use crate::lexer::pos::Span;
use crate::parser::ast::member::MemberAccess;
use crate::parser::ast::op::Operator;
use crate::parser::ast::r#use::UsedModule;
use crate::parser::ast::symbol::Symbol;
use crate::parser::ast::unresolved::UnresolvedType;
use std::fmt;
use std::path::PathBuf;

pub type AnalyzeResult<T> = Result<T, AnalyzeError>;

#[derive(PartialEq, Debug, Clone, Copy)]
pub enum ErrorKind {
    MismatchedTypes,
    ExpectedReturnValue,
    ExpectedExpr,
    InvalidPattern,
    ConflictingPattern,
    InconsistentPatternBindingNames,
    InconsistentPatternBindingTypes,
    IllegalPatternBinding,
    DuplicatePattern,
    DuplicateFunction,
    InvalidConst,
    DuplicateIdentifier,
    UndefType,
    UndefSymbol,
    UndefStructField,
    UndefMod,
    DupImportedMod,
    StructFieldNotInitialized,
    UndefMember,
    SpecMemberAccess,
    AmbiguousAccess,
    DuplicateStructField,
    DuplicateEnumVariant,
    WrongNumberOfArgs,
    UnexpectedBreak,
    UnexpectedContinue,
    UnexpectedReturn,
    UnexpectedYield,
    MissingReturn,
    MissingYield,
    InvalidMain,
    InfiniteSizedType,
    InvalidStatement,
    ImmutableAssignment,
    InvalidMutRef,
    InvalidAssignmentTarget,
    UseOfPrivateValue,
    TypeIsNotStruct,
    TypeIsNotEnum,
    DuplicateSpecImpl,
    ExpectedSpec,
    DuplicateParam,
    UnexpectedParams,
    UnresolvedParams,
    WrongNumberOfParams,
    DuplicateFnArg,
    InvalidTypeCast,
    SuperfluousTypeCast,
    InvalidExtern,
    InvalidArraySize,
    IndexOutOfBounds,
    LiteralOutOfRange,
    SpecNotSatisfied,
    SpecImplMissingFns,
    ImportCycle,
    DuplicateImportName,
    IllegalImpl,
    NonSpecFnInImpl,
    IncorrectSpecFnInImpl,
    IllegalSelfArg,
    MatchNotExhaustive,
    ExpectedType,
}

/// Represents any fatal error that occurs during program analysis.
#[derive(PartialEq, Debug, Clone)]
pub struct AnalyzeError {
    pub kind: ErrorKind,
    pub message: String,
    pub detail: Option<String>,
    pub help: Option<String>,
    pub notes: Vec<Note>,
    pub span: Span,
}

#[derive(PartialEq, Debug, Clone)]
pub struct Note {
    pub message: String,
    pub span: Span,
}

impl fmt::Display for AnalyzeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl AnalyzeError {
    pub fn new(kind: ErrorKind, message: &str, span: Span) -> AnalyzeError {
        AnalyzeError {
            kind,
            message: message.to_string(),
            detail: None,
            help: None,
            notes: vec![],
            span,
        }
    }

    pub fn with_detail(mut self, detail: &str) -> AnalyzeError {
        self.detail = Some(detail.to_string());
        self
    }

    pub fn with_help(mut self, help: &str) -> AnalyzeError {
        self.help = Some(help.to_string());
        self
    }

    pub fn with_note(mut self, note: Note) -> AnalyzeError {
        self.notes.push(note);
        self
    }
}

#[must_use]
pub fn err_dup_import_alias(name: &str, span: Span, existing_span: Span) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::DuplicateImportName,
        format_code!("another import named {} already exists", name).as_str(),
        span,
    )
    .with_detail(
        format_code!(
            "The name {} used for this import is not unique in this module.",
            name
        )
        .as_str(),
    )
    .with_note(Note {
        message: format_code!("{} is also defined here", name),
        span: existing_span,
    })
}

#[must_use]
pub fn err_undef_mod_alias(name: &str, span: Span) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::UndefMod,
        format_code!("module {} is not defined", name).as_str(),
        span,
    )
}

#[must_use]
pub fn err_undef_foreign_symbol(name: &str, mod_path: &str, span: Span) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::UndefSymbol,
        format_code!("{} is not defined in module {}", name, mod_path).as_str(),
        span,
    )
}

#[must_use]
pub fn err_undef_local_symbol(name: &str, span: Span) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::UndefSymbol,
        format_code!("{} is not defined in this scope", name).as_str(),
        span,
    )
}

#[must_use]
pub fn err_not_pub(name: &str, span: Span) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::UseOfPrivateValue,
        format_code!("{} is not public", name).as_str(),
        span,
    )
}

#[must_use]
pub fn err_dup_ident(name: &str, span: Span, existing_span: Span) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::DuplicateIdentifier,
        format_code!("{} is already defined in this scope", name).as_str(),
        span,
    )
    .with_help(
        "Consider changing one of these names so they don't conflict, \
        or place these definitions in separate modules.",
    )
    .with_note(Note {
        message: format_code!("{} is already defined here.", name),
        span: existing_span,
    })
}

#[must_use]
pub fn err_invalid_extern(span: Span) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::InvalidExtern,
        format_code!("{} functions cannot be parameterized", "extern").as_str(),
        span,
    )
}

#[must_use]
pub fn err_assign_to_const(
    ctx: &ProgramContext,
    target_expr: &AExpr,
    target_name: &str,
    span: Span,
) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::ImmutableAssignment,
        format_code!("cannot assign to constant {}", target_expr.display(ctx)).as_str(),
        span,
    )
    .with_help(
        format_code!(
            "Consider declaring {} as a mutable local variable.",
            target_name
        )
        .as_str(),
    )
}

#[must_use]
pub fn err_assign_to_immut_var(
    ctx: &ProgramContext,
    target_expr: &AExpr,
    target_name: &str,
    span: Span,
) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::ImmutableAssignment,
        format_code!(
            "cannot assign to immutable variable {}",
            target_expr.display(ctx)
        )
        .as_str(),
        span,
    )
    .with_help(format_code!("Consider declaring {} as mutable.", &target_name).as_str())
}

#[must_use]
pub fn err_assign_via_immut_ptr(
    ctx: &ProgramContext,
    ptr_type: &APointerType,
    operand: &AExpr,
    span: Span,
) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::ImmutableAssignment,
        "cannot assign via pointer to immutable data",
        span,
    )
    .with_detail(
        format_code!(
            "Cannot assign via a pointer of type {} that points to an immutable value.",
            ptr_type.display(ctx),
        )
        .as_str(),
    )
    .with_help(
        format_code!(
            "For this assignment to work, {} would need to have type {}.",
            operand.display(ctx),
            format!("*mut {}", ctx.display_type(ptr_type.pointee_type_key)),
        )
        .as_str(),
    )
}

#[must_use]
pub fn err_assign_to_non_var(
    ctx: &ProgramContext,
    target_expr: &AExprKind,
    span: Span,
) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::InvalidAssignmentTarget,
        format_code!("cannot assign to non-variable {}", target_expr.display(ctx)).as_str(),
        span,
    )
}

#[must_use]
pub fn err_not_const(ctx: &ProgramContext, value: &AExpr) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::InvalidConst,
        format_code!("{} is not a constant", value.display(ctx)).as_str(),
        value.span,
    )
    .with_detail("Constant expressions cannot contain variables or function calls.")
}

#[must_use]
pub fn err_expected_type(name: &str, span: Span) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::ExpectedType,
        format_code!("{} is not a type", name).as_str(),
        span,
    )
}

#[must_use]
pub fn err_undef_type(unresolved_type: &UnresolvedType) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::UndefType,
        format_code!("type {} is not defined in this scope", unresolved_type).as_str(),
        unresolved_type.span,
    )
}

#[must_use]
pub fn err_expected_expr_found_type(
    ctx: &ProgramContext,
    type_key: TypeKey,
    span: Span,
) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::ExpectedExpr,
        format_code!(
            "expected expression, but found type {}",
            ctx.display_type(type_key)
        )
        .as_str(),
        span,
    )
}

#[must_use]
pub fn err_unresolved_params(
    ctx: &ProgramContext,
    symbol: &Symbol,
    type_key: TypeKey,
    param_names: Vec<&String>,
) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::UnresolvedParams,
        "unresolved parameters",
        symbol.span,
    )
    .with_detail(
        format!(
            "{} has polymorphic type {} which requires that types \
            be specified for parameters: {}.",
            format_code!(symbol),
            format_code!(ctx.display_type(type_key)),
            format_code_vec(&param_names, ", "),
        )
        .as_str(),
    )
}

#[must_use]
pub fn err_invalid_mod_path(mod_path: &str, span: Span) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::UndefMod,
        format_code!("no such module {}", mod_path).as_str(),
        span,
    )
}

#[must_use]
pub fn err_dup_imported_mod(used_mod: &UsedModule, existing: Span) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::DupImportedMod,
        format_code!("duplicate import {}", used_mod.path.raw).as_str(),
        used_mod.path.span,
    )
    .with_note(Note {
        message: format_code!("{} was already imported here.", used_mod.path.raw),
        span: existing,
    })
}

#[must_use]
pub fn err_invalid_statement(span: Span) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::InvalidStatement,
        "statement not allowed in this context",
        span,
    )
}

#[must_use]
pub fn err_literal_out_of_range(type_name: &str, span: Span) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::LiteralOutOfRange,
        format_code!("literal out of range for {}", type_name).as_str(),
        span,
    )
}

#[must_use]
pub fn err_invalid_type_cast(
    ctx: &ProgramContext,
    value_tk: TypeKey,
    target_tk: TypeKey,
    span: Span,
) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::InvalidTypeCast,
        format_code!(
            "cannot cast value of type {} to type {}",
            ctx.display_type(value_tk),
            ctx.display_type(target_tk)
        )
        .as_str(),
        span,
    )
}

#[must_use]
pub fn err_superfluous_type_cast(
    ctx: &ProgramContext,
    left_expr: &AExpr,
    target_tk: TypeKey,
    span: Span,
) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::SuperfluousTypeCast,
        format_code!(
            "{} already has type {}",
            left_expr.display(ctx),
            ctx.display_type(target_tk)
        )
        .as_str(),
        span,
    )
}

#[must_use]
pub fn err_expected_ret_val(ctx: &ProgramContext, call: &AFnCall, span: Span) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::ExpectedReturnValue,
        format_code!(
            "{} has no return value, but is called in an expression",
            call.display(ctx),
        )
        .as_str(),
        span,
    )
}

#[must_use]
pub fn err_invalid_from_expr(span: Span) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::InvalidStatement,
        format_code!("invalid {} expression", "from").as_str(),
        span,
    )
    .with_detail(
        format_code!(
            "The statement following {} must be a conditional, {}, {}, or closure.",
            "from",
            "match",
            "loop",
        )
        .as_str(),
    )
    .with_help(
        format_code!(
            "Consider wrapping the statement following {} in a closure.",
            "from"
        )
        .as_str(),
    )
}

#[must_use]
pub fn err_missing_return(detail: Option<&str>, span: Span) -> AnalyzeError {
    let mut err = AnalyzeError::new(
        ErrorKind::MissingReturn,
        format_code!("missing {}", "return").as_str(),
        span,
    );

    if let Some(detail_str) = detail {
        err = err.with_detail(detail_str);
    }

    err
}

#[must_use]
pub fn err_missing_yield(detail: Option<&str>, span: Span) -> AnalyzeError {
    let mut err = AnalyzeError::new(
        ErrorKind::MissingYield,
        format_code!("missing {}", "yield").as_str(),
        span,
    );

    if let Some(detail_str) = detail {
        err = err.with_detail(detail_str);
    }

    err
}

#[must_use]
pub fn err_unexpected_break(span: Span) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::UnexpectedBreak,
        format_code!("cannot {} from outside a loop", "break").as_str(),
        span,
    )
}

#[must_use]
pub fn err_unexpected_continue(span: Span) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::UnexpectedContinue,
        format_code!("cannot {} from outside a loop", "continue").as_str(),
        span,
    )
}

#[must_use]
pub fn err_unexpected_yield(span: Span) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::UnexpectedYield,
        format_code!("cannot {} from outside a {} block", "yield", "from").as_str(),
        span,
    )
}

#[must_use]
pub fn err_expected_params(ctx: &ProgramContext, type_key: TypeKey, span: Span) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::UnresolvedParams,
        "expected generic parameters",
        span,
    )
    .with_detail(
        format_code!(
            "Type {} requires generic parameters.",
            ctx.display_type(type_key)
        )
        .as_str(),
    )
}

#[must_use]
pub fn err_uninitialized_struct_fields(
    ctx: &ProgramContext,
    type_key: TypeKey,
    uninit_field_names: Vec<&str>,
    span: Span,
) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::StructFieldNotInitialized,
        format!(
            "{} {} on struct type {} {} uninitialized",
            match uninit_field_names.len() {
                1 => "field",
                _ => "fields",
            },
            format_code_vec(&uninit_field_names, ", "),
            format_code!(ctx.display_type(type_key)),
            match uninit_field_names.len() {
                1 => "is",
                _ => "are",
            },
        )
        .as_str(),
        span,
    )
}

#[must_use]
pub fn err_dup_field_assign(field_name: &str, span: Span) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::DuplicateStructField,
        format_code!("struct field {} is already assigned", field_name).as_str(),
        span,
    )
}

#[must_use]
pub fn err_type_not_struct(ctx: &ProgramContext, type_key: TypeKey, span: Span) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::TypeIsNotStruct,
        format_code!(
            "type {} is not a struct, but is being initialized like one",
            ctx.display_type(type_key)
        )
        .as_str(),
        span,
    )
}

#[must_use]
pub fn err_undef_enum_variant(
    ctx: &ProgramContext,
    variant_name: &str,
    type_key: TypeKey,
    span: Span,
) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::UndefType,
        format_code!(
            "enum type {} has no variant {}",
            ctx.display_type(type_key),
            variant_name
        )
        .as_str(),
        span,
    )
}

#[must_use]
pub fn err_undef_field(
    ctx: &ProgramContext,
    field_name: &str,
    type_key: TypeKey,
    span: Span,
) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::UndefStructField,
        format_code!(
            "struct type {} has no field {}",
            ctx.display_type(type_key),
            field_name
        )
        .as_str(),
        span,
    )
}

#[must_use]
pub fn err_dup_field_decl(struct_name: &str, field_name: &str, span: Span) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::DuplicateStructField,
        format_code!(
            "struct type {} already has a field named {}",
            struct_name,
            field_name,
        )
        .as_str(),
        span,
    )
}

#[must_use]
pub fn err_empty_return(ctx: &ProgramContext, expected_tk: TypeKey, span: Span) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::MismatchedTypes,
        format_code!(
            "expected return value of type {}, but found empty return",
            ctx.display_type(expected_tk),
        )
        .as_str(),
        span,
    )
}

#[must_use]
pub fn err_unexpected_return_val(span: Span) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::MismatchedTypes,
        "cannot return value from function with no return type",
        span,
    )
}

#[must_use]
pub fn err_unexpected_return(span: Span) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::UnexpectedReturn,
        "cannot return from outside function body",
        span,
    )
}

#[must_use]
pub fn err_dup_param(name: &str, span: Span) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::DuplicateParam,
        format_code!("parameter {} already defined", name).as_str(),
        span,
    )
}

#[must_use]
pub fn err_expected_spec(ctx: &ProgramContext, type_key: TypeKey, span: Span) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::ExpectedSpec,
        format_code!("type {} is not a spec", ctx.display_type(type_key)).as_str(),
        span,
    )
}

#[must_use]
pub fn err_ambiguous_access(
    ctx: &ProgramContext,
    base_tk: TypeKey,
    member_name: &str,
    span: Span,
) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::AmbiguousAccess,
        format_code!(
            "ambiguous access to member {} on type {}",
            member_name,
            ctx.display_type(base_tk),
        )
        .as_str(),
        span,
    )
    .with_detail(
        format_code!(
            "There are multiple methods named {} on type {}.",
            member_name,
            ctx.display_type(base_tk)
        )
        .as_str(),
    )
    .with_help("Consider referring to the method via its type or spec.")
}

#[must_use]
pub fn err_undef_member(
    ctx: &ProgramContext,
    base_tk: TypeKey,
    member_name: &str,
    span: Span,
) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::UndefMember,
        format_code!(
            "type {} has no member {}",
            ctx.display_type(base_tk),
            member_name
        )
        .as_str(),
        span,
    )
}

#[must_use]
pub fn err_member_not_method(
    ctx: &ProgramContext,
    base_tk: TypeKey,
    member_name: &str,
    span: Span,
) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::UndefMember,
        format_code!("{} is not a method", member_name).as_str(),
        span,
    )
    .with_help(
        format_code!(
            "Consider accessing this function via its type ({}), \
            or add {} as the first argument to make it a method.",
            format!("{}.{}", ctx.display_type(base_tk), member_name),
            "self"
        )
        .as_str(),
    )
}

#[must_use]
pub fn err_ambiguous_generic_member_access(
    access: &MemberAccess,
    generic_type_name: &str,
    matching_spec_names: Vec<&str>,
    member_name: &str,
    span: Span,
) -> AnalyzeError {
    AnalyzeError::new(ErrorKind::AmbiguousAccess, "ambiguous member access", span)
        .with_detail(
            format!(
                "{} is ambiguous because all of the following \
                specs used in constraints for generic type {} contain \
                functions named {}: {}.",
                format_code!(access),
                format_code!(generic_type_name),
                format_code!(member_name),
                format_code_vec(&matching_spec_names, ", "),
            )
            .as_str(),
        )
        .with_help(
            format_code!(
                "Consider calling the function via its type like this: {}.",
                format!("{}.{}", matching_spec_names[0], member_name)
            )
            .as_str(),
        )
}

#[must_use]
pub fn err_unexpected_params(ctx: &ProgramContext, member_tk: TypeKey, span: Span) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::UnexpectedParams,
        "unexpected generic parameters",
        span,
    )
    .with_detail(format_code!("Type {} is not polymorphic.", ctx.display_type(member_tk)).as_str())
}

#[must_use]
pub fn err_spec_member_access(spec_name: &str, span: Span) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::SpecMemberAccess,
        "cannot access members on spec types",
        span,
    )
    .with_detail(
        format_code!(
            "Spec types like {} contain don't have real member functions, so \
            it's impossible to access their members this way.",
            spec_name
        )
        .as_str(),
    )
}

#[must_use]
pub fn err_inexhaustive_match(span: Span) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::MatchNotExhaustive,
        "match is not exhaustive",
        span,
    )
}

#[must_use]
pub fn err_invalid_enum_pattern(span: Span) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::InvalidPattern,
        format_code!("expected identifier or wildcard {}", "_").as_str(),
        span,
    )
    .with_detail("Enum patterns can only contain identifiers or wildcards.")
}

#[must_use]
pub fn err_enum_pattern_missing_value(
    ctx: &ProgramContext,
    variant: &AEnumTypeVariant,
    span: Span,
) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::InvalidPattern,
        format_code!("expected identifier or wildcard {}", "_").as_str(),
        span,
    )
    .with_detail(
        format_code!(
            "Enum variant {} has an associated value that must \
            be bound to an identifier or wildcard in this pattern.",
            variant.display(ctx)
        )
        .as_str(),
    )
}

#[must_use]
pub fn err_inconsistent_binding_types(
    ctx: &ProgramContext,
    name: &str,
    expected_tk: TypeKey,
    binding_tk: TypeKey,
    span: Span,
) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::InconsistentPatternBindingTypes,
        "inconsistent binding types in match case",
        span,
    )
    .with_detail(
        format_code!(
            "Variable {} is bound with type {} in the first pattern, but \
            would have type {} in this binding.",
            name,
            ctx.display_type(expected_tk),
            ctx.display_type(binding_tk)
        )
        .as_str(),
    )
    .with_help("Consider moving this pattern to its own match case.")
}

#[must_use]
pub fn err_illegal_pattern_binding(name: &str, span: Span) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::IllegalPatternBinding,
        "inconsistent bindings in match case",
        span,
    )
    .with_detail(
        "No variable can be bound here because no variable is bound in \
        the first pattern for this case.",
    )
    .with_help(
        format_code!(
            "Consider either changing {} to {} or moving this pattern to its own case.",
            name,
            "_"
        )
        .as_str(),
    )
}

#[must_use]
pub fn err_inconsistent_pattern_binding_names(expected_name: &str, span: Span) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::InconsistentPatternBindingNames,
        "inconsistent bindings in match case",
        span,
    )
    .with_help(
        format_code!(
            "This variable should be bound as {} to match the binding in the \
            first pattern for this case.",
            expected_name
        )
        .as_str(),
    )
}

#[must_use]
pub fn err_enum_variant_has_no_value(
    ctx: &ProgramContext,
    enum_tk: TypeKey,
    variant: &AEnumTypeVariant,
    span: Span,
) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::MismatchedTypes,
        format_code!(
            "enum variant {} has no associated value",
            format!("{}::{}", ctx.display_type(enum_tk), variant.display(ctx),)
        )
        .as_str(),
        span,
    )
}

#[must_use]
pub fn err_dup_pattern(
    ctx: &ProgramContext,
    variant: &AEnumTypeVariant,
    span: Span,
) -> AnalyzeError {
    AnalyzeError::new(ErrorKind::DuplicatePattern, "duplicate pattern", span).with_detail(
        format_code!(
            "Variant {} is already used in this match case.",
            variant.display(ctx),
        )
        .as_str(),
    )
}

#[must_use]
pub fn err_mismatched_pattern_types(
    ctx: &ProgramContext,
    enum_tk: TypeKey,
    target_tk: TypeKey,
    span: Span,
) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::MismatchedTypes,
        format_code!(
            "expected pattern of type {}, but found {}",
            ctx.display_type(target_tk),
            ctx.display_type(enum_tk)
        )
        .as_str(),
        span,
    )
}

#[must_use]
pub fn err_expected_enum_pattern(span: Span) -> AnalyzeError {
    AnalyzeError::new(ErrorKind::InvalidPattern, "expected enum variant", span).with_detail(
        "The first pattern in this case is an enum variant, so all \
            following patterns must also be enum variants.",
    )
}

#[must_use]
pub fn err_invalid_pattern_expr(span: Span) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::InvalidPattern,
        "invalid pattern expression",
        span,
    )
    .with_detail("This expression is not valid inside a pattern.")
    .with_help(
        format_code!(
            "If you're trying to match against an existing value, remove {} from \
            this case.",
            "let"
        )
        .as_str(),
    )
}

#[must_use]
pub fn err_conflicting_patterns(span: Span) -> AnalyzeError {
    AnalyzeError::new(ErrorKind::ConflictingPattern, "conflicting patterns", span)
        .with_detail("Variable binding patterns must appear alone in match cases.")
}

#[must_use]
pub fn err_mismatched_index_type(
    ctx: &ProgramContext,
    is_const: bool,
    type_key: TypeKey,
    span: Span,
) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::MismatchedTypes,
        format!(
            "expected constant of type {}, but found {}{}",
            format_code!("uint"),
            match is_const {
                true => "",
                false => "non-constant ",
            },
            ctx.display_type(type_key)
        )
        .as_str(),
        span,
    )
    .with_detail(
        format_code!(
            "Tuple indices must be {} values that are known at compile time.",
            "unit"
        )
        .as_str(),
    )
}

#[must_use]
pub fn err_index_out_of_bounds(i: u64, len: u64, span: Span) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::IndexOutOfBounds,
        format!("index {} is out of bounds (0:{})", i, len - 1).as_str(),
        span,
    )
}

#[must_use]
pub fn err_index_empty_array(span: Span) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::IndexOutOfBounds,
        "cannot index zero-length array",
        span,
    )
}

#[must_use]
pub fn err_cannot_index_value(ctx: &ProgramContext, type_key: TypeKey, span: Span) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::MismatchedTypes,
        format_code!("cannot index value of type {}", ctx.display_type(type_key)).as_str(),
        span,
    )
}

#[must_use]
pub fn err_non_spec_impl(
    ctx: &ProgramContext,
    spec_name: &str,
    fn_name: &str,
    type_key: TypeKey,
    span: Span,
) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::NonSpecFnInImpl,
        format_code!("function {} is not defined in spec {}", fn_name, spec_name).as_str(),
        span,
    )
    .with_detail(
        format_code!(
            "Spec {} does not contain a function named {}, so it should not appear \
            in this {} block.",
            spec_name,
            fn_name,
            "impl",
        )
        .as_str(),
    )
    .with_help(
        format_code!(
            "Consider moving function {} to a default {} block.",
            fn_name,
            format!("impl {}", ctx.display_type(type_key))
        )
        .as_str(),
    )
}

#[must_use]
pub fn err_incorrect_spec_fn(
    ctx: &ProgramContext,
    spec_tk: TypeKey,
    spec_fn_sig: &AFnSig,
    span: Span,
) -> AnalyzeError {
    let spec_name = ctx.display_type(spec_tk);

    AnalyzeError::new(
        ErrorKind::IncorrectSpecFnInImpl,
        format_code!(
            "{} is implemented incorrectly for spec {}",
            spec_fn_sig.name,
            spec_name
        )
        .as_str(),
        span,
    )
    .with_detail(format_code!("Spec {} expects {}.", spec_name, spec_fn_sig.display(ctx),).as_str())
    .with_note(Note {
        message: format_code!("{} is defined here.", spec_fn_sig.name),
        span: spec_fn_sig.span,
    })
}

#[must_use]
pub fn err_spec_impl_missing_fns(
    spec_name: &str,
    missing_fn_names: &Vec<String>,
    span: Span,
) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::SpecImplMissingFns,
        format_code!("spec {} not fully implemented", spec_name).as_str(),
        span,
    )
    .with_detail(
        format!(
            "The following functions from spec {} are missing: {}.",
            format_code!(spec_name),
            format_code_vec(&missing_fn_names, ", "),
        )
        .as_str(),
    )
}

#[must_use]
pub fn err_dup_fn_arg(name: &str, span: Span) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::DuplicateFnArg,
        format_code!(
            "another argument named {} already exists for this function",
            name
        )
        .as_str(),
        span,
    )
}

#[must_use]
pub fn err_illegal_self_arg(span: Span) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::IllegalSelfArg,
        format_code!(
            "cannot declare argument {} outside of {} or {} block",
            "self",
            "spec",
            "impl"
        )
        .as_str(),
        span,
    )
}

#[must_use]
pub fn err_misplaced_self_arg(span: Span) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::IllegalSelfArg,
        format!("{} must always be the first argument, if present", "self",).as_str(),
        span,
    )
}

#[must_use]
pub fn err_illegal_foreign_type_impl(
    ctx: &ProgramContext,
    type_key: TypeKey,
    span: Span,
) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::IllegalImpl,
        format_code!(
            "cannot define {} for foreign type {}",
            "impl",
            ctx.display_type(type_key)
        )
        .as_str(),
        span,
    )
}

#[must_use]
pub fn err_illegal_foreign_spec_impl(
    ctx: &ProgramContext,
    spec_tk: TypeKey,
    type_key: TypeKey,
    span: Span,
) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::IllegalImpl,
        format_code!(
            "cannot implement foreign spec {} for foreign type {}",
            ctx.display_type(spec_tk),
            ctx.display_type(type_key)
        )
        .as_str(),
        span,
    )
    .with_detail(
        "Either the type or the spec being implemented must be \
        defined in this module.",
    )
}

#[must_use]
pub fn err_spec_not_satisfied(
    ctx: &ProgramContext,
    actual_tk: TypeKey,
    missing_spec_names: &Vec<String>,
    param_name: &str,
    parent_tk: TypeKey,
    span: Span,
) -> AnalyzeError {
    let actual_type_str = ctx.display_type(actual_tk);
    let parent_type_str = ctx.display_type(parent_tk);

    AnalyzeError::new(
        ErrorKind::SpecNotSatisfied,
        format_code!("type {} violates parameter constraints", actual_type_str).as_str(),
        span,
    )
    .with_detail(
        format!(
            "{} does not implement spec{} {} required by parameter {} in {}.",
            format_code!(actual_type_str),
            match missing_spec_names.len() {
                1 => "",
                _ => "s",
            },
            format_code_vec(&missing_spec_names, ", "),
            format_code!(param_name),
            format_code!(parent_type_str),
        )
        .as_str(),
    )
}

#[must_use]
pub fn err_mismatched_types(
    ctx: &ProgramContext,
    expected_tk: TypeKey,
    actual_tk: TypeKey,
    span: Span,
) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::MismatchedTypes,
        format_code!(
            "expected expression of type {}, but found {}",
            ctx.display_type(expected_tk),
            ctx.display_type(actual_tk)
        )
        .as_str(),
        span,
    )
}

#[must_use]
pub fn err_wrong_num_args(
    ctx: &ProgramContext,
    expected_args: usize,
    actual_args: usize,
    fn_sig: &AFnSig,
    span: Span,
) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::WrongNumberOfArgs,
        format!(
            "{} expects {} argument{}, but found {}",
            format_code!("{}", fn_sig.display(ctx)),
            expected_args,
            match expected_args {
                1 => "",
                _ => "s",
            },
            actual_args
        )
        .as_str(),
        span,
    )
}

#[must_use]
pub fn err_not_callable(ctx: &ProgramContext, type_key: TypeKey, span: Span) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::MismatchedTypes,
        format_code!("type {} is not callable", ctx.display_type(type_key)).as_str(),
        span,
    )
}

#[must_use]
pub fn err_type_annotations_needed(
    ctx: &ProgramContext,
    type_key: TypeKey,
    span: Span,
) -> AnalyzeError {
    AnalyzeError::new(ErrorKind::UnresolvedParams, "type annotations needed", span).with_detail(
        format_code!(
            "This expression has polymorphic type {}, \
            but it's not clear how to monomorphize it here without additional \
            type annotations.",
            ctx.display_type(type_key)
        )
        .as_str(),
    )
}

#[must_use]
pub fn err_invalid_mut_ref_const(symbol: &ASymbol, span: Span) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::InvalidMutRef,
        format_code!("cannot mutably reference constant value {}", symbol).as_str(),
        span,
    )
    .with_help(format_code!("Consider declaring {} as a mutable local variable.", symbol).as_str())
}

#[must_use]
pub fn err_invalid_mut_ref_fn(symbol: &ASymbol, span: Span) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::InvalidMutRef,
        format_code!("cannot mutably reference function {}", symbol).as_str(),
        span,
    )
}

#[must_use]
pub fn err_invalid_mut_ref_immut(symbol: &ASymbol, span: Span) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::InvalidMutRef,
        format_code!("cannot mutably reference immutable variable {}", symbol).as_str(),
        span,
    )
    .with_help(format_code!("Consider declaring {} as mutable.", symbol).as_str())
}

#[must_use]
pub fn err_mismatched_operand_types(
    ctx: &ProgramContext,
    op: &Operator,
    left_tk: TypeKey,
    right_tk: TypeKey,
    span: Span,
) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::MismatchedTypes,
        format_code!(
            "{} operands have mismatched types {} and {}",
            op,
            ctx.display_type(left_tk),
            ctx.display_type(right_tk),
        )
        .as_str(),
        span,
    )
}

#[must_use]
pub fn err_invalid_operand_type(
    ctx: &ProgramContext,
    op: &Operator,
    type_key: TypeKey,
    is_left: bool,
    span: Span,
) -> AnalyzeError {
    let side = match is_left {
        true => "left",
        false => "right",
    };

    AnalyzeError::new(
        ErrorKind::MismatchedTypes,
        format!(
            "cannot apply operator {} to {side}-side expression of type {}",
            format_code!(&op),
            format_code!(ctx.display_type(type_key)),
        )
        .as_str(),
        span,
    )
}

#[must_use]
pub fn err_invalid_unary_operand_type(
    ctx: &ProgramContext,
    type_key: TypeKey,
    span: Span,
) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::MismatchedTypes,
        format_code!(
            "unary operator {} cannot be applied to value of type {}",
            "!",
            ctx.display_type(type_key),
        )
        .as_str(),
        span,
    )
}

#[must_use]
pub fn err_cannot_deref_value(ctx: &ProgramContext, type_key: TypeKey, span: Span) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::MismatchedTypes,
        format_code!(
            "cannot dereference value of type {}",
            ctx.display_type(type_key)
        )
        .as_str(),
        span,
    )
}

#[must_use]
pub fn err_cannot_negate_value(
    ctx: &ProgramContext,
    type_key: TypeKey,
    is_numeric: bool,
    span: Span,
) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::MismatchedTypes,
        format!(
            "cannot negate value of {} type {}",
            match is_numeric {
                false => "non-numeric",
                true => "unsigned",
            },
            format_code!(ctx.display_type(type_key))
        )
        .as_str(),
        span,
    )
}

#[must_use]
pub fn err_cannot_bitwise_neg_value(
    ctx: &ProgramContext,
    type_key: TypeKey,
    span: Span,
) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::MismatchedTypes,
        format!(
            "cannot bitwise negate value of non-integer type {}",
            format_code!(ctx.display_type(type_key))
        )
        .as_str(),
        span,
    )
}

#[must_use]
pub fn err_missing_variant_value(
    ctx: &ProgramContext,
    variant: &AEnumTypeVariant,
    type_key: TypeKey,
    enum_name: &str,
    span: Span,
) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::MismatchedTypes,
        format_code!(
            "missing value of type {} for variant {} of enum {}",
            ctx.display_type(type_key),
            variant.display(ctx),
            enum_name
        )
        .as_str(),
        span,
    )
}

#[must_use]
pub fn err_unexpected_variant_value(
    ctx: &ProgramContext,
    variant: &AEnumTypeVariant,
    enum_name: &str,
    span: Span,
) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::MismatchedTypes,
        format_code!(
            "variant {} of enum {} has no associated type, but a value was provided",
            variant.display(ctx),
            enum_name,
        )
        .as_str(),
        span,
    )
}

#[must_use]
pub fn err_no_such_variant(
    ctx: &ProgramContext,
    type_key: TypeKey,
    variant_name: &str,
    span: Span,
) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::UndefType,
        format_code!(
            "enum type {} has no variant {}",
            ctx.display_type(type_key),
            variant_name
        )
        .as_str(),
        span,
    )
}

#[must_use]
pub fn err_expected_enum(ctx: &ProgramContext, type_key: TypeKey, span: Span) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::TypeIsNotEnum,
        format_code!(
            "type {} is not an enum, but is being used like one",
            ctx.display_type(type_key)
        )
        .as_str(),
        span,
    )
}

#[must_use]
pub fn err_dup_enum_variant(enum_name: &str, variant_name: &str, span: Span) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::DuplicateEnumVariant,
        format_code!(
            "enum type {} already has a variant named {}",
            enum_name,
            variant_name
        )
        .as_str(),
        span,
    )
}

#[must_use]
pub fn err_invalid_array_size_type(span: Span) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::InvalidArraySize,
        format_code!("expected constant of type {}", "uint").as_str(),
        span,
    )
}

#[must_use]
pub fn err_type_already_implements_spec(
    ctx: &ProgramContext,
    type_key: TypeKey,
    spec_tk: TypeKey,
    span: Span,
) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::DuplicateSpecImpl,
        format_code!(
            "{} already implements {}",
            ctx.display_type(type_key),
            ctx.display_type(spec_tk),
        )
        .as_str(),
        span,
    )
}

#[must_use]
pub fn err_dup_impl_fn(name: &str, span: Span) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::DuplicateFunction,
        format_code!("function {} already defined in this {}", name, "impl",).as_str(),
        span,
    )
}

#[must_use]
pub fn err_dup_mem_fn(
    ctx: &ProgramContext,
    name: &str,
    impl_tk: TypeKey,
    span: Span,
) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::DuplicateFunction,
        format_code!(
            "function {} already defined for type {}",
            name,
            ctx.display_type(impl_tk),
        )
        .as_str(),
        span,
    )
}

#[must_use]
pub fn err_import_cycle(used_mod: &UsedModule, cycle: &Vec<PathBuf>) -> AnalyzeError {
    let mod_chain = hierarchy_to_string(
        &cycle
            .iter()
            .map(|p| p.to_str().unwrap().to_string())
            .collect(),
    );

    AnalyzeError::new(ErrorKind::ImportCycle, "import cycle", used_mod.path.span)
        .with_detail(format!("The offending import chain is: {}", mod_chain).as_str())
}
