use std::fmt;
use std::fmt::Formatter;

use colored::Colorize;

use crate::analyzer::ast::array::AArrayInit;
use crate::analyzer::ast::closure::AClosure;
use crate::analyzer::ast::fn_call::AFnCall;
use crate::analyzer::ast::func::{AFn, AFnSig};
use crate::analyzer::ast::pointer::APointerType;
use crate::analyzer::ast::r#enum::{AEnumTypeVariant, AEnumVariantInit};
use crate::analyzer::ast::r#struct::AStructInit;
use crate::analyzer::ast::r#type::AType;
use crate::analyzer::ast::symbol::{AMemberAccess, ASymbol};
use crate::analyzer::ast::tuple::ATupleInit;
use crate::analyzer::error::{AnalyzeError, AnalyzeResult, ErrorKind};
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::scope::ScopeKind;
use crate::analyzer::type_store::TypeKey;
use crate::lexer::pos::{Locatable, Position};
use crate::parser::ast::expr::Expression;
use crate::parser::ast::op::Operator;
use crate::parser::ast::r#type::Type;
use crate::parser::ast::unresolved::UnresolvedType;
use crate::{format_code, locatable_impl};

/// Represents a kind of expression.
#[derive(Debug, Clone)]
pub enum AExprKind {
    Symbol(ASymbol),
    BoolLiteral(bool),
    /// The bool here will be true if this literal includes an explicit type suffix.
    I64Literal(i64, bool),
    /// The bool here will be true if this literal includes an explicit type suffix.
    U64Literal(u64, bool),
    StrLiteral(String),
    StructInit(AStructInit),
    EnumInit(AEnumVariantInit),
    TupleInit(ATupleInit),
    ArrayInit(AArrayInit),
    FunctionCall(AFnCall),
    AnonFunction(Box<AFn>),
    UnaryOperation(Operator, Box<AExpr>),
    BinaryOperation(Box<AExpr>, Operator, Box<AExpr>),
    TypeCast(Box<AExpr>, TypeKey),
    Unknown,
}

impl fmt::Display for AExprKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            AExprKind::Symbol(sym) => write!(f, "{}", sym),
            AExprKind::BoolLiteral(b) => write!(f, "{}", b),
            AExprKind::I64Literal(i, has_suffix) => {
                write!(f, "{}{}", i, if *has_suffix { "i64" } else { "" })
            }
            AExprKind::U64Literal(i, has_suffix) => {
                write!(f, "{}{}", i, if *has_suffix { "u64" } else { "" })
            }
            AExprKind::StrLiteral(s) => write!(f, "{}", s),
            AExprKind::StructInit(s) => write!(f, "{}", s),
            AExprKind::EnumInit(e) => write!(f, "{}", e),
            AExprKind::TupleInit(t) => write!(f, "{}", t),
            AExprKind::ArrayInit(a) => write!(f, "{}", a),
            AExprKind::FunctionCall(call) => write!(f, "{}", call),
            AExprKind::AnonFunction(func) => write!(f, "{}", *func),
            AExprKind::UnaryOperation(op, expr) => write!(f, "{} {}", op, expr),
            AExprKind::BinaryOperation(left, op, right) => {
                write!(f, "{} {} {}", left, op, right)
            }
            AExprKind::TypeCast(expr, target_type_key) => {
                write!(f, "{} as {}", expr, target_type_key)
            }
            AExprKind::Unknown => {
                write!(f, "<unknown>")
            }
        }
    }
}

impl PartialEq for AExprKind {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (AExprKind::Symbol(v1), AExprKind::Symbol(v2)) => v1 == v2,
            (AExprKind::BoolLiteral(b1), AExprKind::BoolLiteral(b2)) => b1 == b2,
            (AExprKind::I64Literal(i1, _), AExprKind::I64Literal(i2, _)) => i1 == i2,
            (AExprKind::U64Literal(i1, _), AExprKind::U64Literal(i2, _)) => i1 == i2,
            (AExprKind::StrLiteral(s1), AExprKind::StrLiteral(s2)) => s1 == s2,
            (AExprKind::StructInit(s1), AExprKind::StructInit(s2)) => s1 == s2,
            (AExprKind::EnumInit(e1), AExprKind::EnumInit(e2)) => e1 == e2,
            (AExprKind::TupleInit(t1), AExprKind::TupleInit(t2)) => t1 == t2,
            (AExprKind::ArrayInit(a1), AExprKind::ArrayInit(a2)) => a1 == a2,
            (AExprKind::FunctionCall(f1), AExprKind::FunctionCall(f2)) => f1 == f2,
            (AExprKind::AnonFunction(a1), AExprKind::AnonFunction(a2)) => a1 == a2,
            (AExprKind::UnaryOperation(o1, e1), AExprKind::UnaryOperation(o2, e2)) => {
                o1 == o2 && e1 == e2
            }
            (AExprKind::BinaryOperation(l1, o1, r1), AExprKind::BinaryOperation(l2, o2, r2)) => {
                l1 == l2 && o1 == o2 && r1 == r2
            }
            (AExprKind::Unknown, AExprKind::Unknown) => true,
            (_, _) => false,
        }
    }
}

impl AExprKind {
    /// Returns true if the expression kind can be used as a constant.
    pub fn is_const(&self) -> bool {
        match self {
            // Primitive literals are valid constants.
            AExprKind::BoolLiteral(_)
            | AExprKind::I64Literal(_, _)
            | AExprKind::U64Literal(_, _)
            | AExprKind::StrLiteral(_) => true,

            // Unary and binary operations are constants if they only operate on constants and have
            // valid constant operators.
            AExprKind::UnaryOperation(op, expr) => expr.kind.is_const() && op.is_const(),
            AExprKind::BinaryOperation(left_expr, op, right_expr) => {
                left_expr.kind.is_const() && right_expr.kind.is_const() && op.is_const()
            }

            // Struct initializations are constants if all their fields are constants.
            AExprKind::StructInit(struct_init) => {
                for (_, field_val) in &struct_init.field_values {
                    if !field_val.kind.is_const() {
                        return false;
                    }
                }

                true
            }

            // Enum variant initializations are constants if they have no values or their values
            // are constants.
            AExprKind::EnumInit(enum_init) => {
                if let Some(val) = &enum_init.maybe_value {
                    if !val.kind.is_const() {
                        return false;
                    }
                }

                true
            }

            // Tuple values are constants if all their fields are constants.
            AExprKind::TupleInit(tuple_init) => {
                for val in &tuple_init.values {
                    if !val.kind.is_const() {
                        return false;
                    }
                }

                true
            }

            // Array values are constants if all their fields are constants.
            AExprKind::ArrayInit(array_init) => {
                for val in &array_init.values {
                    if !val.kind.is_const() {
                        return false;
                    }
                }

                true
            }

            // Symbols can be constants.
            AExprKind::Symbol(sym) => sym.is_const,

            // Function calls and unknown values are never constants.
            AExprKind::FunctionCall(_) | AExprKind::AnonFunction(_) | AExprKind::Unknown => false,

            // Type cast expressions are constants if the expressions they're type casting are
            // constants.
            AExprKind::TypeCast(expr, _) => expr.kind.is_const(),
        }
    }

    /// Returns the human-readable version of this expression kind.
    pub fn display(&self, ctx: &ProgramContext) -> String {
        match self {
            AExprKind::Symbol(sym) => format!("{}", sym),
            AExprKind::BoolLiteral(b) => format!("{}", b),
            AExprKind::I64Literal(i, _) => format!("{}", i),
            AExprKind::U64Literal(i, _) => format!("{}", i),
            AExprKind::StrLiteral(s) => format!("{}", s),
            AExprKind::StructInit(s) => s.display(ctx),
            AExprKind::EnumInit(e) => e.display(ctx),
            AExprKind::TupleInit(t) => t.display(ctx),
            AExprKind::ArrayInit(a) => a.display(ctx),
            AExprKind::FunctionCall(call) => call.display(ctx),
            AExprKind::AnonFunction(func) => func.display(ctx),
            AExprKind::UnaryOperation(op, expr) => format!("{} {}", op, expr.display(ctx)),
            AExprKind::BinaryOperation(left, op, right) => {
                format!("{} {} {}", left.display(ctx), op, right.display(ctx))
            }
            AExprKind::TypeCast(left_expr, target_type_key) => {
                format!(
                    "{} as {}",
                    left_expr.display(ctx),
                    ctx.display_type_for_key(*target_type_key)
                )
            }
            AExprKind::Unknown => {
                format!("<unknown>")
            }
        }
    }

    /// Returns true if this expression kind is a symbol.
    pub fn is_symbol(&self) -> bool {
        matches!(self, AExprKind::Symbol(_))
    }
}

/// Represents a semantically valid and type-rich expression.
#[derive(Clone, PartialEq, Debug)]
pub struct AExpr {
    pub kind: AExprKind,
    pub type_key: TypeKey,
    start_pos: Position,
    end_pos: Position,
}

impl fmt::Display for AExpr {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.kind)
    }
}

locatable_impl!(AExpr);

impl AExpr {
    /// Performs semantic analysis on the given expression and returns a type-rich version of it.
    /// `maybe_expected_type_key` is the optional type key of the expected type that this expression
    /// should have.
    /// If `allow_templated_result` is false, this function will check that the resulting expression
    /// type is not templated and record an error if it is. Otherwise, templated result types will
    /// be allowed.
    pub fn from(
        ctx: &mut ProgramContext,
        expr: Expression,
        maybe_expected_type_key: Option<TypeKey>,
        allow_templated_result: bool,
    ) -> AExpr {
        let start_pos = expr.start_pos().clone();
        let end_pos = expr.end_pos().clone();

        let mut result = match &expr {
            Expression::TypeCast(expr, target_type) => {
                let left_expr = AExpr::from(ctx, *expr.clone(), None, false);
                let target_type_key = ctx.resolve_type(target_type);
                let left_type = ctx.must_get_type(left_expr.type_key);
                let a_target_type = ctx.must_get_type(target_type_key);

                // Skip the check if the left expression already failed analysis.
                if !left_type.is_unknown() && !is_valid_type_cast(left_type, a_target_type) {
                    ctx.insert_err(AnalyzeError::new(
                        ErrorKind::InvalidTypeCast,
                        format_code!(
                            "cannot cast value of type {} to type {}",
                            left_type.display(ctx),
                            a_target_type.display(ctx)
                        )
                        .as_str(),
                        &left_expr,
                    ));

                    AExpr::new_zero_value(ctx, target_type.clone())
                } else {
                    AExpr {
                        kind: AExprKind::TypeCast(Box::new(left_expr), target_type_key),
                        type_key: target_type_key,
                        start_pos,
                        end_pos,
                    }
                }
            }

            Expression::Symbol(ref symbol) => {
                let a_symbol = ASymbol::from(ctx, symbol, true, None);
                let type_key = a_symbol.get_type_key().clone();
                AExpr {
                    kind: AExprKind::Symbol(a_symbol),
                    type_key,
                    start_pos,
                    end_pos,
                }
            }

            Expression::BoolLiteral(b) => AExpr {
                kind: AExprKind::BoolLiteral(b.value),
                type_key: ctx.bool_type_key(),
                start_pos,
                end_pos,
            },

            Expression::I64Literal(i) => AExpr {
                kind: AExprKind::I64Literal(i.value, i.has_type_suffix),
                type_key: ctx.i64_type_key(),
                start_pos,
                end_pos,
            },

            Expression::U64Literal(i) => AExpr {
                kind: AExprKind::U64Literal(i.value, i.has_type_suffix),
                type_key: ctx.u64_type_key(),
                start_pos,
                end_pos,
            },

            Expression::StrLiteral(s) => AExpr {
                kind: AExprKind::StrLiteral(s.value.clone()),
                type_key: ctx.str_type_key(),
                start_pos,
                end_pos,
            },

            Expression::StructInit(struct_init) => {
                let a_init = AStructInit::from(ctx, &struct_init);
                let type_key = a_init.type_key;
                AExpr {
                    kind: AExprKind::StructInit(a_init),
                    type_key,
                    start_pos,
                    end_pos,
                }
            }

            Expression::EnumInit(enum_init) => {
                let a_init = AEnumVariantInit::from(ctx, &enum_init);
                let type_key = a_init.type_key;
                AExpr {
                    kind: AExprKind::EnumInit(a_init),
                    type_key,
                    start_pos,
                    end_pos,
                }
            }

            Expression::TupleInit(tuple_init) => {
                let maybe_expected_field_type_keys = match maybe_expected_type_key {
                    Some(tk) => {
                        if let AType::Tuple(tuple_type) = ctx.must_get_type(tk) {
                            let mut field_type_keys = Vec::with_capacity(tuple_type.fields.len());
                            for i in 0..tuple_type.fields.len() {
                                field_type_keys
                                    .insert(i, tuple_type.get_field_type_key(i).unwrap());
                            }

                            Some(field_type_keys)
                        } else {
                            None
                        }
                    }
                    None => None,
                };

                let a_init = ATupleInit::from(ctx, &tuple_init, maybe_expected_field_type_keys);
                let type_key = a_init.type_key;
                AExpr {
                    kind: AExprKind::TupleInit(a_init),
                    type_key,
                    start_pos,
                    end_pos,
                }
            }

            Expression::ArrayInit(array_init) => {
                let maybe_element_type_key = match maybe_expected_type_key {
                    Some(tk) => {
                        if let AType::Array(array_type) = ctx.must_get_type(tk) {
                            array_type.maybe_element_type_key
                        } else {
                            None
                        }
                    }
                    None => None,
                };

                let a_init = AArrayInit::from(ctx, &array_init, maybe_element_type_key);
                let type_key = a_init.type_key;
                AExpr {
                    kind: AExprKind::ArrayInit(a_init),
                    type_key,
                    start_pos,
                    end_pos,
                }
            }

            Expression::SizeOf(sizeof) => {
                // Get the size of the type and just represent it as a u64 literal.
                let type_key = ctx.resolve_type(&sizeof.typ);
                let typ = ctx.must_get_type(type_key);
                AExpr {
                    kind: AExprKind::U64Literal(typ.size_bytes(ctx) as u64, false),
                    type_key: ctx.u64_type_key(),
                    start_pos,
                    end_pos,
                }
            }

            Expression::FunctionCall(fn_call) => {
                // Analyze the function call and ensure it has a return type.
                let a_call = AFnCall::from(ctx, fn_call);
                if let Some(type_key) = a_call.maybe_ret_type_key.clone() {
                    return AExpr {
                        kind: AExprKind::FunctionCall(a_call),
                        type_key,
                        start_pos,
                        end_pos,
                    };
                }

                // The function does not have a return value. Record the error and return some
                // some zero-value instead.
                ctx.insert_err(AnalyzeError::new(
                    ErrorKind::ExpectedReturnValue,
                    format_code!(
                        "function {} has no return value, but is called in an expression \
                        where a return value is expected",
                        &fn_call.fn_symbol,
                    )
                    .as_str(),
                    fn_call,
                ));

                AExpr::new_zero_value(ctx, Type::Unresolved(UnresolvedType::unresolved_none()))
            }

            Expression::AnonFunction(anon_fn) => {
                let sig = anon_fn.signature.clone();
                let a_closure = AClosure::from(
                    ctx,
                    &anon_fn.body,
                    ScopeKind::FnBody,
                    sig.args.clone(),
                    sig.maybe_ret_type.clone(),
                );
                let type_key = ctx.resolve_type(&Type::Function(Box::new(sig)));

                AExpr {
                    start_pos,
                    end_pos,
                    kind: AExprKind::AnonFunction(Box::new(AFn {
                        signature: AFnSig::from(ctx, &anon_fn.signature),
                        body: a_closure,
                    })),
                    type_key,
                }
            }

            Expression::Lambda(_) => {
                todo!();
            }

            Expression::UnaryOperation(ref op, ref right_expr) => {
                match op {
                    Operator::LogicalNot => {
                        let a_expr =
                            AExpr::from(ctx, *right_expr.clone(), Some(ctx.bool_type_key()), false);

                        // Make sure the expression has type bool.
                        if !ctx.must_get_type(a_expr.type_key).is_bool() {
                            ctx.insert_err(AnalyzeError::new(
                                ErrorKind::MismatchedTypes,
                                format_code!(
                                    "unary operator {} cannot be applied to value of type {}",
                                    "!",
                                    a_expr.display(ctx),
                                )
                                .as_str(),
                                &expr,
                            ));

                            AExpr::new_zero_value(ctx, Type::new_unresolved("bool"))
                        } else {
                            AExpr {
                                type_key: a_expr.type_key,
                                kind: AExprKind::UnaryOperation(
                                    Operator::LogicalNot,
                                    Box::new(a_expr),
                                ),
                                start_pos,
                                end_pos,
                            }
                        }
                    }

                    Operator::Reference => {
                        let operand_expr = AExpr::from(ctx, *right_expr.clone(), None, false);
                        let a_ptr_type = APointerType::new(operand_expr.type_key);
                        let type_key = ctx.insert_type(AType::Pointer(a_ptr_type));

                        AExpr {
                            type_key,
                            kind: AExprKind::UnaryOperation(
                                Operator::Reference,
                                Box::new(operand_expr),
                            ),
                            start_pos,
                            end_pos,
                        }
                    }

                    Operator::Defererence => {
                        let operand_expr = AExpr::from(ctx, *right_expr.clone(), None, false);
                        let operand_expr_type = ctx.must_get_type(operand_expr.type_key);

                        // Make sure the operand expression is of a pointer type.
                        match operand_expr_type {
                            AType::Pointer(ptr_type) => AExpr {
                                type_key: ptr_type.pointee_type_key,
                                kind: AExprKind::UnaryOperation(
                                    Operator::Defererence,
                                    Box::new(operand_expr),
                                ),
                                start_pos,
                                end_pos,
                            },

                            other => {
                                // Don't display a redundant error if the operand expression already
                                // failed analysis.
                                if !other.is_unknown() {
                                    ctx.insert_err(AnalyzeError::new(
                                        ErrorKind::MismatchedTypes,
                                        format_code!(
                                            "cannot dereference value of non-pointer type {}",
                                            other.display(ctx)
                                        )
                                        .as_str(),
                                        &expr,
                                    ));
                                }

                                AExpr::new_null_ptr(ctx)
                            }
                        }
                    }

                    _ => {
                        panic!("unexpected unary operator {}", op)
                    }
                }
            }

            Expression::BinaryOperation(ref left_expr, ref op, ref right_expr) => {
                let maybe_expected_operand_tk = match maybe_expected_type_key {
                    Some(tk) => get_expected_operand_type_key(ctx, op, tk),
                    None => None,
                };

                let a_left = AExpr::from(ctx, *left_expr.clone(), maybe_expected_operand_tk, false);
                // If there is no expected operand type, we should try to coerce the right
                // expression to the type of the left expression.
                let expected_tk = maybe_expected_operand_tk.unwrap_or(a_left.type_key);
                let a_right = AExpr::from(ctx, *right_expr.clone(), Some(expected_tk), false);

                // If we couldn't resolve both of the operand types, we'll skip any further
                // type checks by returning early.
                let left_type = ctx.must_get_type(a_left.type_key);
                let right_type = ctx.must_get_type(a_right.type_key);
                if left_type.is_unknown() || right_type.is_unknown() {
                    return AExpr {
                        kind: AExprKind::BinaryOperation(
                            Box::new(a_left.clone()),
                            op.clone(),
                            Box::new(a_right),
                        ),
                        type_key: get_result_type(ctx, op, None),
                        start_pos,
                        end_pos,
                    };
                }

                // Check that the operands are compatible with the operator and one another.
                let (maybe_operand_type_key, errors) =
                    match check_operand_types(ctx, &a_left, op, &a_right) {
                        Ok(maybe_type_key) => (maybe_type_key, vec![]),
                        Err(errs) => (None, errs),
                    };

                // Add any errors we collected to the program context. We're doing it this way
                // instead of adding errors to the program context immediately to avoid borrowing
                // issues.
                for err in errors {
                    ctx.insert_err(err);
                }

                AExpr {
                    kind: AExprKind::BinaryOperation(
                        Box::new(a_left.clone()),
                        op.clone(),
                        Box::new(a_right),
                    ),
                    type_key: get_result_type(ctx, op, maybe_operand_type_key),
                    start_pos,
                    end_pos,
                }
            }
        };

        // Try to (safely) coerce the expression to the right type (this may involve template
        // rendering).
        result = result.coerce_and_check_types(ctx, maybe_expected_type_key, &expr);

        if !allow_templated_result {
            // Make sure the resulting type is not still templated. If it is, coercion/rendering failed.
            let actual_type = ctx.must_get_type(result.type_key);
            if actual_type.is_templated() {
                ctx.insert_err(AnalyzeError::new(
                    ErrorKind::UnresolvedTmplParams,
                    format_code!("failed to resolve template parameters for {}", expr).as_str(),
                    &expr,
                ));
            }
        }

        result
    }

    /// Returns a string containing the human-readable version of this expression.
    pub fn display(&self, ctx: &ProgramContext) -> String {
        self.kind.display(ctx)
    }

    /// Creates a new expression with the value of the given symbol.
    pub fn from_symbol(symbol: ASymbol) -> Self {
        AExpr {
            start_pos: symbol.start_pos().clone(),
            end_pos: symbol.end_pos().clone(),
            type_key: symbol.get_type_key(),
            kind: AExprKind::Symbol(symbol),
        }
    }

    /// Checks if type coercion to the expected type is necessary and, if so, attempts it before
    /// performing type checks. Adds an error to the program context if type checks fail. No
    /// type checks are performed if `maybe_expected_type_key` is None.
    fn coerce_and_check_types(
        mut self,
        ctx: &mut ProgramContext,
        maybe_expected_type_key: Option<TypeKey>,
        expr: &Expression,
    ) -> Self {
        let expected_tk = match maybe_expected_type_key {
            Some(tk) => tk,
            None => return self,
        };

        // Try coerce this expression to the expected type before doing the type check.
        self = self.try_coerce_to(ctx, expected_tk);

        // Skip the type check if either type is unknown, as this implies that semantic analysis
        // has already failed somewhere else in this expression or wherever it's being used.
        let actual_type = ctx.must_get_type(self.type_key);
        let expected_type = ctx.must_get_type(expected_tk);
        if actual_type.is_unknown() || expected_type.is_unknown() {
            return self;
        }

        if !actual_type.is_same_as(ctx, &expected_type) {
            ctx.insert_err(AnalyzeError::new(
                ErrorKind::MismatchedTypes,
                format_code!(
                    "expected expression of type {}, but found {}",
                    expected_type.display(ctx),
                    actual_type.display(ctx),
                )
                .as_str(),
                expr,
            ));
        }

        self
    }

    /// Tries to coerce this expression to the target type. If coercion is successful, returns
    /// the coerced expression, otherwise just returns the expression as-is.
    pub fn try_coerce_to(mut self, ctx: &mut ProgramContext, target_type_key: TypeKey) -> Self {
        let target_type = ctx.must_get_type(target_type_key);
        if target_type.is_unknown() {
            return self;
        }

        match &self.kind {
            // Only coerce i64 literals with they don't have explicit type suffixes.
            AExprKind::I64Literal(i, has_type_suffix) if !has_type_suffix && *i >= 0 => {
                match target_type {
                    AType::U64 => {
                        self.kind = AExprKind::U64Literal(*i as u64, false);
                        self.type_key = ctx.u64_type_key();
                    }
                    _ => {}
                }
            }

            // Only coerce u64 literals with they don't have explicit type suffixes.
            AExprKind::U64Literal(u, has_type_suffix) if !has_type_suffix => match target_type {
                AType::I64 => {
                    self.kind = AExprKind::I64Literal(*u as i64, false);
                    self.type_key = ctx.i64_type_key();
                }
                _ => {}
            },

            AExprKind::Symbol(symbol) => {
                let tk = symbol.get_type_key();
                match ctx.must_get_type(tk) {
                    // Only continue if the symbol refers to a templated function.
                    AType::Function(sig) if sig.is_templated() => {}
                    _ => return self,
                };

                todo!()
            }

            AExprKind::UnaryOperation(Operator::Reference, operand) => {
                if let AType::Pointer(target_ptr_type) = target_type {
                    let coerced_operand = operand
                        .clone()
                        .try_coerce_to(ctx, target_ptr_type.pointee_type_key);
                    let new_type = AType::Pointer(APointerType::new(coerced_operand.type_key));

                    self.type_key = ctx.insert_type(new_type);
                    self.kind =
                        AExprKind::UnaryOperation(Operator::Reference, Box::new(coerced_operand));
                }
            }

            _ => {}
        };

        self
    }

    /// Creates a new expression.
    pub fn new_with_default_pos(kind: AExprKind, type_key: TypeKey) -> Self {
        AExpr {
            kind,
            type_key,
            start_pos: Position::default(),
            end_pos: Position::default(),
        }
    }

    /// Returns a new expression with value null. The null value for the rawptr type is just 0u64
    /// type cast to a rawptr.
    pub fn new_null_ptr(ctx: &ProgramContext) -> AExpr {
        AExpr {
            kind: AExprKind::TypeCast(
                Box::new(AExpr::new_with_default_pos(
                    AExprKind::U64Literal(0, false),
                    ctx.u64_type_key(),
                )),
                ctx.rawptr_type_key(),
            ),
            type_key: ctx.unknown_type_key(),
            start_pos: Position::default(),
            end_pos: Position::default(),
        }
    }

    /// Creates a new zero-valued expression of the given type.
    pub fn new_zero_value(ctx: &mut ProgramContext, typ: Type) -> Self {
        let type_key = ctx.resolve_type(&typ);
        let start_pos = typ.start_pos().clone();
        let end_pos = typ.end_pos().clone();

        match typ {
            Type::Struct(_) => AExpr {
                kind: AExprKind::StructInit(AStructInit {
                    type_key,
                    field_values: Default::default(),
                }),
                type_key,
                start_pos,
                end_pos,
            },

            Type::Enum(_) => AExpr {
                kind: AExprKind::EnumInit(AEnumVariantInit {
                    type_key: type_key,
                    variant: AEnumTypeVariant {
                        number: 0,
                        name: "<unknown>".to_string(),
                        maybe_type_key: None,
                    },
                    maybe_value: None,
                }),
                type_key,
                start_pos,
                end_pos,
            },

            Type::Tuple(_) => AExpr {
                kind: AExprKind::TupleInit(ATupleInit::new_empty(ctx)),
                type_key,
                start_pos,
                end_pos,
            },

            Type::Array(_) => AExpr {
                kind: AExprKind::ArrayInit(AArrayInit::new_empty(ctx)),
                type_key,
                start_pos,
                end_pos,
            },

            Type::Function(_) => AExpr {
                kind: AExprKind::AnonFunction(Box::new(AFn {
                    signature: AFnSig {
                        name: "".to_string(),
                        args: vec![],
                        ret_type_key: None,
                        type_key,
                        maybe_impl_type_key: None,
                        tmpl_params: None,
                    },
                    body: AClosure::new_empty(),
                })),
                type_key,
                start_pos,
                end_pos,
            },

            Type::Unresolved(unresolved_type) => {
                let kind = match unresolved_type.name.as_str() {
                    "bool" => AExprKind::BoolLiteral(false),
                    "i64" => AExprKind::I64Literal(0, false),
                    "u64" => AExprKind::U64Literal(0, false),
                    "str" => AExprKind::StrLiteral("".to_string()),
                    "rawptr" => AExpr::new_null_ptr(ctx).kind,
                    _ => AExprKind::Unknown,
                };

                AExpr {
                    kind,
                    type_key,
                    start_pos,
                    end_pos,
                }
            }

            Type::Pointer(_) => AExpr::new_null_ptr(ctx),
        }
    }

    /// Tries to compute the value of this expression as a u64. Returns an error if this expression
    /// does not result in a constant u64 value.
    pub fn try_into_const_u64(&self, ctx: &mut ProgramContext) -> AnalyzeResult<u64> {
        let expr = self.clone().try_coerce_to(ctx, ctx.u64_type_key());

        let err = Err(AnalyzeError::new(
            ErrorKind::InvalidArraySize,
            format_code!(
                "expected constant expression of type {}, but found {}",
                "u64",
                self.display(ctx)
            )
            .as_str(),
            self,
        ));

        if !expr.kind.is_const()
            || !ctx
                .must_get_type(expr.type_key)
                .is_same_as(ctx, &AType::U64)
        {
            return err;
        }

        let result = match &expr.kind {
            AExprKind::Symbol(symbol) => {
                let const_value = ctx.get_const_value(symbol.name.as_str()).unwrap().clone();

                match &symbol.member_access {
                    Some(access) => {
                        return try_get_const_member_value_as_u64(ctx, &const_value, access)
                    }
                    None => return const_value.try_into_const_u64(ctx),
                }
            }

            AExprKind::I64Literal(i, _) => {
                if *i < 0 {
                    None
                } else {
                    Some(*i as u64)
                }
            }

            AExprKind::U64Literal(u, _) => Some(*u),

            AExprKind::BinaryOperation(left_expr, op, right_expr) => {
                let left = left_expr.try_into_const_u64(ctx).unwrap();
                let right = right_expr.try_into_const_u64(ctx).unwrap();
                match op {
                    Operator::Add => Some(left + right),
                    Operator::Subtract => Some(left - right),
                    Operator::Multiply => Some(left * right),
                    Operator::Divide => Some(left / right),
                    Operator::Modulo => Some(left % right),
                    other => panic!("unexpected operator {}", other),
                }
            }

            AExprKind::TypeCast(expr, target_type_key) => {
                // At this point we already know that the expression can be cast to u64 because
                // we checked its type above.
                let mut expr = expr.clone();
                expr.type_key = *target_type_key;
                return expr.try_into_const_u64(ctx);
            }

            other => panic!("cannot evaluate expression {} as constant u64", other),
        };

        match result {
            Some(v) => Ok(v),
            None => err,
        }
    }
}

/// Checks that the operands of a binary operation are compatible with the operator and one
/// another. If successful, returns the type key of the operands (their types should be the
/// same).
fn check_operand_types(
    ctx: &ProgramContext,
    left_expr: &AExpr,
    op: &Operator,
    right_expr: &AExpr,
) -> Result<Option<TypeKey>, Vec<AnalyzeError>> {
    let left_type = ctx.must_get_type(left_expr.type_key);
    let right_type = ctx.must_get_type(right_expr.type_key);

    let mut operand_type_key = None;
    let mut errors = vec![];

    if !is_valid_operand_type(op, left_type) {
        errors.push(AnalyzeError::new(
            ErrorKind::MismatchedTypes,
            format_code!(
                "cannot apply operator {} to left-side expression of type {}",
                &op,
                ctx.display_type_for_key(left_expr.type_key),
            )
            .as_str(),
            left_expr,
        ));
    } else {
        operand_type_key = Some(left_expr.type_key);
    }

    if !is_valid_operand_type(op, right_type) {
        errors.push(AnalyzeError::new(
            ErrorKind::MismatchedTypes,
            format_code!(
                "cannot apply operator {} to right-side expression of type {}",
                &op,
                ctx.display_type_for_key(right_expr.type_key),
            )
            .as_str(),
            right_expr,
        ));
    } else {
        operand_type_key = Some(right_expr.type_key);
    }

    if !right_type.is_same_as(ctx, left_type) {
        errors.push(AnalyzeError::new(
            ErrorKind::MismatchedTypes,
            format_code!(
                "{} operands have mismatched types {} and {}",
                op,
                left_type.display(ctx),
                right_type.display(ctx),
            )
            .as_str(),
            right_expr,
        ));
    }

    match errors.is_empty() {
        true => Ok(operand_type_key),
        false => Err(errors),
    }
}

/// Returns true only if `operand_type` is valid for operator `op`.
fn is_valid_operand_type(op: &Operator, operand_type: &AType) -> bool {
    // Determine the expected operand types on the operator.
    match op {
        // Mathematical operators only work on numeric types.
        Operator::Add
        | Operator::Subtract
        | Operator::Multiply
        | Operator::Divide
        | Operator::Modulo => matches!(operand_type, AType::I64 | AType::RawPtr | AType::U64),

        // Logical operators only work on bools.
        Operator::LogicalAnd | Operator::LogicalOr => matches!(operand_type, AType::Bool),

        // Equality operators only work on most primitive types.
        Operator::EqualTo | Operator::NotEqualTo => {
            matches!(
                operand_type,
                AType::Bool | AType::I64 | AType::RawPtr | AType::U64 | AType::Str
            )
        }

        // Both operands of "like" and "not like" comparisons should be enums.
        Operator::Like | Operator::NotLike => matches!(operand_type, AType::Enum(_)),

        // Comparators only work on numeric types.
        Operator::GreaterThan
        | Operator::LessThan
        | Operator::GreaterThanOrEqual
        | Operator::LessThanOrEqual => matches!(operand_type, AType::I64 | AType::U64),

        // If this happens, something is badly broken.
        other => panic!("unexpected operator {}", other),
    }
}

/// Returns true only if it is possible to cast from `left_type` to `right_type`.
fn is_valid_type_cast(left_type: &AType, right_type: &AType) -> bool {
    match (left_type, right_type) {
        // Casting between rawptr and u64 is allowed.
        (AType::RawPtr, AType::U64)
        | (AType::U64, AType::RawPtr)

        // Casting between typed pointers and rawptrs is allowed.
        | (AType::Pointer(_), AType::RawPtr)
        | (AType::RawPtr, AType::Pointer(_))

        // Casting between compatible numeric types is allowed.
        | (AType::I64, AType::U64) | (AType::U64, AType::I64)  => true,

        _ => false,
    }
}

/// Returns the type of the value that would result from performing `op` on operands with
/// `operand_type_key`. If no `operand_type_key` was specified, falls back to default result type.
fn get_result_type(
    ctx: &ProgramContext,
    op: &Operator,
    operand_type_key: Option<TypeKey>,
) -> TypeKey {
    match op {
        // Mathematical operations result in the same type as their operands.
        Operator::Add
        | Operator::Subtract
        | Operator::Multiply
        | Operator::Divide
        | Operator::Modulo => match operand_type_key {
            Some(type_key) => type_key,
            None => ctx.i64_type_key(),
        },

        // Logical operators result in bools.
        Operator::LogicalAnd | Operator::LogicalOr => ctx.bool_type_key(),

        // Equality operators result in bools.
        Operator::EqualTo | Operator::NotEqualTo | Operator::Like | Operator::NotLike => {
            ctx.bool_type_key()
        }

        // Comparators result in bools.
        Operator::GreaterThan
        | Operator::LessThan
        | Operator::GreaterThanOrEqual
        | Operator::LessThanOrEqual => ctx.bool_type_key(),

        Operator::As => match operand_type_key {
            Some(type_key) => type_key,
            None => ctx.unknown_type_key(),
        },

        // If this happens, the something is badly broken.
        other => panic!("unexpected operator {}", other),
    }
}

/// Computes the operand type that should be expected for operator `op` that yields a result of
/// `expected_result_type_key`. Returns `None` if it's unclear what the operand type should be.
fn get_expected_operand_type_key(
    ctx: &ProgramContext,
    op: &Operator,
    expected_result_type_key: TypeKey,
) -> Option<TypeKey> {
    match op {
        Operator::Add
        | Operator::Subtract
        | Operator::Multiply
        | Operator::Divide
        | Operator::Modulo => Some(expected_result_type_key),

        Operator::LogicalAnd | Operator::LogicalOr => Some(ctx.bool_type_key()),

        Operator::EqualTo | Operator::NotEqualTo | Operator::Like | Operator::NotLike => None,

        Operator::GreaterThan
        | Operator::LessThan
        | Operator::GreaterThanOrEqual
        | Operator::LessThanOrEqual => None,

        Operator::As => None,

        // If this happens, the something is badly broken.
        other => panic!("unexpected operator {}", other),
    }
}

/// Tries to compute the value of a member access as a u64.
fn try_get_const_member_value_as_u64(
    ctx: &mut ProgramContext,
    const_value: &AExpr,
    member_access: &AMemberAccess,
) -> AnalyzeResult<u64> {
    let member_value = match &const_value.kind {
        AExprKind::StructInit(struct_init) => struct_init
            .field_values
            .get(member_access.member_name.as_str())
            .unwrap(),

        AExprKind::TupleInit(tuple_init) => {
            let member_index = member_access.member_name.parse::<usize>().unwrap();
            tuple_init.values.get(member_index).unwrap()
        }

        other => panic!("unexpected member access: {}", other),
    };

    match &member_access.submember {
        Some(sub) => try_get_const_member_value_as_u64(ctx, member_value, sub),
        None => member_value.try_into_const_u64(ctx),
    }
}

#[cfg(test)]
mod tests {
    use crate::analyzer::ast::arg::AArg;
    use crate::analyzer::ast::closure::AClosure;
    use crate::analyzer::ast::expr::{AExpr, AExprKind};
    use crate::analyzer::ast::fn_call::AFnCall;
    use crate::analyzer::ast::func::{AFn, AFnSig};
    use crate::analyzer::ast::r#type::AType;
    use crate::analyzer::ast::symbol::ASymbol;
    use crate::analyzer::error::{AnalyzeError, ErrorKind};
    use crate::analyzer::prog_context::ProgramContext;
    use crate::analyzer::scope::ScopedSymbol;
    use crate::lexer::pos::Position;
    use crate::parser::ast::arg::Argument;
    use crate::parser::ast::bool_lit::BoolLit;
    use crate::parser::ast::expr::Expression;
    use crate::parser::ast::func_call::FunctionCall;
    use crate::parser::ast::func_sig::FunctionSignature;
    use crate::parser::ast::i64_lit::I64Lit;
    use crate::parser::ast::op::Operator;
    use crate::parser::ast::r#type::Type;
    use crate::parser::ast::str_lit::StrLit;
    use crate::parser::ast::symbol::Symbol;

    #[test]
    fn analyze_i64_literal() {
        let mut ctx = ProgramContext::new();
        let expr = Expression::I64Literal(I64Lit::new_with_default_pos(1));
        let result = AExpr::from(&mut ctx, expr, None, false);
        assert!(ctx.errors().is_empty());
        assert_eq!(
            result,
            AExpr {
                kind: AExprKind::I64Literal(1, false),
                type_key: ctx.i64_type_key(),
                start_pos: Position::default(),
                end_pos: Position::default(),
            }
        );
    }

    #[test]
    fn analyze_bool_literal() {
        let mut ctx = ProgramContext::new();
        let expr = Expression::BoolLiteral(BoolLit::new_with_default_pos(false));
        let result = AExpr::from(&mut ctx, expr, None, false);
        assert!(ctx.errors().is_empty());
        assert_eq!(
            result,
            AExpr {
                kind: AExprKind::BoolLiteral(false),
                type_key: ctx.bool_type_key(),
                start_pos: Position::default(),
                end_pos: Position::default(),
            },
        );
    }

    #[test]
    fn analyze_string_literal() {
        let mut ctx = ProgramContext::new();
        let expr = Expression::StrLiteral(StrLit::new_with_default_pos("test"));
        let result = AExpr::from(&mut ctx, expr, None, false);
        assert!(ctx.errors().is_empty());
        assert_eq!(
            result,
            AExpr {
                kind: AExprKind::StrLiteral(String::from("test")),
                type_key: ctx.str_type_key(),
                start_pos: Position::default(),
                end_pos: Position::default(),
            }
        );
    }

    #[test]
    fn analyze_var() {
        let mut ctx = ProgramContext::new();
        ctx.insert_symbol(ScopedSymbol::new("myvar", ctx.str_type_key(), false, false));
        let result = AExpr::from(
            &mut ctx,
            Expression::Symbol(Symbol::new_with_default_pos("myvar")),
            None,
            false,
        );
        assert!(ctx.errors().is_empty());
        assert_eq!(
            result,
            AExpr {
                kind: AExprKind::Symbol(ASymbol::new_with_default_pos(
                    "myvar",
                    ctx.str_type_key(),
                    None
                )),
                type_key: ctx.str_type_key(),
                start_pos: Position::default(),
                end_pos: Position::default(),
            }
        );
    }

    #[test]
    fn analyze_invalid_var() {
        let mut ctx = ProgramContext::new();
        let result = AExpr::from(
            &mut ctx,
            Expression::Symbol(Symbol::new_with_default_pos("myvar")),
            None,
            false,
        );
        assert_eq!(
            result,
            AExpr {
                kind: AExprKind::Symbol(ASymbol::new_with_default_pos(
                    "myvar",
                    ctx.unknown_type_key(),
                    None,
                )),
                type_key: ctx.unknown_type_key(),
                start_pos: Position::default(),
                end_pos: Position::default(),
            }
        );
        assert!(matches!(
            ctx.errors()
                .values()
                .collect::<Vec<&AnalyzeError>>()
                .get(0)
                .unwrap(),
            AnalyzeError {
                kind: ErrorKind::UndefSymbol,
                ..
            }
        ));
    }

    #[test]
    fn analyze_fn_call() {
        let mut ctx = ProgramContext::new();
        let fn_sig = FunctionSignature::new_with_default_pos(
            "do_thing",
            vec![Argument::new_with_default_pos(
                "first",
                Type::new_unresolved("bool"),
                false,
            )],
            Some(Type::new_unresolved("str")),
        );
        let fn_type_key = ctx.resolve_type(&Type::Function(Box::new(fn_sig.clone())));
        let a_fn = AFn {
            signature: AFnSig {
                name: "do_thing".to_string(),
                args: vec![AArg {
                    name: "first".to_string(),
                    type_key: ctx.bool_type_key(),
                    is_mut: false,
                }],
                ret_type_key: Some(ctx.str_type_key()),
                type_key: fn_type_key,
                maybe_impl_type_key: None,
                tmpl_params: None,
            },
            body: AClosure::new_empty(),
        };

        // Add the function and its type to the context so they can be retrieved when analyzing
        // the expression that calls the function.
        ctx.insert_fn(a_fn.clone());
        ctx.insert_type(AType::from_fn_sig(a_fn.signature.clone()));

        // Analyze the function call expression.
        let fn_call = FunctionCall::new_with_default_pos(
            "do_thing",
            vec![Expression::BoolLiteral(BoolLit::new_with_default_pos(true))],
        );
        let call_expr = Expression::FunctionCall(fn_call.clone());
        let result = AExpr::from(&mut ctx, call_expr, None, false);

        // Check that analysis succeeded.
        assert!(ctx.errors().is_empty());
        assert_eq!(
            result,
            AExpr {
                kind: AExprKind::FunctionCall(AFnCall {
                    fn_symbol: ASymbol::new_with_default_pos(
                        "do_thing",
                        a_fn.signature.type_key,
                        None,
                    ),
                    args: vec![AExpr {
                        kind: AExprKind::BoolLiteral(true),
                        type_key: ctx.bool_type_key(),
                        start_pos: Position::default(),
                        end_pos: Position::default(),
                    }],
                    maybe_ret_type_key: Some(ctx.str_type_key()),
                }),
                type_key: ctx.str_type_key(),
                start_pos: Position::default(),
                end_pos: Position::default(),
            },
        );
    }

    #[test]
    fn fn_call_no_return() {
        let mut ctx = ProgramContext::new();
        let fn_sig = FunctionSignature::new_with_default_pos(
            "do_thing",
            vec![Argument::new_with_default_pos(
                "first",
                Type::new_unresolved("bool"),
                false,
            )],
            None,
        );
        let fn_type_key = ctx.resolve_type(&Type::Function(Box::new(fn_sig.clone())));
        let a_fn = AFn {
            signature: AFnSig {
                name: "do_thing".to_string(),
                args: vec![],
                ret_type_key: None,
                type_key: fn_type_key,
                maybe_impl_type_key: None,
                tmpl_params: None,
            },
            body: AClosure::new_empty(),
        };

        // Add the function and its type to the context so they can be retrieved when analyzing
        // the expression that calls the function.
        ctx.insert_fn(a_fn.clone());
        ctx.insert_type(AType::from_fn_sig(a_fn.signature.clone()));

        // Analyze the function call expression.
        let result = AExpr::from(
            &mut ctx,
            Expression::BinaryOperation(
                Box::new(Expression::I64Literal(I64Lit::new_with_default_pos(1))),
                Operator::Add,
                Box::new(Expression::FunctionCall(
                    FunctionCall::new_with_default_pos("do_thing", vec![]),
                )),
            ),
            None,
            false,
        );

        match result {
            AExpr {
                kind: AExprKind::BinaryOperation(left, Operator::Add, right),
                type_key,
                ..
            } => {
                assert_eq!(
                    *left,
                    AExpr {
                        kind: AExprKind::I64Literal(1, false),
                        type_key: ctx.i64_type_key(),
                        start_pos: Position::default(),
                        end_pos: Position::default(),
                    }
                );
                assert_eq!(
                    *right,
                    AExpr {
                        kind: AExprKind::Unknown,
                        type_key: ctx.none_type_key(),
                        start_pos: Position::default(),
                        end_pos: Position::default(),
                    }
                );
                assert_eq!(type_key, ctx.i64_type_key())
            }
            other => panic!("incorrect result {}", other),
        }

        assert!(matches!(
            ctx.errors()
                .values()
                .collect::<Vec<&AnalyzeError>>()
                .get(0)
                .unwrap(),
            AnalyzeError {
                kind: ErrorKind::ExpectedReturnValue,
                ..
            }
        ));
    }

    #[test]
    fn fn_call_missing_arg() {
        let mut ctx = ProgramContext::new();
        let fn_sig = FunctionSignature::new_with_default_pos(
            "do_thing",
            vec![
                Argument::new_with_default_pos("arg1", Type::new_unresolved("bool"), false),
                Argument::new_with_default_pos("arg2", Type::new_unresolved("i64"), false),
            ],
            Some(Type::new_unresolved("bool")),
        );
        let fn_type_key = ctx.resolve_type(&Type::Function(Box::new(fn_sig)));
        let a_fn = AFn {
            signature: AFnSig {
                name: "do_thing".to_string(),
                args: vec![
                    AArg {
                        name: "arg1".to_string(),
                        type_key: ctx.bool_type_key(),
                        is_mut: false,
                    },
                    AArg {
                        name: "arg2".to_string(),
                        type_key: ctx.i64_type_key(),
                        is_mut: false,
                    },
                ],
                ret_type_key: Some(ctx.bool_type_key()),
                type_key: fn_type_key,
                maybe_impl_type_key: None,
                tmpl_params: None,
            },
            body: AClosure::new_empty(),
        };

        // Add the function and its type to the context so they can be retrieved when analyzing
        // the expression that calls the function.
        ctx.insert_fn(a_fn.clone());
        ctx.insert_type(AType::from_fn_sig(a_fn.signature.clone()));

        // Analyze the function call expression.
        let result = AExpr::from(
            &mut ctx,
            Expression::FunctionCall(FunctionCall::new_with_default_pos(
                "do_thing",
                vec![Expression::BoolLiteral(BoolLit::new_with_default_pos(true))],
            )),
            None,
            false,
        );

        assert_eq!(
            result,
            AExpr {
                kind: AExprKind::FunctionCall(AFnCall {
                    fn_symbol: ASymbol::new_with_default_pos(
                        "do_thing",
                        a_fn.signature.type_key,
                        None,
                    ),
                    args: vec![AExpr {
                        kind: AExprKind::BoolLiteral(true),
                        type_key: ctx.bool_type_key(),
                        start_pos: Position::default(),
                        end_pos: Position::default(),
                    }],
                    maybe_ret_type_key: Some(ctx.bool_type_key()),
                }),
                type_key: ctx.bool_type_key(),
                start_pos: Position::default(),
                end_pos: Position::default(),
            }
        );

        match result.kind {
            AExprKind::FunctionCall(call) => {
                assert_eq!(
                    call.fn_symbol,
                    ASymbol::new_with_default_pos("do_thing", a_fn.signature.type_key, None,)
                );
                assert_eq!(call.maybe_ret_type_key, Some(ctx.bool_type_key()));
                assert_eq!(call.args.len(), 1);
                assert_eq!(
                    call.args.get(0),
                    Some(&AExpr {
                        kind: AExprKind::BoolLiteral(true),
                        type_key: ctx.bool_type_key(),
                        start_pos: Position::default(),
                        end_pos: Position::default(),
                    })
                );
            }
            _ => unreachable!(),
        };

        assert!(matches!(
            ctx.errors()
                .values()
                .collect::<Vec<&AnalyzeError>>()
                .get(0)
                .unwrap(),
            AnalyzeError {
                kind: ErrorKind::WrongNumberOfArgs,
                ..
            }
        ));
    }

    #[test]
    fn fn_call_invalid_arg_type() {
        let mut ctx = ProgramContext::new();
        let fn_sig = FunctionSignature::new_with_default_pos(
            "do_thing",
            vec![Argument::new_with_default_pos(
                "arg",
                Type::new_unresolved("bool"),
                false,
            )],
            Some(Type::new_unresolved("bool")),
        );
        let a_fn = AFn {
            signature: AFnSig {
                name: "do_thing".to_string(),
                args: vec![AArg {
                    name: "arg".to_string(),
                    type_key: ctx.bool_type_key(),
                    is_mut: false,
                }],
                ret_type_key: Some(ctx.bool_type_key()),
                type_key: ctx.resolve_type(&Type::Function(Box::new(fn_sig))),
                maybe_impl_type_key: None,
                tmpl_params: None,
            },
            body: AClosure::new_empty(),
        };

        // Add the function and its type to the context so they can be retrieved when analyzing
        // the expression that calls the function.
        ctx.insert_fn(a_fn.clone());
        ctx.insert_type(AType::from_fn_sig(a_fn.signature.clone()));

        // Analyze the function call expression.
        let result = AExpr::from(
            &mut ctx,
            Expression::FunctionCall(FunctionCall::new_with_default_pos(
                "do_thing",
                vec![Expression::I64Literal(I64Lit::new_with_default_pos(1))],
            )),
            None,
            false,
        );

        assert_eq!(
            result,
            AExpr::new_with_default_pos(
                AExprKind::FunctionCall(AFnCall {
                    fn_symbol: ASymbol::new_with_default_pos(
                        "do_thing",
                        a_fn.signature.type_key,
                        None,
                    ),
                    args: vec![AExpr {
                        kind: AExprKind::I64Literal(1, false),
                        type_key: ctx.i64_type_key(),
                        start_pos: Position::default(),
                        end_pos: Position::default(),
                    }],
                    maybe_ret_type_key: Some(ctx.bool_type_key()),
                }),
                ctx.bool_type_key(),
            )
        );

        assert!(matches!(
            ctx.errors()
                .values()
                .collect::<Vec<&AnalyzeError>>()
                .get(0)
                .unwrap(),
            AnalyzeError {
                kind: ErrorKind::MismatchedTypes,
                ..
            }
        ));
    }

    #[test]
    fn binary_op_invalid_operand_types() {
        let mut ctx = ProgramContext::new();
        let result = AExpr::from(
            &mut ctx,
            Expression::BinaryOperation(
                Box::new(Expression::I64Literal(I64Lit::new_with_default_pos(1))),
                Operator::Add,
                Box::new(Expression::StrLiteral(StrLit::new_with_default_pos("asdf"))),
            ),
            None,
            false,
        );

        assert_eq!(
            result,
            AExpr {
                kind: AExprKind::BinaryOperation(
                    Box::new(AExpr {
                        kind: AExprKind::I64Literal(1, false),
                        type_key: ctx.i64_type_key(),
                        start_pos: Position::default(),
                        end_pos: Position::default(),
                    }),
                    Operator::Add,
                    Box::new(AExpr {
                        kind: AExprKind::StrLiteral("asdf".to_string()),
                        type_key: ctx.str_type_key(),
                        start_pos: Position::default(),
                        end_pos: Position::default(),
                    })
                ),
                type_key: ctx.i64_type_key(),
                start_pos: Position::default(),
                end_pos: Position::default(),
            }
        );

        assert!(matches!(
            ctx.errors()
                .values()
                .collect::<Vec<&AnalyzeError>>()
                .get(0)
                .unwrap(),
            AnalyzeError {
                kind: ErrorKind::MismatchedTypes,
                ..
            }
        ));

        let mut ctx = ProgramContext::new();
        let result = AExpr::from(
            &mut ctx,
            Expression::BinaryOperation(
                Box::new(Expression::StrLiteral(StrLit::new_with_default_pos("asdf"))),
                Operator::Add,
                Box::new(Expression::I64Literal(I64Lit::new_with_default_pos(1))),
            ),
            None,
            false,
        );

        assert_eq!(
            result,
            AExpr {
                kind: AExprKind::BinaryOperation(
                    Box::new(AExpr {
                        kind: AExprKind::StrLiteral("asdf".to_string()),
                        type_key: ctx.str_type_key(),
                        start_pos: Position::default(),
                        end_pos: Position::default(),
                    }),
                    Operator::Add,
                    Box::new(AExpr {
                        kind: AExprKind::I64Literal(1, false),
                        type_key: ctx.i64_type_key(),
                        start_pos: Position::default(),
                        end_pos: Position::default(),
                    })
                ),
                type_key: ctx.i64_type_key(),
                start_pos: Position::default(),
                end_pos: Position::default(),
            }
        );

        assert!(matches!(
            ctx.errors()
                .values()
                .collect::<Vec<&AnalyzeError>>()
                .get(0)
                .unwrap(),
            AnalyzeError {
                kind: ErrorKind::MismatchedTypes,
                ..
            }
        ));
    }

    #[test]
    fn unary_op() {
        let mut ctx = ProgramContext::new();
        let result = AExpr::from(
            &mut ctx,
            Expression::UnaryOperation(
                Operator::LogicalNot,
                Box::new(Expression::I64Literal(I64Lit::new_with_default_pos(1))),
            ),
            None,
            false,
        );

        assert_eq!(
            result,
            AExpr {
                kind: AExprKind::BoolLiteral(false),
                type_key: ctx.bool_type_key(),
                start_pos: Position::default(),
                end_pos: Position::default(),
            }
        );

        assert!(matches!(
            ctx.errors()
                .values()
                .collect::<Vec<&AnalyzeError>>()
                .get(0)
                .unwrap(),
            AnalyzeError {
                kind: ErrorKind::MismatchedTypes,
                ..
            }
        ));
    }

    #[test]
    fn unary_op_invalid_operand_type() {
        let mut ctx = ProgramContext::new();
        let result = AExpr::from(
            &mut ctx,
            Expression::UnaryOperation(
                Operator::LogicalNot,
                Box::new(Expression::StrLiteral(StrLit::new_with_default_pos("s"))),
            ),
            None,
            false,
        );

        assert_eq!(
            result,
            AExpr {
                kind: AExprKind::BoolLiteral(false),
                type_key: ctx.bool_type_key(),
                start_pos: Position::default(),
                end_pos: Position::default(),
            }
        );

        assert!(matches!(
            ctx.errors()
                .values()
                .collect::<Vec<&AnalyzeError>>()
                .get(0)
                .unwrap(),
            AnalyzeError {
                kind: ErrorKind::MismatchedTypes,
                ..
            }
        ));
    }
}
