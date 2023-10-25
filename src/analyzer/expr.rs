use std::fmt;
use std::fmt::Formatter;

use colored::Colorize;

use crate::analyzer::closure::RichClosure;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::func::RichFn;
use crate::analyzer::func_call::RichFnCall;
use crate::analyzer::func_sig::RichFnSig;
use crate::analyzer::prog_context::{ProgramContext, ScopeKind};
use crate::analyzer::r#enum::{RichEnumTypeVariant, RichEnumVariantInit};
use crate::analyzer::r#struct::RichStructInit;
use crate::analyzer::r#type::{RichType, TypeId};
use crate::analyzer::symbol::RichSymbol;
use crate::analyzer::tuple::RichTupleInit;
use crate::lexer::pos::{Locatable, Position};
use crate::parser::expr::Expression;
use crate::parser::op::Operator;
use crate::parser::r#type::Type;
use crate::parser::unresolved::UnresolvedType;
use crate::{format_code, locatable_impl};

/// Represents a kind of expression.
#[derive(Debug, Clone)]
pub enum RichExprKind {
    Symbol(RichSymbol),
    BoolLiteral(bool),
    I64Literal(i64),
    U64Literal(u64),
    Null,
    StrLiteral(String),
    StructInit(RichStructInit),
    EnumInit(RichEnumVariantInit),
    TupleInit(RichTupleInit),
    FunctionCall(RichFnCall),
    AnonFunction(Box<RichFn>),
    UnaryOperation(Operator, Box<RichExpr>),
    BinaryOperation(Box<RichExpr>, Operator, Box<RichExpr>),
    Unknown,
}

impl fmt::Display for RichExprKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            RichExprKind::Symbol(sym) => write!(f, "{}", sym),
            RichExprKind::BoolLiteral(b) => write!(f, "{}", b),
            RichExprKind::I64Literal(i) => write!(f, "{}", i),
            RichExprKind::U64Literal(i) => write!(f, "{}", i),
            RichExprKind::Null => write!(f, "null"),
            RichExprKind::StrLiteral(s) => write!(f, "{}", s),
            RichExprKind::StructInit(s) => write!(f, "{}", s),
            RichExprKind::EnumInit(e) => write!(f, "{}", e),
            RichExprKind::TupleInit(t) => write!(f, "{}", t),
            RichExprKind::FunctionCall(call) => write!(f, "{}", call),
            RichExprKind::AnonFunction(func) => write!(f, "{}", *func),
            RichExprKind::UnaryOperation(op, expr) => write!(f, "{} {}", op, expr),
            RichExprKind::BinaryOperation(left, op, right) => {
                write!(f, "{} {} {}", left, op, right)
            }
            RichExprKind::Unknown => {
                write!(f, "<unknown>")
            }
        }
    }
}

impl PartialEq for RichExprKind {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (RichExprKind::Symbol(v1), RichExprKind::Symbol(v2)) => v1 == v2,
            (RichExprKind::BoolLiteral(b1), RichExprKind::BoolLiteral(b2)) => b1 == b2,
            (RichExprKind::I64Literal(i1), RichExprKind::I64Literal(i2)) => i1 == i2,
            (RichExprKind::U64Literal(i1), RichExprKind::U64Literal(i2)) => i1 == i2,
            (RichExprKind::Null, RichExprKind::Null) => true,
            (RichExprKind::StrLiteral(s1), RichExprKind::StrLiteral(s2)) => s1 == s2,
            (RichExprKind::StructInit(s1), RichExprKind::StructInit(s2)) => s1 == s2,
            (RichExprKind::EnumInit(e1), RichExprKind::EnumInit(e2)) => e1 == e2,
            (RichExprKind::TupleInit(t1), RichExprKind::TupleInit(t2)) => t1 == t2,
            (RichExprKind::FunctionCall(f1), RichExprKind::FunctionCall(f2)) => f1 == f2,
            (RichExprKind::AnonFunction(a1), RichExprKind::AnonFunction(a2)) => a1 == a2,
            (RichExprKind::UnaryOperation(o1, e1), RichExprKind::UnaryOperation(o2, e2)) => {
                o1 == o2 && e1 == e2
            }
            (
                RichExprKind::BinaryOperation(l1, o1, r1),
                RichExprKind::BinaryOperation(l2, o2, r2),
            ) => l1 == l2 && o1 == o2 && r1 == r2,
            (RichExprKind::Unknown, RichExprKind::Unknown) => true,
            (_, _) => false,
        }
    }
}

impl RichExprKind {
    /// Returns true if the expression kind can be used as a constant.
    pub fn is_const(&self) -> bool {
        match self {
            // Primitive literals are valid constants.
            RichExprKind::BoolLiteral(_)
            | RichExprKind::I64Literal(_)
            | RichExprKind::Null
            | RichExprKind::U64Literal(_)
            | RichExprKind::StrLiteral(_) => true,

            // Unary and binary operations are constants if they only operate on constants.
            RichExprKind::UnaryOperation(_, expr) => expr.kind.is_const(),
            RichExprKind::BinaryOperation(left_expr, _, right_expr) => {
                left_expr.kind.is_const() && right_expr.kind.is_const()
            }

            // Struct initializations are constants if all their fields are constants.
            RichExprKind::StructInit(struct_init) => {
                for (_, field_val) in &struct_init.field_values {
                    if !field_val.kind.is_const() {
                        return false;
                    }
                }

                true
            }

            // Enum variant initializations are constants if they have no values or their values
            // are constants.
            RichExprKind::EnumInit(enum_init) => {
                if let Some(val) = &enum_init.maybe_value {
                    if !val.kind.is_const() {
                        return false;
                    }
                }

                true
            }

            // Tuple values are constants if all their fields are constants.
            RichExprKind::TupleInit(tuple_init) => {
                for val in &tuple_init.values {
                    if !val.kind.is_const() {
                        return false;
                    }
                }

                true
            }

            // Symbols can be constants.
            RichExprKind::Symbol(sym) => sym.is_const,

            // Function calls and unknown values are never constants.
            RichExprKind::FunctionCall(_)
            | RichExprKind::AnonFunction(_)
            | RichExprKind::Unknown => false,
        }
    }
}

/// Represents a semantically valid and type-rich expression.
#[derive(Clone, PartialEq, Debug)]
pub struct RichExpr {
    pub kind: RichExprKind,
    pub type_id: TypeId,
    start_pos: Position,
    end_pos: Position,
}

impl fmt::Display for RichExpr {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.kind)
    }
}

locatable_impl!(RichExpr);

impl RichExpr {
    /// Performs semantic analysis on the given expression and returns a type-rich version of it.
    pub fn from(ctx: &mut ProgramContext, expr: Expression) -> RichExpr {
        let start_pos = expr.start_pos().clone();
        let end_pos = expr.end_pos().clone();

        match expr {
            Expression::Symbol(ref symbol) => {
                let rich_symbol = RichSymbol::from(ctx, symbol, true, None);
                let type_id = rich_symbol.get_type_id().clone();
                RichExpr {
                    kind: RichExprKind::Symbol(rich_symbol),
                    type_id,
                    start_pos,
                    end_pos,
                }
            }

            Expression::BoolLiteral(b) => RichExpr {
                kind: RichExprKind::BoolLiteral(b.value),
                type_id: TypeId::bool(),
                start_pos,
                end_pos,
            },

            Expression::I64Literal(i) => RichExpr {
                kind: RichExprKind::I64Literal(i.value),
                type_id: TypeId::i64(),
                start_pos,
                end_pos,
            },

            Expression::U64Literal(i) => RichExpr {
                kind: RichExprKind::U64Literal(i.value),
                type_id: TypeId::u64(),
                start_pos,
                end_pos,
            },

            Expression::Null(_) => RichExpr {
                kind: RichExprKind::Null,
                type_id: TypeId::ptr(),
                start_pos,
                end_pos,
            },

            Expression::StrLiteral(s) => RichExpr {
                kind: RichExprKind::StrLiteral(s.value),
                type_id: TypeId::str(),
                start_pos,
                end_pos,
            },

            Expression::StructInit(struct_init) => {
                let rich_init = RichStructInit::from(ctx, &struct_init);
                RichExpr {
                    kind: RichExprKind::StructInit(rich_init),
                    type_id: TypeId::from(struct_init.typ), // TODO: can this just be `type_id`?
                    start_pos,
                    end_pos,
                }
            }

            Expression::EnumInit(enum_init) => {
                let rich_init = RichEnumVariantInit::from(ctx, &enum_init);
                let type_id = rich_init.enum_type_id.clone();
                RichExpr {
                    kind: RichExprKind::EnumInit(rich_init),
                    type_id,
                    start_pos,
                    end_pos,
                }
            }

            Expression::TupleInit(tuple_init) => {
                let rich_init = RichTupleInit::from(ctx, &tuple_init);
                let type_id = rich_init.type_id.clone();
                RichExpr {
                    kind: RichExprKind::TupleInit(rich_init),
                    type_id,
                    start_pos,
                    end_pos,
                }
            }

            Expression::SizeOf(sizeof) => {
                // Get the size of the type and just represent it as a u64 literal.
                let type_id = RichType::analyze(ctx, &sizeof.typ);
                let typ = ctx.must_get_resolved_type(&type_id);
                RichExpr {
                    kind: RichExprKind::U64Literal(typ.size_bytes(ctx) as u64),
                    type_id: TypeId::u64(),
                    start_pos,
                    end_pos,
                }
            }

            Expression::FunctionCall(fn_call) => {
                // Analyze the function call and ensure it has a return type.
                let rich_call = RichFnCall::from(ctx, fn_call.clone());
                if let Some(type_id) = rich_call.maybe_ret_type_id.clone() {
                    return RichExpr {
                        kind: RichExprKind::FunctionCall(rich_call),
                        type_id,
                        start_pos,
                        end_pos,
                    };
                }

                // The function does not have a return value. Record the error and return some
                // some zero-value instead.
                ctx.add_err(AnalyzeError::new(
                    ErrorKind::ExpectedReturnValue,
                    format_code!(
                        "function {} has no return value, but is called in an expression \
                            where a return value is expected",
                        &fn_call.fn_symbol,
                    )
                    .as_str(),
                    &fn_call,
                ));

                RichExpr::new_zero_value(ctx, Type::Unresolved(UnresolvedType::none()))
            }

            Expression::AnonFunction(anon_fn) => {
                // We don't need to analyze the function signature, since it has no name. Just analyze
                // the function body.
                let sig = anon_fn.signature.clone();
                let rich_closure = RichClosure::from(
                    ctx,
                    anon_fn.body,
                    ScopeKind::FnBody,
                    sig.args.clone(),
                    sig.return_type.clone(),
                );
                RichExpr {
                    start_pos,
                    end_pos,
                    kind: RichExprKind::AnonFunction(Box::new(RichFn {
                        signature: RichFnSig::from(ctx, &anon_fn.signature),
                        body: rich_closure,
                    })),
                    type_id: TypeId::from(Type::Function(Box::new(sig))),
                }
            }

            ref expr @ Expression::UnaryOperation(ref op, ref right_expr) => {
                if *op != Operator::Not {
                    // If this happens, the parser is badly broken.
                    panic!("invalid unary operator {}", op)
                }

                // Make sure the expression has type bool.
                let rich_expr = RichExpr::from(ctx, *right_expr.clone());
                if rich_expr.type_id.is_bool() {
                    RichExpr {
                        kind: RichExprKind::UnaryOperation(Operator::Not, Box::new(rich_expr)),
                        type_id: TypeId::bool(),
                        start_pos,
                        end_pos,
                    }
                } else {
                    // The expression has the wrong type. Record the error and insert a
                    // zero-value instead.
                    ctx.add_err(AnalyzeError::new(
                        ErrorKind::MismatchedTypes,
                        format_code!(
                            "unary operator {} cannot be applied to value of type {}",
                            "!",
                            rich_expr.type_id,
                        )
                        .as_str(),
                        expr,
                    ));

                    RichExpr::new_zero_value(ctx, Type::bool())
                }
            }

            Expression::BinaryOperation(ref left_expr, ref op, ref right_expr) => {
                // Analyze the left and right operands.
                let rich_left = RichExpr::from(ctx, *left_expr.clone());
                let rich_right = RichExpr::from(ctx, *right_expr.clone());

                // If we couldn't resolve both of the operand types, we'll skip any further
                // type checks by returning early.
                let left_type = ctx.must_get_resolved_type(&rich_left.type_id);
                let right_type = ctx.must_get_resolved_type(&rich_right.type_id);
                if left_type.is_unknown() || right_type.is_unknown() {
                    return RichExpr {
                        kind: RichExprKind::BinaryOperation(
                            Box::new(rich_left.clone()),
                            op.clone(),
                            Box::new(rich_right),
                        ),
                        type_id: RichExpr::get_result_type(op, None),
                        start_pos,
                        end_pos,
                    };
                }

                // Make sure the left-side expression is of the right type.
                let mut errors = vec![];
                let mut operand_type_id = None;
                if !RichExpr::is_valid_operand_type(op, left_type) {
                    errors.push(AnalyzeError::new(
                        ErrorKind::MismatchedTypes,
                        format_code!(
                            "cannot apply operator {} to left-side expression of type {}",
                            &op,
                            &rich_left.type_id,
                        )
                        .as_str(),
                        left_expr.as_ref(),
                    ));
                } else {
                    operand_type_id = Some(rich_left.type_id.clone());
                }

                // Make sure the right-side expression is of the right type.
                if !RichExpr::is_valid_operand_type(op, right_type) {
                    errors.push(AnalyzeError::new(
                        ErrorKind::MismatchedTypes,
                        format_code!(
                            "cannot apply operator {} to right-side expression of type {}",
                            &op,
                            &rich_right.type_id,
                        )
                        .as_str(),
                        right_expr.as_ref(),
                    ));
                } else {
                    operand_type_id = Some(rich_right.type_id.clone());
                }

                // Make sure both operands are of the same type.
                if right_type != left_type {
                    errors.push(AnalyzeError::new(
                        ErrorKind::MismatchedTypes,
                        format_code!(
                            "{} operands have mismatched types {} and {}",
                            op,
                            left_type,
                            right_type,
                        )
                        .as_str(),
                        right_expr.as_ref(),
                    ));
                }

                // Add any errors we collected to the program context. We're doing it this way
                // instead of adding errors to the program context immediately to avoid borrowing
                // issues.
                for err in errors {
                    ctx.add_err(err);
                }

                RichExpr {
                    kind: RichExprKind::BinaryOperation(
                        Box::new(rich_left.clone()),
                        op.clone(),
                        Box::new(rich_right),
                    ),
                    type_id: RichExpr::get_result_type(op, operand_type_id),
                    start_pos,
                    end_pos,
                }
            }
        }
    }

    /// Creates a new expression with the value of the given symbol.
    pub fn from_symbol(symbol: RichSymbol) -> Self {
        let type_id = symbol.get_type_id().clone();
        RichExpr {
            start_pos: symbol.start_pos().clone(),
            end_pos: symbol.end_pos().clone(),
            kind: RichExprKind::Symbol(symbol),
            type_id,
        }
    }

    /// Creates a new expression.
    #[cfg(test)]
    pub fn new(kind: RichExprKind, type_id: TypeId) -> Self {
        RichExpr {
            kind,
            type_id,
            start_pos: Position::default(),
            end_pos: Position::default(),
        }
    }

    /// Creates a new zero-valued expression of the given type.
    pub fn new_zero_value(ctx: &mut ProgramContext, typ: Type) -> Self {
        let type_id = TypeId::from(typ.clone());
        match typ {
            Type::Bool(_) => RichExpr {
                kind: RichExprKind::BoolLiteral(false),
                type_id,
                start_pos: Position::default(),
                end_pos: Position::default(),
            },

            Type::Str(_) => RichExpr {
                kind: RichExprKind::StrLiteral("".to_string()),
                type_id,
                start_pos: Position::default(),
                end_pos: Position::default(),
            },

            Type::I64(_) => RichExpr {
                kind: RichExprKind::I64Literal(0),
                type_id,
                start_pos: Position::default(),
                end_pos: Position::default(),
            },

            Type::Ptr(_) => RichExpr {
                kind: RichExprKind::Null,
                type_id,
                start_pos: Position::default(),
                end_pos: Position::default(),
            },

            Type::U64(_) => RichExpr {
                kind: RichExprKind::U64Literal(0),
                type_id,
                start_pos: Position::default(),
                end_pos: Position::default(),
            },

            Type::Struct(struct_type) => RichExpr {
                kind: RichExprKind::StructInit(RichStructInit {
                    type_id: TypeId::new_unresolved(struct_type.name.as_str()),
                    field_values: Default::default(),
                }),
                type_id,
                start_pos: Position::default(),
                end_pos: Position::default(),
            },

            Type::Enum(enum_type) => RichExpr {
                kind: RichExprKind::EnumInit(RichEnumVariantInit {
                    enum_type_id: TypeId::new_unresolved(enum_type.name.as_str()),
                    variant: RichEnumTypeVariant {
                        number: 0,
                        name: "<unknown>".to_string(),
                        maybe_type_id: None,
                    },
                    maybe_value: None,
                }),
                type_id,
                start_pos: Position::default(),
                end_pos: Position::default(),
            },

            Type::Tuple(_) => RichExpr {
                kind: RichExprKind::TupleInit(RichTupleInit::new_empty(ctx)),
                type_id,
                start_pos: Position::default(),
                end_pos: Position::default(),
            },

            func_type @ Type::Function(_) => RichExpr {
                kind: RichExprKind::AnonFunction(Box::new(RichFn {
                    signature: RichFnSig {
                        name: "".to_string(),
                        args: vec![],
                        ret_type_id: None,
                        type_id: TypeId::from(func_type.clone()),
                        impl_type_id: None,
                        tmpl_params: None,
                    },
                    body: RichClosure::new_empty(),
                })),
                type_id,
                start_pos: Position::default(),
                end_pos: Position::default(),
            },

            Type::Unresolved(_) => RichExpr {
                kind: RichExprKind::Unknown,
                type_id,
                start_pos: Position::default(),
                end_pos: Position::default(),
            },

            Type::This(_) => {
                // This should never happen because type `This` is always resolved to a valid type
                // inside `impl` blocks.
                unreachable!()
            }
        }
    }

    /// Returns true only if `operand_type` is valid for operator `op`.
    fn is_valid_operand_type(op: &Operator, operand_type: &RichType) -> bool {
        // Determine the expected operand types on the operator.
        match op {
            // Mathematical operators only work on numeric types.
            Operator::Add
            | Operator::Subtract
            | Operator::Multiply
            | Operator::Divide
            | Operator::Modulo => {
                matches!(operand_type, RichType::I64 | RichType::Ptr | RichType::U64)
            }

            // Logical operators only work on bools.
            Operator::LogicalAnd | Operator::LogicalOr => matches!(operand_type, RichType::Bool),

            // Equality operators only work on numerics and bools.
            Operator::EqualTo | Operator::NotEqualTo => {
                matches!(
                    operand_type,
                    RichType::Bool | RichType::I64 | RichType::Ptr | RichType::U64
                )
            }

            // Comparators only work on numeric types.
            Operator::GreaterThan
            | Operator::LessThan
            | Operator::GreaterThanOrEqual
            | Operator::LessThanOrEqual => matches!(operand_type, RichType::I64 | RichType::U64),

            // If this happens, something is badly broken.
            other => panic!("unexpected operator {}", other),
        }
    }

    /// Returns the type of the value that would result from performing `op` on operands with
    /// `operand_type_id`. If no `operand_type_id` was specified, falls back to default result type.
    fn get_result_type(op: &Operator, operand_type_id: Option<TypeId>) -> TypeId {
        match op {
            // Mathematical operations result in the same type as their operands.
            Operator::Add
            | Operator::Subtract
            | Operator::Multiply
            | Operator::Divide
            | Operator::Modulo => match operand_type_id {
                Some(type_id) => type_id,
                None => TypeId::i64(),
            },

            // Logical operators result in bools.
            Operator::LogicalAnd | Operator::LogicalOr => TypeId::bool(),

            // Equality operators result in bools.
            Operator::EqualTo | Operator::NotEqualTo => TypeId::bool(),

            // Comparators result in bools.
            Operator::GreaterThan
            | Operator::LessThan
            | Operator::GreaterThanOrEqual
            | Operator::LessThanOrEqual => TypeId::bool(),

            // If this happens, the something is badly broken.
            other => panic!("unexpected operator {}", other),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::analyzer::arg::RichArg;
    use crate::analyzer::closure::RichClosure;
    use crate::analyzer::error::{AnalyzeError, ErrorKind};
    use crate::analyzer::expr::{RichExpr, RichExprKind};
    use crate::analyzer::func::RichFn;
    use crate::analyzer::func_call::RichFnCall;
    use crate::analyzer::func_sig::RichFnSig;
    use crate::analyzer::prog_context::{ProgramContext, ScopedSymbol};
    use crate::analyzer::r#type::{RichType, TypeId};
    use crate::analyzer::symbol::RichSymbol;
    use crate::lexer::pos::Position;
    use crate::parser::arg::Argument;
    use crate::parser::bool_lit::BoolLit;
    use crate::parser::expr::Expression;
    use crate::parser::func_call::FunctionCall;
    use crate::parser::func_sig::FunctionSignature;
    use crate::parser::i64_lit::I64Lit;
    use crate::parser::op::Operator;
    use crate::parser::r#type::Type;
    use crate::parser::str_lit::StrLit;
    use crate::parser::symbol::Symbol;

    #[test]
    fn analyze_i64_literal() {
        let mut ctx = ProgramContext::new();
        let expr = Expression::I64Literal(I64Lit::new_with_default_pos(1));
        let result = RichExpr::from(&mut ctx, expr);
        assert!(ctx.errors().is_empty());
        assert_eq!(
            result,
            RichExpr {
                kind: RichExprKind::I64Literal(1),
                type_id: TypeId::i64(),
                start_pos: Position::default(),
                end_pos: Position::default(),
            }
        );
    }

    #[test]
    fn analyze_bool_literal() {
        let mut ctx = ProgramContext::new();
        let expr = Expression::BoolLiteral(BoolLit::new_with_default_pos(false));
        let result = RichExpr::from(&mut ctx, expr);
        assert!(ctx.errors().is_empty());
        assert_eq!(
            result,
            RichExpr {
                kind: RichExprKind::BoolLiteral(false),
                type_id: TypeId::bool(),
                start_pos: Position::default(),
                end_pos: Position::default(),
            },
        );
    }

    #[test]
    fn analyze_string_literal() {
        let mut ctx = ProgramContext::new();
        let expr = Expression::StrLiteral(StrLit::new_with_default_pos("test"));
        let result = RichExpr::from(&mut ctx, expr);
        assert!(ctx.errors().is_empty());
        assert_eq!(
            result,
            RichExpr {
                kind: RichExprKind::StrLiteral(String::from("test")),
                type_id: TypeId::str(),
                start_pos: Position::default(),
                end_pos: Position::default(),
            }
        );
    }

    #[test]
    fn analyze_var() {
        let mut ctx = ProgramContext::new();
        ctx.add_symbol(ScopedSymbol::new("myvar", TypeId::str(), false, false));
        let result = RichExpr::from(
            &mut ctx,
            Expression::Symbol(Symbol::new_with_default_pos("myvar")),
        );
        assert!(ctx.errors().is_empty());
        assert_eq!(
            result,
            RichExpr {
                kind: RichExprKind::Symbol(RichSymbol::new_with_default_pos(
                    "myvar",
                    TypeId::str(),
                    None
                )),
                type_id: TypeId::str(),
                start_pos: Position::default(),
                end_pos: Position::default(),
            }
        );
    }

    #[test]
    fn analyze_invalid_var() {
        let mut ctx = ProgramContext::new();
        let result = RichExpr::from(
            &mut ctx,
            Expression::Symbol(Symbol::new_with_default_pos("myvar")),
        );
        assert_eq!(
            result,
            RichExpr {
                kind: RichExprKind::Symbol(RichSymbol::new_with_default_pos(
                    "myvar",
                    TypeId::unknown(),
                    None,
                )),
                type_id: TypeId::unknown(),
                start_pos: Position::default(),
                end_pos: Position::default(),
            }
        );
        assert!(matches!(
            ctx.errors().remove(0),
            AnalyzeError {
                kind: ErrorKind::SymbolNotDefined,
                ..
            }
        ));
    }

    #[test]
    fn analyze_fn_call() {
        let mut ctx = ProgramContext::new();
        let fn_sig = FunctionSignature::new_with_default_pos(
            "do_thing",
            vec![Argument::new_with_default_pos("first", Type::bool(), false)],
            Some(Type::str()),
        );
        let rich_fn = RichFn {
            signature: RichFnSig {
                name: "do_thing".to_string(),
                args: vec![RichArg {
                    name: "first".to_string(),
                    type_id: TypeId::bool(),
                    is_mut: false,
                }],
                ret_type_id: Some(TypeId::str()),
                type_id: TypeId::from(Type::Function(Box::new(fn_sig.clone()))),
                impl_type_id: None,
                tmpl_params: None,
            },
            body: RichClosure::new_empty(),
        };

        // Add the function and its type to the context so they can be retrieved when analyzing
        // the expression that calls the function.
        ctx.add_fn(rich_fn.clone());
        ctx.add_resolved_type(
            TypeId::from(Type::Function(Box::new(fn_sig))),
            RichType::from_fn_sig(rich_fn.signature.clone()),
        );

        // Analyze the function call expression.
        let fn_call = FunctionCall::new_with_default_pos(
            "do_thing",
            vec![Expression::BoolLiteral(BoolLit::new_with_default_pos(true))],
        );
        let call_expr = Expression::FunctionCall(fn_call.clone());
        let result = RichExpr::from(&mut ctx, call_expr);

        // Check that analysis succeeded.
        assert!(ctx.errors().is_empty());
        assert_eq!(
            result,
            RichExpr {
                kind: RichExprKind::FunctionCall(RichFnCall {
                    fn_symbol: RichSymbol::new_with_default_pos(
                        "do_thing",
                        rich_fn.signature.type_id,
                        None,
                    ),
                    args: vec![RichExpr {
                        kind: RichExprKind::BoolLiteral(true),
                        type_id: TypeId::bool(),
                        start_pos: Position::default(),
                        end_pos: Position::default(),
                    }],
                    maybe_ret_type_id: Some(TypeId::str()),
                }),
                type_id: TypeId::str(),
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
            vec![Argument::new_with_default_pos("first", Type::bool(), false)],
            None,
        );
        let rich_fn = RichFn {
            signature: RichFnSig {
                name: "do_thing".to_string(),
                args: vec![],
                ret_type_id: None,
                type_id: TypeId::from(Type::Function(Box::new(fn_sig.clone()))),
                impl_type_id: None,
                tmpl_params: None,
            },
            body: RichClosure::new_empty(),
        };

        // Add the function and its type to the context so they can be retrieved when analyzing
        // the expression that calls the function.
        ctx.add_fn(rich_fn.clone());
        ctx.add_resolved_type(
            TypeId::from(Type::Function(Box::new(fn_sig))),
            RichType::from_fn_sig(rich_fn.signature),
        );

        // Analyze the function call expression.
        let result = RichExpr::from(
            &mut ctx,
            Expression::BinaryOperation(
                Box::new(Expression::I64Literal(I64Lit::new_with_default_pos(1))),
                Operator::Add,
                Box::new(Expression::FunctionCall(
                    FunctionCall::new_with_default_pos("do_thing", vec![]),
                )),
            ),
        );

        match result {
            RichExpr {
                kind: RichExprKind::BinaryOperation(left, Operator::Add, right),
                type_id,
                ..
            } => {
                assert_eq!(
                    *left,
                    RichExpr {
                        kind: RichExprKind::I64Literal(1),
                        type_id: TypeId::i64(),
                        start_pos: Position::default(),
                        end_pos: Position::default(),
                    }
                );
                assert_eq!(
                    *right,
                    RichExpr {
                        kind: RichExprKind::Unknown,
                        type_id: TypeId::none(),
                        start_pos: Position::default(),
                        end_pos: Position::default(),
                    }
                );
                assert_eq!(type_id, TypeId::i64())
            }
            other => panic!("incorrect result {}", other),
        }

        assert!(matches!(
            ctx.errors().remove(0),
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
                Argument::new_with_default_pos("arg1", Type::bool(), false),
                Argument::new_with_default_pos("arg2", Type::i64(), false),
            ],
            Some(Type::bool()),
        );
        let rich_fn = RichFn {
            signature: RichFnSig {
                name: "do_thing".to_string(),
                args: vec![
                    RichArg {
                        name: "arg1".to_string(),
                        type_id: TypeId::bool(),
                        is_mut: false,
                    },
                    RichArg {
                        name: "arg2".to_string(),
                        type_id: TypeId::i64(),
                        is_mut: false,
                    },
                ],
                ret_type_id: Some(TypeId::bool()),
                type_id: TypeId::from(Type::Function(Box::new(fn_sig.clone()))),
                impl_type_id: None,
                tmpl_params: None,
            },
            body: RichClosure::new_empty(),
        };

        // Add the function and its type to the context so they can be retrieved when analyzing
        // the expression that calls the function.
        ctx.add_fn(rich_fn.clone());
        ctx.add_resolved_type(
            TypeId::from(Type::Function(Box::new(fn_sig))),
            RichType::from_fn_sig(rich_fn.signature.clone()),
        );

        // Analyze the function call expression.
        let result = RichExpr::from(
            &mut ctx,
            Expression::FunctionCall(FunctionCall::new_with_default_pos(
                "do_thing",
                vec![Expression::BoolLiteral(BoolLit::new_with_default_pos(true))],
            )),
        );

        assert_eq!(
            result,
            RichExpr {
                kind: RichExprKind::FunctionCall(RichFnCall {
                    fn_symbol: RichSymbol::new_with_default_pos(
                        "do_thing",
                        rich_fn.signature.type_id.clone(),
                        None,
                    ),
                    args: vec![RichExpr {
                        kind: RichExprKind::BoolLiteral(true),
                        type_id: TypeId::bool(),
                        start_pos: Position::default(),
                        end_pos: Position::default(),
                    }],
                    maybe_ret_type_id: Some(TypeId::bool()),
                }),
                type_id: TypeId::bool(),
                start_pos: Position::default(),
                end_pos: Position::default(),
            }
        );

        match result.kind {
            RichExprKind::FunctionCall(call) => {
                assert_eq!(
                    call.fn_symbol,
                    RichSymbol::new_with_default_pos("do_thing", rich_fn.signature.type_id, None,)
                );
                assert_eq!(call.maybe_ret_type_id, Some(TypeId::bool()));
                assert_eq!(call.args.len(), 1);
                assert_eq!(
                    call.args.get(0),
                    Some(&RichExpr {
                        kind: RichExprKind::BoolLiteral(true),
                        type_id: TypeId::bool(),
                        start_pos: Position::default(),
                        end_pos: Position::default(),
                    })
                );
            }
            _ => unreachable!(),
        };

        assert!(matches!(
            ctx.errors().remove(0),
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
            vec![Argument::new_with_default_pos("arg", Type::bool(), false)],
            Some(Type::bool()),
        );
        let rich_fn = RichFn {
            signature: RichFnSig {
                name: "do_thing".to_string(),
                args: vec![RichArg {
                    name: "arg".to_string(),
                    type_id: TypeId::bool(),
                    is_mut: false,
                }],
                ret_type_id: Some(TypeId::bool()),
                type_id: TypeId::from(Type::Function(Box::new(fn_sig.clone()))),
                impl_type_id: None,
                tmpl_params: None,
            },
            body: RichClosure::new_empty(),
        };

        // Add the function and its type to the context so they can be retrieved when analyzing
        // the expression that calls the function.
        ctx.add_fn(rich_fn.clone());
        ctx.add_resolved_type(
            TypeId::from(Type::Function(Box::new(fn_sig))),
            RichType::from_fn_sig(rich_fn.signature.clone()),
        );

        // Analyze the function call expression.
        let result = RichExpr::from(
            &mut ctx,
            Expression::FunctionCall(FunctionCall::new_with_default_pos(
                "do_thing",
                vec![Expression::I64Literal(I64Lit::new_with_default_pos(1))],
            )),
        );

        assert_eq!(
            result,
            RichExpr::new(
                RichExprKind::FunctionCall(RichFnCall {
                    fn_symbol: RichSymbol::new_with_default_pos(
                        "do_thing",
                        rich_fn.signature.type_id,
                        None,
                    ),
                    args: vec![RichExpr {
                        kind: RichExprKind::I64Literal(1),
                        type_id: TypeId::i64(),
                        start_pos: Position::default(),
                        end_pos: Position::default(),
                    }],
                    maybe_ret_type_id: Some(TypeId::bool()),
                }),
                TypeId::bool(),
            )
        );

        assert!(matches!(
            ctx.errors().remove(0),
            AnalyzeError {
                kind: ErrorKind::MismatchedTypes,
                ..
            }
        ));
    }

    #[test]
    fn binary_op_invalid_operand_types() {
        let mut ctx = ProgramContext::new();
        let result = RichExpr::from(
            &mut ctx,
            Expression::BinaryOperation(
                Box::new(Expression::I64Literal(I64Lit::new_with_default_pos(1))),
                Operator::Add,
                Box::new(Expression::StrLiteral(StrLit::new_with_default_pos("asdf"))),
            ),
        );

        assert_eq!(
            result,
            RichExpr {
                kind: RichExprKind::BinaryOperation(
                    Box::new(RichExpr {
                        kind: RichExprKind::I64Literal(1),
                        type_id: TypeId::i64(),
                        start_pos: Position::default(),
                        end_pos: Position::default(),
                    }),
                    Operator::Add,
                    Box::new(RichExpr {
                        kind: RichExprKind::StrLiteral("asdf".to_string()),
                        type_id: TypeId::str(),
                        start_pos: Position::default(),
                        end_pos: Position::default(),
                    })
                ),
                type_id: TypeId::i64(),
                start_pos: Position::default(),
                end_pos: Position::default(),
            }
        );

        assert!(matches!(
            ctx.errors().remove(0),
            AnalyzeError {
                kind: ErrorKind::MismatchedTypes,
                ..
            }
        ));

        let mut ctx = ProgramContext::new();
        let result = RichExpr::from(
            &mut ctx,
            Expression::BinaryOperation(
                Box::new(Expression::StrLiteral(StrLit::new_with_default_pos("asdf"))),
                Operator::Add,
                Box::new(Expression::I64Literal(I64Lit::new_with_default_pos(1))),
            ),
        );

        assert_eq!(
            result,
            RichExpr {
                kind: RichExprKind::BinaryOperation(
                    Box::new(RichExpr {
                        kind: RichExprKind::StrLiteral("asdf".to_string()),
                        type_id: TypeId::str(),
                        start_pos: Position::default(),
                        end_pos: Position::default(),
                    }),
                    Operator::Add,
                    Box::new(RichExpr {
                        kind: RichExprKind::I64Literal(1),
                        type_id: TypeId::i64(),
                        start_pos: Position::default(),
                        end_pos: Position::default(),
                    })
                ),
                type_id: TypeId::i64(),
                start_pos: Position::default(),
                end_pos: Position::default(),
            }
        );

        assert!(matches!(
            ctx.errors().remove(0),
            AnalyzeError {
                kind: ErrorKind::MismatchedTypes,
                ..
            }
        ));
    }

    #[test]
    fn unary_op() {
        let mut ctx = ProgramContext::new();
        let result = RichExpr::from(
            &mut ctx,
            Expression::UnaryOperation(
                Operator::Not,
                Box::new(Expression::I64Literal(I64Lit::new_with_default_pos(1))),
            ),
        );

        assert_eq!(
            result,
            RichExpr {
                kind: RichExprKind::BoolLiteral(false),
                type_id: TypeId::bool(),
                start_pos: Position::default(),
                end_pos: Position::default(),
            }
        );

        assert!(matches!(
            ctx.errors().remove(0),
            AnalyzeError {
                kind: ErrorKind::MismatchedTypes,
                ..
            }
        ));
    }

    #[test]
    fn unary_op_invalid_operand_type() {
        let mut ctx = ProgramContext::new();
        let result = RichExpr::from(
            &mut ctx,
            Expression::UnaryOperation(
                Operator::Not,
                Box::new(Expression::StrLiteral(StrLit::new_with_default_pos("s"))),
            ),
        );

        assert_eq!(
            result,
            RichExpr {
                kind: RichExprKind::BoolLiteral(false),
                type_id: TypeId::bool(),
                start_pos: Position::default(),
                end_pos: Position::default(),
            }
        );

        assert!(matches!(
            ctx.errors().remove(0),
            AnalyzeError {
                kind: ErrorKind::MismatchedTypes,
                ..
            }
        ));
    }
}
