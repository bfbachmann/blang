use std::fmt;
use std::fmt::Formatter;

use colored::Colorize;

use crate::analyzer::closure::RichClosure;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::func::{RichFn, RichFnCall, RichFnSig};
use crate::analyzer::prog_context::{ProgramContext, ScopeKind};
use crate::analyzer::r#struct::{RichStruct, RichStructInit};
use crate::analyzer::r#type::RichType;
use crate::format_code;
use crate::parser::closure::Closure;
use crate::parser::expr::Expression;
use crate::parser::op::Operator;
use crate::parser::r#type::Type;
use crate::parser::unresolved::UnresolvedType;

#[derive(Debug, Clone)]
pub enum RichExprKind {
    VariableReference(String),
    BoolLiteral(bool),
    I64Literal(i64),
    StringLiteral(String),
    StructInit(RichStructInit),
    FunctionCall(RichFnCall),
    AnonFunction(Box<RichFn>),
    UnaryOperation(Operator, Box<RichExpr>),
    BinaryOperation(Box<RichExpr>, Operator, Box<RichExpr>),
    Unknown,
}

impl fmt::Display for RichExprKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            RichExprKind::VariableReference(var_name) => write!(f, "variable {}", var_name),
            RichExprKind::BoolLiteral(b) => write!(f, "{}", b),
            RichExprKind::I64Literal(i) => write!(f, "{}", i),
            RichExprKind::StringLiteral(s) => write!(f, "{}", s),
            RichExprKind::StructInit(s) => write!(f, "{}", s),
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
            (RichExprKind::VariableReference(v1), RichExprKind::VariableReference(v2)) => v1 == v2,
            (RichExprKind::BoolLiteral(b1), RichExprKind::BoolLiteral(b2)) => b1 == b2,
            (RichExprKind::I64Literal(i1), RichExprKind::I64Literal(i2)) => i1 == i2,
            (RichExprKind::StringLiteral(s1), RichExprKind::StringLiteral(s2)) => s1 == s2,
            (RichExprKind::StructInit(s1), RichExprKind::StructInit(s2)) => s1 == s2,
            (RichExprKind::FunctionCall(f1), RichExprKind::FunctionCall(f2)) => f1 == f2,
            (RichExprKind::AnonFunction(a1), RichExprKind::AnonFunction(a2)) => a1 == a2,
            (RichExprKind::UnaryOperation(o1, e1), RichExprKind::UnaryOperation(o2, e2)) => {
                o1 == o2 && e1 == e2
            }
            (
                RichExprKind::BinaryOperation(l1, o1, r1),
                RichExprKind::BinaryOperation(l2, o2, r2),
            ) => l1 == l2 && o1 == o2 && r1 == r2,
            (_, _) => false,
        }
    }
}

/// Represents a semantically valid and type-rich expression.
#[derive(Clone, PartialEq, Debug)]
pub struct RichExpr {
    pub kind: RichExprKind,
    pub typ: RichType,
}

impl fmt::Display for RichExpr {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.kind)
    }
}

impl RichExpr {
    /// Performs semantic analysis on the given expression and returns a type-rich version of it,
    /// or an error if the expression is semantically invalid.
    pub fn from(ctx: &mut ProgramContext, expr: Expression) -> RichExpr {
        match expr {
            Expression::VariableReference(ref var_ref) => {
                let var_name = var_ref.var_name.clone();

                // Make sure the variable being referenced exists. Note that it might be a function.
                if let Some(var_typ) = ctx.get_var(var_name.as_str()) {
                    RichExpr {
                        kind: RichExprKind::VariableReference(var_name),
                        typ: var_typ.clone(),
                    }
                } else if let Some(func) = ctx.get_fn(var_name.as_str()) {
                    RichExpr {
                        kind: RichExprKind::VariableReference(var_name),
                        typ: RichType::Function(Box::new(func.signature.clone())),
                    }
                } else if let Some(fn_sig) = ctx.get_extern_fn(var_name.as_str()) {
                    RichExpr {
                        kind: RichExprKind::VariableReference(var_name),
                        typ: RichType::Function(Box::new(fn_sig.clone())),
                    }
                } else {
                    // The variable was not defined, so record the error and return a zero-valued
                    // expression instead.
                    ctx.add_err(AnalyzeError::new_from_expr(
                        ErrorKind::VariableNotDefined,
                        &expr,
                        format_code!("variable {} does not exist", &var_name).as_str(),
                    ));

                    RichExpr::new_zero_value(Type::Unresolved(UnresolvedType::unknown()))
                }
            }
            Expression::BoolLiteral(b) => RichExpr {
                kind: RichExprKind::BoolLiteral(b.value),
                typ: RichType::Bool,
            },
            Expression::I64Literal(i) => RichExpr {
                kind: RichExprKind::I64Literal(i.value),
                typ: RichType::I64,
            },
            Expression::StringLiteral(s) => RichExpr {
                kind: RichExprKind::StringLiteral(s.value),
                typ: RichType::String,
            },
            Expression::StructInit(struct_init) => {
                let rich_init = RichStructInit::from(ctx, &struct_init);
                let typ = (&rich_init.typ).clone();
                RichExpr {
                    kind: RichExprKind::StructInit(rich_init),
                    typ: RichType::Struct(typ),
                }
            }
            Expression::FunctionCall(fn_call) => {
                // Analyze the function call and ensure it has a return type.
                let rich_call = RichFnCall::from(ctx, fn_call.clone());
                if let Some(typ) = rich_call.ret_type.clone() {
                    return RichExpr {
                        kind: RichExprKind::FunctionCall(rich_call),
                        typ,
                    };
                }

                // The function does not have a return value. Record the error and return some
                // some zero-value instead.
                ctx.add_err(AnalyzeError::new_with_locatable(
                    ErrorKind::ExpectedReturnValue,
                    format_code!(
                        "function {} has no return value, but is called in an expression \
                            where a return value is expected",
                        &fn_call.fn_name,
                    )
                    .as_str(),
                    Box::new(fn_call),
                ));

                RichExpr::new_zero_value(Type::Unresolved(UnresolvedType::none()))
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
                    kind: RichExprKind::AnonFunction(Box::new(RichFn {
                        signature: RichFnSig::from(ctx, &anon_fn.signature),
                        body: rich_closure,
                    })),
                    typ: RichType::Function(Box::new(RichFnSig::from(ctx, &anon_fn.signature))),
                }
            }
            ref expr @ Expression::UnaryOperation(ref op, ref right_expr) => {
                if *op != Operator::Not {
                    // If this happens, the parser is badly broken.
                    panic!("invalid unary operator {}", op)
                }

                // Make sure the expression has type bool.
                let rich_expr = RichExpr::from(ctx, *right_expr.clone());
                match &rich_expr.typ {
                    &RichType::Bool => RichExpr {
                        kind: RichExprKind::UnaryOperation(Operator::Not, Box::new(rich_expr)),
                        typ: RichType::Bool,
                    },
                    other => {
                        // The expression has the wrong type. Record the error and insert a
                        // zero-value instead.
                        ctx.add_err(AnalyzeError::new_from_expr(
                            ErrorKind::IncompatibleTypes,
                            &expr,
                            format_code!(
                                "unary operator {} cannot be applied to value of type {}",
                                "!",
                                other,
                            )
                            .as_str(),
                        ));

                        RichExpr::new_zero_value(Type::bool())
                    }
                }
            }
            ref expr @ Expression::BinaryOperation(ref left_expr, ref op, ref right_expr) => {
                // Analyze the left and right operands.
                let rich_left = RichExpr::from(ctx, *left_expr.clone());
                let rich_right = RichExpr::from(ctx, *right_expr.clone());

                // Determine the expected operand types and result type based on the operator.
                let (expected_type, result_type) = match op {
                    // Mathematical operators only work on numeric types.
                    Operator::Add
                    | Operator::Subtract
                    | Operator::Multiply
                    | Operator::Divide
                    | Operator::Modulo => (Some(RichType::I64), RichType::I64),
                    // Logical operators only work on bools.
                    Operator::LogicalAnd | Operator::LogicalOr => {
                        (Some(RichType::Bool), RichType::Bool)
                    }
                    // Equality operators work on anything.
                    Operator::EqualTo | Operator::NotEqualTo => (None, RichType::Bool),
                    // Comparators only work on numeric types.
                    Operator::GreaterThan
                    | Operator::LessThan
                    | Operator::GreaterThanOrEqual
                    | Operator::LessThanOrEqual => (Some(RichType::I64), RichType::Bool),
                    // If this happens, the parser is badly broken.
                    other => panic!("unexpected operator {}", other),
                };

                // If we couldn't resolve both of the operand types, we'll skip any further
                // type checks by returning early.
                if rich_left.typ.is_unknown() || rich_right.typ.is_unknown() {
                    return RichExpr {
                        kind: RichExprKind::BinaryOperation(
                            Box::new(rich_left),
                            op.clone(),
                            Box::new(rich_right),
                        ),
                        typ: result_type,
                    };
                }

                // If there is an expected type, make sure the left and right expressions match the
                // type. Otherwise, we just make sure both the left and right expression types
                // match.
                if let Some(expected) = expected_type {
                    if rich_left.typ != expected {
                        // The left-side expression is of the wrong type. Record the error.
                        ctx.add_err(AnalyzeError::new_from_expr(
                            ErrorKind::IncompatibleTypes,
                            &expr,
                            format_code!(
                                "cannot apply operator {} to left-side expression of type {}",
                                &op,
                                &rich_left.typ,
                            )
                            .as_str(),
                        ));
                    }

                    if rich_right.typ != expected {
                        // The right-size expression is of the wrong type. Record the error.
                        ctx.add_err(AnalyzeError::new_from_expr(
                            ErrorKind::IncompatibleTypes,
                            &expr,
                            format_code!(
                                "cannot apply operator {} to right-side expression type {}",
                                &op,
                                &rich_right.typ,
                            )
                            .as_str(),
                        ));
                    }
                } else if rich_left.typ != rich_right.typ {
                    // The operand types don't match. Record the error.
                    ctx.add_err(AnalyzeError::new_from_expr(
                        ErrorKind::IncompatibleTypes,
                        &expr,
                        format_code!(
                            "incompatible types {} and {}",
                            &rich_left.typ,
                            &rich_right.typ,
                        )
                        .as_str(),
                    ));
                }

                RichExpr {
                    kind: RichExprKind::BinaryOperation(
                        Box::new(rich_left),
                        op.clone(),
                        Box::new(rich_right),
                    ),
                    typ: result_type,
                }
            }
        }
    }

    /// Creates a new zero-valued expression of the given type.
    pub fn new_zero_value(typ: Type) -> Self {
        match typ {
            Type::Bool(_) => RichExpr {
                kind: RichExprKind::BoolLiteral(false),
                typ: RichType::Bool,
            },
            Type::String(_) => RichExpr {
                kind: RichExprKind::StringLiteral("".to_string()),
                typ: RichType::String,
            },
            Type::I64(_) => RichExpr {
                kind: RichExprKind::I64Literal(0),
                typ: RichType::I64,
            },
            Type::Struct(struct_type) => RichExpr {
                kind: RichExprKind::StructInit(RichStructInit {
                    typ: RichStruct {
                        name: struct_type.name.clone(),
                        fields: vec![],
                    },
                    field_values: Default::default(),
                }),
                typ: RichType::Struct(RichStruct {
                    name: struct_type.name,
                    fields: vec![],
                }),
            },
            Type::Function(_) => RichExpr {
                kind: RichExprKind::AnonFunction(Box::new(RichFn {
                    signature: RichFnSig {
                        name: "".to_string(),
                        args: vec![],
                        return_type: None,
                    },
                    body: RichClosure {
                        statements: vec![],
                        ret_type: None,
                        original: Closure {
                            statements: vec![],
                            result: None,
                            start_pos: Default::default(),
                            end_pos: Default::default(),
                        },
                    },
                })),
                typ: RichType::Function(Box::new(RichFnSig {
                    name: "".to_string(),
                    args: vec![],
                    return_type: None,
                })),
            },
            Type::Unresolved(unresolved_type) => RichExpr {
                kind: RichExprKind::Unknown,
                typ: RichType::Unknown(unresolved_type.name),
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::analyzer::closure::RichClosure;
    use crate::analyzer::error::{AnalyzeError, ErrorKind};
    use crate::analyzer::expr::{RichExpr, RichExprKind};
    use crate::analyzer::func::{RichArg, RichFn, RichFnCall, RichFnSig};
    use crate::analyzer::prog_context::ProgramContext;
    use crate::analyzer::r#type::RichType;
    use crate::parser::bool_lit::BoolLit;
    use crate::parser::closure::Closure;
    use crate::parser::expr::Expression;
    use crate::parser::func_call::FunctionCall;
    use crate::parser::i64_lit::I64Lit;
    use crate::parser::op::Operator;
    use crate::parser::string_lit::StringLit;
    use crate::parser::var_ref::VarRef;

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
                typ: RichType::I64
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
                typ: RichType::Bool,
            },
        );
    }

    #[test]
    fn analyze_string_literal() {
        let mut ctx = ProgramContext::new();
        let expr = Expression::StringLiteral(StringLit::new_with_default_pos("test"));
        let result = RichExpr::from(&mut ctx, expr);
        assert!(ctx.errors().is_empty());
        assert_eq!(
            result,
            RichExpr {
                kind: RichExprKind::StringLiteral(String::from("test")),
                typ: RichType::String
            }
        );
    }

    #[test]
    fn analyze_var_ref() {
        let mut ctx = ProgramContext::new();
        ctx.add_var("myvar", RichType::String);
        let result = RichExpr::from(
            &mut ctx,
            Expression::VariableReference(VarRef::new_with_default_pos("myvar")),
        );
        assert!(ctx.errors().is_empty());
        assert_eq!(
            result,
            RichExpr {
                kind: RichExprKind::VariableReference("myvar".to_string()),
                typ: RichType::String
            }
        );
    }

    #[test]
    fn analyze_invalid_var_ref() {
        let mut ctx = ProgramContext::new();
        let result = RichExpr::from(
            &mut ctx,
            Expression::VariableReference(VarRef::new_with_default_pos("myvar")),
        );
        assert!(matches!(
            result,
            RichExpr {
                kind: RichExprKind::Unknown,
                typ: RichType::Unknown(_),
            }
        ));
        assert!(matches!(
            ctx.errors().remove(0),
            AnalyzeError {
                kind: ErrorKind::VariableNotDefined,
                ..
            }
        ));
    }

    #[test]
    fn analyze_fn_call() {
        let mut ctx = ProgramContext::new();
        ctx.add_fn(RichFn {
            signature: RichFnSig {
                name: "do_thing".to_string(),
                args: vec![RichArg {
                    name: "first".to_string(),
                    typ: RichType::Bool,
                }],
                return_type: Some(RichType::String),
            },
            body: RichClosure {
                statements: vec![],
                ret_type: None,
                original: Closure::new_empty(),
            },
        });
        let fn_call = FunctionCall::new_with_default_pos(
            "do_thing",
            vec![Expression::BoolLiteral(BoolLit::new_with_default_pos(true))],
        );
        let call_expr = Expression::FunctionCall(fn_call.clone());
        let result = RichExpr::from(&mut ctx, call_expr);
        assert!(ctx.errors().is_empty());
        assert_eq!(
            result,
            RichExpr {
                kind: RichExprKind::FunctionCall(RichFnCall {
                    fn_name: fn_call.fn_name,
                    args: vec![RichExpr {
                        kind: RichExprKind::BoolLiteral(true),
                        typ: RichType::Bool
                    }],
                    ret_type: Some(RichType::String),
                }),
                typ: RichType::String,
            },
        );
    }

    #[test]
    fn fn_call_no_return() {
        let mut ctx = ProgramContext::new();
        ctx.add_fn(RichFn {
            signature: RichFnSig {
                name: "do_thing".to_string(),
                args: vec![],
                return_type: None,
            },
            body: RichClosure {
                statements: vec![],
                ret_type: None,
                original: Closure::new_empty(),
            },
        });
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
                typ: RichType::I64,
            } => {
                assert!(matches!(
                    *left,
                    RichExpr {
                        kind: RichExprKind::I64Literal(1),
                        typ: RichType::I64,
                    }
                ));
                assert!(matches!(
                    *right,
                    RichExpr {
                        kind: RichExprKind::Unknown,
                        typ: RichType::Unknown(_),
                    }
                ));
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
        ctx.add_fn(RichFn {
            signature: RichFnSig {
                name: "do_thing".to_string(),
                args: vec![
                    RichArg {
                        name: "arg1".to_string(),
                        typ: RichType::Bool,
                    },
                    RichArg {
                        name: "arg2".to_string(),
                        typ: RichType::I64,
                    },
                ],
                return_type: Some(RichType::Bool),
            },
            body: RichClosure {
                statements: vec![],
                ret_type: None,
                original: Closure::new_empty(),
            },
        });
        let result = RichExpr::from(
            &mut ctx,
            Expression::FunctionCall(FunctionCall::new_with_default_pos(
                "do_thing",
                vec![Expression::BoolLiteral(BoolLit::new_with_default_pos(true))],
            )),
        );

        assert!(matches!(
            result,
            RichExpr {
                kind: RichExprKind::FunctionCall(_),
                typ: RichType::Bool,
            }
        ));

        match result.kind {
            RichExprKind::FunctionCall(call) => {
                assert_eq!(call.fn_name, "do_thing");
                assert_eq!(call.ret_type, Some(RichType::Bool));
                assert_eq!(call.args.len(), 1);
                assert_eq!(
                    call.args.get(0),
                    Some(&RichExpr {
                        kind: RichExprKind::BoolLiteral(true),
                        typ: RichType::Bool,
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
        ctx.add_fn(RichFn {
            signature: RichFnSig {
                name: "do_thing".to_string(),
                args: vec![RichArg {
                    name: "arg".to_string(),
                    typ: RichType::Bool,
                }],
                return_type: Some(RichType::Bool),
            },
            body: RichClosure {
                statements: vec![],
                ret_type: None,
                original: Closure::new_empty(),
            },
        });
        let result = RichExpr::from(
            &mut ctx,
            Expression::FunctionCall(FunctionCall::new_with_default_pos(
                "do_thing",
                vec![Expression::I64Literal(I64Lit::new_with_default_pos(1))],
            )),
        );

        assert!(matches!(
            result,
            RichExpr {
                kind: RichExprKind::FunctionCall(_),
                typ: RichType::Bool,
            }
        ));

        match result.kind {
            RichExprKind::FunctionCall(call) => {
                assert_eq!(call.fn_name, "do_thing");
                assert_eq!(call.ret_type, Some(RichType::Bool));
                assert_eq!(call.args.len(), 1);
                assert_eq!(
                    call.args.get(0).unwrap(),
                    &RichExpr {
                        kind: RichExprKind::I64Literal(1),
                        typ: RichType::I64,
                    }
                );
            }
            _ => unreachable!(),
        };

        assert!(matches!(
            ctx.errors().remove(0),
            AnalyzeError {
                kind: ErrorKind::IncompatibleTypes,
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
                Box::new(Expression::StringLiteral(StringLit::new_with_default_pos(
                    "asdf",
                ))),
            ),
        );

        assert!(matches!(
            result,
            RichExpr {
                kind: RichExprKind::BinaryOperation(_, Operator::Add, _),
                typ: RichType::I64,
            }
        ));

        match result.kind {
            RichExprKind::BinaryOperation(left, Operator::Add, right) => {
                assert_eq!(left.typ, RichType::I64);
                assert_eq!(right.typ, RichType::String);
                assert_eq!(left.kind, RichExprKind::I64Literal(1));
                assert_eq!(right.kind, RichExprKind::StringLiteral("asdf".to_string()));
            }
            _ => unreachable!(),
        };

        assert!(matches!(
            ctx.errors().remove(0),
            AnalyzeError {
                kind: ErrorKind::IncompatibleTypes,
                ..
            }
        ));

        let mut ctx = ProgramContext::new();
        let result = RichExpr::from(
            &mut ctx,
            Expression::BinaryOperation(
                Box::new(Expression::StringLiteral(StringLit::new_with_default_pos(
                    "asdf",
                ))),
                Operator::Add,
                Box::new(Expression::I64Literal(I64Lit::new_with_default_pos(1))),
            ),
        );

        assert!(matches!(
            result,
            RichExpr {
                kind: RichExprKind::BinaryOperation(_, Operator::Add, _),
                typ: RichType::I64,
            }
        ));

        match result.kind {
            RichExprKind::BinaryOperation(left, Operator::Add, right) => {
                assert_eq!(left.typ, RichType::String);
                assert_eq!(right.typ, RichType::I64);
                assert_eq!(left.kind, RichExprKind::StringLiteral("asdf".to_string()));
                assert_eq!(right.kind, RichExprKind::I64Literal(1));
            }
            other => panic!("incorrect result kind {}", other),
        };

        assert!(matches!(
            ctx.errors().remove(0),
            AnalyzeError {
                kind: ErrorKind::IncompatibleTypes,
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

        assert!(matches!(
            result,
            RichExpr {
                kind: RichExprKind::BoolLiteral(false),
                typ: RichType::Bool,
            }
        ));

        assert!(matches!(
            ctx.errors().remove(0),
            AnalyzeError {
                kind: ErrorKind::IncompatibleTypes,
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
                Box::new(Expression::StringLiteral(StringLit::new_with_default_pos(
                    "s",
                ))),
            ),
        );

        assert!(matches!(
            result,
            RichExpr {
                kind: RichExprKind::BoolLiteral(false),
                typ: RichType::Bool,
            }
        ));

        assert!(matches!(
            ctx.errors().remove(0),
            AnalyzeError {
                kind: ErrorKind::IncompatibleTypes,
                ..
            }
        ));
    }
}
