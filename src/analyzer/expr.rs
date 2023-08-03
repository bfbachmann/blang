use std::fmt;
use std::fmt::Formatter;

use crate::analyzer::closure::RichClosure;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::func::{RichFn, RichFnCall, RichFnSig};
use crate::analyzer::prog_context::{ProgramContext, ScopeKind};
use crate::analyzer::r#type::RichType;
use crate::analyzer::AnalyzeResult;
use crate::parser::expr::Expression;
use crate::parser::op::Operator;

#[derive(Debug, Clone)]
pub enum RichExprKind {
    VariableReference(String),
    BoolLiteral(bool),
    I64Literal(i64),
    StringLiteral(String),
    FunctionCall(RichFnCall),
    AnonFunction(Box<RichFn>),
    UnaryOperation(Operator, Box<RichExpr>),
    BinaryOperation(Box<RichExpr>, Operator, Box<RichExpr>),
}

impl fmt::Display for RichExprKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            RichExprKind::VariableReference(var_name) => write!(f, "variable {}", var_name),
            RichExprKind::BoolLiteral(b) => write!(f, "{}", b),
            RichExprKind::I64Literal(i) => write!(f, "{}", i),
            RichExprKind::StringLiteral(s) => write!(f, "{}", s),
            RichExprKind::FunctionCall(call) => write!(f, "{}", call),
            RichExprKind::AnonFunction(func) => write!(f, "{}", *func),
            RichExprKind::UnaryOperation(op, expr) => write!(f, "{} {}", op, expr),
            RichExprKind::BinaryOperation(left, op, right) => {
                write!(f, "{} {} {}", left, op, right)
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
    pub fn from(ctx: &mut ProgramContext, expr: Expression) -> AnalyzeResult<RichExpr> {
        match expr {
            Expression::VariableReference(ref var_name) => {
                // Make sure the variable being referenced exists.
                match ctx.get_var(var_name.as_str()) {
                    Some(var_typ) => Ok(RichExpr {
                        kind: RichExprKind::VariableReference(var_name.clone()),
                        typ: var_typ.clone(),
                    }),
                    None => Err(AnalyzeError::new_from_expr(
                        ErrorKind::VariableNotDefined,
                        &expr,
                        format!("variable {} does not exist", &var_name).as_str(),
                    )),
                }
            }
            Expression::BoolLiteral(b) => Ok(RichExpr {
                kind: RichExprKind::BoolLiteral(b),
                typ: RichType::Bool,
            }),
            Expression::I64Literal(i) => Ok(RichExpr {
                kind: RichExprKind::I64Literal(i),
                typ: RichType::I64,
            }),
            Expression::StringLiteral(s) => Ok(RichExpr {
                kind: RichExprKind::StringLiteral(s),
                typ: RichType::String,
            }),
            Expression::FunctionCall(fn_call) => {
                let name = fn_call.fn_name.clone();
                let rich_call = RichFnCall::from(ctx, fn_call)?;
                if rich_call.ret_type.is_none() {
                    return Err(AnalyzeError::new(
                        ErrorKind::ExpectedValue,
                        format!(
                            r#"function {} has no return value, but was used in an expression \
                            where a value is expected"#,
                            name,
                        )
                        .as_str(),
                    ));
                }

                let typ = rich_call.ret_type.as_ref().unwrap().clone();
                Ok(RichExpr {
                    kind: RichExprKind::FunctionCall(rich_call),
                    typ,
                })
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
                )?;
                Ok(RichExpr {
                    kind: RichExprKind::AnonFunction(Box::new(RichFn {
                        signature: RichFnSig::from(ctx, &anon_fn.signature)?,
                        body: rich_closure,
                    })),
                    typ: RichType::Function(Box::new(RichFnSig::from(ctx, &anon_fn.signature)?)),
                })
            }
            ref expr @ Expression::UnaryOperation(ref op, ref right_expr) => {
                if *op != Operator::Not {
                    // If this happens, the parser is badly broken.
                    panic!("invalid unary operator {}", op)
                }

                // Make sure the expression has type bool.
                let rich_expr = RichExpr::from(ctx, *right_expr.clone())?;
                match &rich_expr.typ {
                    &RichType::Bool => Ok(RichExpr {
                        kind: RichExprKind::UnaryOperation(Operator::Not, Box::new(rich_expr)),
                        typ: RichType::Bool,
                    }),
                    other => Err(AnalyzeError::new_from_expr(
                        ErrorKind::IncompatibleTypes,
                        &expr,
                        format!(
                            "unary operator ! cannot be applied to value of type {}",
                            other,
                        )
                        .as_str(),
                    )),
                }
            }
            ref expr @ Expression::BinaryOperation(ref left_expr, ref op, ref right_expr) => {
                let rich_left = RichExpr::from(ctx, *left_expr.clone())?;
                let rich_right = RichExpr::from(ctx, *right_expr.clone())?;
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

                // If there is an expected type, make sure the left and right expressions match the
                // type. Otherwise, we just make sure both the left and right expression types
                // match.
                if let Some(expected) = expected_type {
                    if rich_left.typ != expected {
                        return Err(AnalyzeError::new_from_expr(
                            ErrorKind::IncompatibleTypes,
                            &expr,
                            format!(
                                r#"cannot apply operator {} to left-side \
                                expression of type {}"#,
                                &op, &rich_left.typ
                            )
                            .as_str(),
                        ));
                    }

                    if rich_right.typ != expected {
                        return Err(AnalyzeError::new_from_expr(
                            ErrorKind::IncompatibleTypes,
                            &expr,
                            format!(
                                "cannot apply operator {} to right-side expression type {}",
                                &op, &rich_right.typ
                            )
                            .as_str(),
                        ));
                    }
                } else if rich_left.typ != rich_right.typ {
                    return Err(AnalyzeError::new_from_expr(
                        ErrorKind::IncompatibleTypes,
                        &expr,
                        format!(
                            "incompatible types {} and {}",
                            &rich_left.typ, &rich_right.typ
                        )
                        .as_str(),
                    ));
                }

                Ok(RichExpr {
                    kind: RichExprKind::BinaryOperation(
                        Box::new(rich_left),
                        op.clone(),
                        Box::new(rich_right),
                    ),
                    typ: result_type,
                })
            }
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
    use crate::parser::expr::Expression;
    use crate::parser::func_call::FunctionCall;
    use crate::parser::op::Operator;
    

    #[test]
    fn analyze_i64_literal() {
        let mut ctx = ProgramContext::new();
        let expr = Expression::I64Literal(1);
        let result = RichExpr::from(&mut ctx, expr);
        assert!(matches!(
            result,
            Ok(RichExpr {
                kind: RichExprKind::I64Literal(1),
                typ: RichType::I64
            })
        ));
    }

    #[test]
    fn analyze_bool_literal() {
        let mut ctx = ProgramContext::new();
        let expr = Expression::BoolLiteral(false);
        let result = RichExpr::from(&mut ctx, expr);
        assert!(matches!(
            result,
            Ok(RichExpr {
                kind: RichExprKind::BoolLiteral(false),
                typ: RichType::Bool
            })
        ));
    }

    #[test]
    fn analyze_string_literal() {
        let mut ctx = ProgramContext::new();
        let expr = Expression::StringLiteral("test".to_string());
        let result = RichExpr::from(&mut ctx, expr);
        assert_eq!(
            result,
            Ok(RichExpr {
                kind: RichExprKind::StringLiteral(String::from("test")),
                typ: RichType::String
            })
        );
    }

    #[test]
    fn analyze_var_ref() {
        let mut ctx = ProgramContext::new();
        ctx.add_var("myvar", RichType::String);
        let result = RichExpr::from(&mut ctx, Expression::VariableReference("myvar".to_string()));
        assert_eq!(
            result,
            Ok(RichExpr {
                kind: RichExprKind::VariableReference("myvar".to_string()),
                typ: RichType::String
            })
        );
    }

    #[test]
    fn analyze_invalid_var_ref() {
        let mut ctx = ProgramContext::new();
        let result = RichExpr::from(&mut ctx, Expression::VariableReference("myvar".to_string()));
        assert!(matches!(
            result,
            Err(AnalyzeError {
                kind: ErrorKind::VariableNotDefined,
                ..
            })
        ));
    }

    #[test]
    fn analyze_fn_call() {
        let mut ctx = ProgramContext::new();
        ctx.add_fn(RichFn::new(
            RichFnSig::new(
                "do_thing",
                vec![RichArg {
                    name: "first".to_string(),
                    typ: RichType::Bool,
                }],
                Some(RichType::String),
            ),
            RichClosure::new(vec![], None),
        ));
        let fn_call = FunctionCall::new("do_thing", vec![Expression::BoolLiteral(true)]);
        let call_expr = Expression::FunctionCall(fn_call.clone());
        let result = RichExpr::from(&mut ctx, call_expr);
        assert_eq!(
            result,
            Ok(RichExpr {
                kind: RichExprKind::FunctionCall(RichFnCall {
                    fn_name: fn_call.fn_name,
                    args: vec![RichExpr {
                        kind: RichExprKind::BoolLiteral(true),
                        typ: RichType::Bool
                    }],
                    ret_type: Some(RichType::String),
                }),
                typ: RichType::String,
            }),
        );
    }

    #[test]
    fn fn_call_no_return() {
        let mut ctx = ProgramContext::new();
        ctx.add_fn(RichFn::new(
            RichFnSig::new("do_thing", vec![], None),
            RichClosure::new(vec![], None),
        ));
        let result = RichExpr::from(
            &mut ctx,
            Expression::BinaryOperation(
                Box::new(Expression::I64Literal(1)),
                Operator::Add,
                Box::new(Expression::FunctionCall(FunctionCall::new(
                    "do_thing",
                    vec![],
                ))),
            ),
        );
        assert!(matches!(
            result,
            Err(AnalyzeError {
                kind: ErrorKind::ExpectedValue,
                ..
            })
        ));
    }

    #[test]
    fn fn_call_missing_arg() {
        let mut ctx = ProgramContext::new();
        ctx.add_fn(RichFn::new(
            RichFnSig::new(
                "do_thing",
                vec![RichArg {
                    name: "arg".to_string(),
                    typ: RichType::Bool,
                }],
                None,
            ),
            RichClosure::new(vec![], None),
        ));
        let result = RichExpr::from(
            &mut ctx,
            Expression::BinaryOperation(
                Box::new(Expression::I64Literal(1)),
                Operator::Add,
                Box::new(Expression::FunctionCall(FunctionCall::new(
                    "do_thing",
                    vec![],
                ))),
            ),
        );
        assert!(matches!(
            result,
            Err(AnalyzeError {
                kind: ErrorKind::WrongNumberOfArgs,
                ..
            })
        ));
    }

    #[test]
    fn fn_call_invalid_arg_type() {
        let mut ctx = ProgramContext::new();
        ctx.add_fn(RichFn::new(
            RichFnSig::new(
                "do_thing",
                vec![RichArg {
                    name: "arg".to_string(),
                    typ: RichType::Bool,
                }],
                None,
            ),
            RichClosure::new(vec![], None),
        ));
        let result = RichExpr::from(
            &mut ctx,
            Expression::BinaryOperation(
                Box::new(Expression::I64Literal(1)),
                Operator::Add,
                Box::new(Expression::FunctionCall(FunctionCall::new(
                    "do_thing",
                    vec![Expression::I64Literal(1)],
                ))),
            ),
        );
        assert!(matches!(
            result,
            Err(AnalyzeError {
                kind: ErrorKind::IncompatibleTypes,
                ..
            })
        ));
    }

    #[test]
    fn binary_op_invalid_operand_types() {
        let mut ctx = ProgramContext::new();
        let result = RichExpr::from(
            &mut ctx,
            Expression::BinaryOperation(
                Box::new(Expression::I64Literal(1)),
                Operator::Add,
                Box::new(Expression::StringLiteral("asdf".to_string())),
            ),
        );
        assert!(matches!(
            result,
            Err(AnalyzeError {
                kind: ErrorKind::IncompatibleTypes,
                ..
            })
        ));

        let result = RichExpr::from(
            &mut ctx,
            Expression::BinaryOperation(
                Box::new(Expression::StringLiteral("asdf".to_string())),
                Operator::Add,
                Box::new(Expression::I64Literal(1)),
            ),
        );
        assert!(matches!(
            result,
            Err(AnalyzeError {
                kind: ErrorKind::IncompatibleTypes,
                ..
            })
        ));

        let result = RichExpr::from(
            &mut ctx,
            Expression::BinaryOperation(
                Box::new(Expression::I64Literal(2)),
                Operator::LogicalOr,
                Box::new(Expression::I64Literal(1)),
            ),
        );
        assert!(matches!(
            result,
            Err(AnalyzeError {
                kind: ErrorKind::IncompatibleTypes,
                ..
            })
        ));
    }

    #[test]
    fn unary_op() {
        let mut ctx = ProgramContext::new();
        let result = RichExpr::from(
            &mut ctx,
            Expression::UnaryOperation(Operator::Not, Box::new(Expression::I64Literal(1))),
        );
        assert!(matches!(
            result,
            Err(AnalyzeError {
                kind: ErrorKind::IncompatibleTypes,
                ..
            })
        ));
    }

    #[test]
    fn unary_op_invalid_operand_type() {
        let mut ctx = ProgramContext::new();
        let result = RichExpr::from(
            &mut ctx,
            Expression::UnaryOperation(
                Operator::Not,
                Box::new(Expression::StringLiteral("s".to_string())),
            ),
        );
        assert!(matches!(
            result,
            Err(AnalyzeError {
                kind: ErrorKind::IncompatibleTypes,
                ..
            })
        ));
    }
}
