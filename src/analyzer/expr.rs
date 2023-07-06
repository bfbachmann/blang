use crate::analyzer::closure::analyze_closure;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::func::analyze_fn_call;
use crate::analyzer::prog_context::{ProgramContext, ScopeKind};
use crate::analyzer::AnalyzeResult;
use crate::parser::expr::Expression;
use crate::parser::op::Operator;
use crate::parser::r#type::Type;

pub fn analyze_expr(ctx: &mut ProgramContext, expr: &Expression) -> AnalyzeResult<Type> {
    match expr {
        Expression::VariableReference(ref var_name) => {
            // Make sure the variable being referenced exists.
            match ctx.get_var(var_name.as_str()) {
                Some(&ref var_dec) => Ok(var_dec.typ.clone()),
                None => Err(AnalyzeError::new_from_expr(
                    ErrorKind::VariableNotDefined,
                    &expr,
                    format!("Variable {} does not exist", var_name).as_str(),
                )),
            }
        }
        Expression::BoolLiteral(_) => Ok(Type::Bool),
        Expression::I64Literal(_) => Ok(Type::I64),
        Expression::StringLiteral(_) => Ok(Type::String),
        Expression::FunctionCall(ref fn_call) => match analyze_fn_call(ctx, fn_call)? {
            Some(typ) => Ok(typ),
            None => Err(AnalyzeError::new(
                ErrorKind::ExpectedValue,
                format!(
                    r#"Function {} has no return value, but was used in an expression \
                            where a value is expected"#,
                    fn_call.fn_name,
                )
                .as_str(),
            )),
        },
        Expression::AnonFunction(anon_fn) => {
            // We don't need to analyze the function signature, since it has no name. Just analyze
            // the function body.
            analyze_closure(
                ctx,
                &anon_fn.body,
                ScopeKind::FnBody,
                anon_fn.signature.args.clone(),
                anon_fn.signature.return_type.clone(),
            )?;

            Ok(Type::Function(Box::new(anon_fn.signature.clone())))
        }
        Expression::UnaryOperation(ref op, ref right_expr) => match op {
            Operator::Not => {
                // Make sure the expression has type bool.
                match analyze_expr(ctx, right_expr)? {
                    Type::Bool => Ok(Type::Bool),
                    other => Err(AnalyzeError::new_from_expr(
                        ErrorKind::IncompatibleTypes,
                        &expr,
                        format!(
                            r#"Unary operator ! can only be applied to \
                            values of type bool, but found type {}"#,
                            other,
                        )
                        .as_str(),
                    )),
                }
            }
            other => {
                // If this happens, the parser is badly broken.
                panic!("invalid unary operator {}", other)
            }
        },
        Expression::BinaryOperation(ref left_expr, ref op, ref right_expr) => {
            let left_type = analyze_expr(ctx, left_expr)?;
            let right_type = analyze_expr(ctx, right_expr)?;
            let (expected_type, result_type) = match op {
                // Mathematical operators only work on numeric types.
                Operator::Add
                | Operator::Subtract
                | Operator::Multiply
                | Operator::Divide
                | Operator::Modulo => (Some(Type::I64), Type::I64),
                // Logical operators only work on bools.
                Operator::LogicalAnd | Operator::LogicalOr => (Some(Type::Bool), Type::Bool),
                // Equality operators work on anything.
                Operator::EqualTo | Operator::NotEqualTo => (None, Type::Bool),
                // Comparators only work on numeric types.
                Operator::GreaterThan
                | Operator::LessThan
                | Operator::GreaterThanOrEqual
                | Operator::LessThanOrEqual => (Some(Type::I64), Type::Bool),
                // If this happens, the parser is badly broken.
                other => panic!("unexpected operator {}", other),
            };

            // If there is an expected type, make sure the left and right expressions match the
            // type. Otherwise, we just make sure both the left and right expression types match.
            if let Some(expected) = expected_type {
                if left_type != expected {
                    return Err(AnalyzeError::new_from_expr(
                        ErrorKind::IncompatibleTypes,
                        &expr,
                        format!(
                            r#"Cannot apply operator {} to left-side \
                            expression of type {}"#,
                            op, left_type
                        )
                        .as_str(),
                    ));
                }

                if right_type != expected {
                    return Err(AnalyzeError::new_from_expr(
                        ErrorKind::IncompatibleTypes,
                        &expr,
                        format!(
                            "Cannot apply operator {} to right-side expression type {}",
                            op, right_type
                        )
                        .as_str(),
                    ));
                }
            } else if left_type != right_type {
                return Err(AnalyzeError::new_from_expr(
                    ErrorKind::IncompatibleTypes,
                    &expr,
                    format!("Incompatible types {} and {}", left_type, right_type).as_str(),
                ));
            }

            Ok(result_type)
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::analyzer::error::{AnalyzeError, ErrorKind};
    use crate::analyzer::expr::analyze_expr;
    use crate::analyzer::prog_context::ProgramContext;
    use crate::parser::arg::Argument;
    use crate::parser::closure::Closure;
    use crate::parser::expr::Expression;
    use crate::parser::func::Function;
    use crate::parser::func_call::FunctionCall;
    use crate::parser::func_sig::FunctionSignature;
    use crate::parser::op::Operator;
    use crate::parser::r#type::Type;
    use crate::parser::var_dec::VariableDeclaration;

    #[test]
    fn analyze_i64_literal() {
        let mut ctx = ProgramContext::new();
        let expr = Expression::I64Literal(1);
        let result = analyze_expr(&mut ctx, &expr);
        assert!(matches!(result, Ok(Type::I64)));
    }

    #[test]
    fn analyze_bool_literal() {
        let mut ctx = ProgramContext::new();
        let expr = Expression::BoolLiteral(false);
        let result = analyze_expr(&mut ctx, &expr);
        assert!(matches!(result, Ok(Type::Bool)));
    }

    #[test]
    fn analyze_string_literal() {
        let mut ctx = ProgramContext::new();
        let expr = Expression::StringLiteral("test".to_string());
        let result = analyze_expr(&mut ctx, &expr);
        assert!(matches!(result, Ok(Type::String)));
    }

    #[test]
    fn analyze_var_ref() {
        let mut ctx = ProgramContext::new();
        ctx.add_var(VariableDeclaration::new(
            Type::String,
            "myvar".to_string(),
            Expression::StringLiteral("hello".to_string()),
        ));
        let result = analyze_expr(
            &mut ctx,
            &Expression::VariableReference("myvar".to_string()),
        );
        assert!(matches!(result, Ok(Type::String)));
    }

    #[test]
    fn analyze_invalid_var_ref() {
        let mut ctx = ProgramContext::new();
        let result = analyze_expr(
            &mut ctx,
            &Expression::VariableReference("myvar".to_string()),
        );
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
        ctx.add_fn(Function::new(
            FunctionSignature::new(
                "do_thing",
                vec![Argument::new("first", Type::Bool)],
                Some(Type::String),
            ),
            Closure::new(vec![], None),
        ));
        let result = analyze_expr(
            &mut ctx,
            &Expression::FunctionCall(FunctionCall::new(
                "do_thing",
                vec![Expression::BoolLiteral(true)],
            )),
        );
        assert!(matches!(result, Ok(Type::String)));
    }

    #[test]
    fn fn_call_no_return() {
        let mut ctx = ProgramContext::new();
        ctx.add_fn(Function::new(
            FunctionSignature::new("do_thing", vec![], None),
            Closure::new(vec![], None),
        ));
        let result = analyze_expr(
            &mut ctx,
            &Expression::BinaryOperation(
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
        ctx.add_fn(Function::new(
            FunctionSignature::new("do_thing", vec![Argument::new("arg", Type::Bool)], None),
            Closure::new(vec![], None),
        ));
        let result = analyze_expr(
            &mut ctx,
            &Expression::BinaryOperation(
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
        ctx.add_fn(Function::new(
            FunctionSignature::new("do_thing", vec![Argument::new("arg", Type::Bool)], None),
            Closure::new(vec![], None),
        ));
        let result = analyze_expr(
            &mut ctx,
            &Expression::BinaryOperation(
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
        let result = analyze_expr(
            &mut ctx,
            &Expression::BinaryOperation(
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

        let result = analyze_expr(
            &mut ctx,
            &Expression::BinaryOperation(
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

        let result = analyze_expr(
            &mut ctx,
            &Expression::BinaryOperation(
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
        let result = analyze_expr(
            &mut ctx,
            &Expression::UnaryOperation(Operator::Not, Box::new(Expression::I64Literal(1))),
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
        let result = analyze_expr(
            &mut ctx,
            &Expression::UnaryOperation(
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
