use crate::lexer::kind::TokenKind;
use crate::lexer::Token;
use crate::parser::error::ParseError;
use crate::parser::fn_call::FunctionCall;
use crate::parser::op::Operator;
use crate::parser::r#fn::Function;
use crate::parser::ParseResult;
use std::collections::VecDeque;

/// Represents basic and composite expressions. A basic expression can be any of the following:
///  - an identifier representing a variable value
///  - a literal value
///  - a function call
///  - a unary operator followed by a composite expression (`<unary_op> <comp_expr>`)
/// whereas a composite expression can be any token sequence of the forms
///
///     <basic_expr> <binary_op> <comp_expr>
///
/// where
///  - `basic_expr` is a basic expression
///  - `binary_op` is a binary operator
///  - `comp_expr` is a composite expression
#[derive(Debug, PartialEq)]
pub enum Expression {
    // Basic expressions.
    VariableValue(String),
    BoolLiteral(bool),
    IntLiteral(i64),
    StringLiteral(String),
    FunctionCall(FunctionCall),
    AnonFunction(Box<Function>),

    // Composite expressions.
    BinaryOperation(Box<Expression>, Operator, Box<Expression>),
    UnaryOperation(Operator, Box<Expression>),
}

impl Expression {
    /// Parses a basic expression. A basic expression can be any of the following:
    ///  - an identifier representing a variable value
    ///  - a literal value (includes anonymous functions)
    ///  - a function call
    ///  - a unary operator followed by a composite expression (`<unary_op> <comp_expr>`)
    fn from_basic(tokens: &mut VecDeque<Token>) -> ParseResult<Expression> {
        match tokens.pop_front() {
            // If the first token is "fn", we'll assume the expression is an anonymous function.
            Some(
                token @ Token {
                    kind: TokenKind::Function,
                    ..
                },
            ) => {
                // Put the "fn" token back because it's expected by Function::from_anon.
                tokens.push_front(token);

                // Parse the anonymous function and return it.
                let func = Function::from_anon(tokens)?;
                Ok(Expression::AnonFunction(Box::new(func)))
            }

            // If the first token is an identifier, the expression can either be a function call
            // or a variable value.
            Some(
                token @ Token {
                    kind: TokenKind::Identifier(_),
                    ..
                },
            ) => {
                match tokens.front() {
                    // If the next token is "(", it's a function call.
                    Some(&Token {
                        kind: TokenKind::OpenParen,
                        ..
                    }) => {
                        tokens.push_front(token);
                        let call = FunctionCall::from(tokens)?;
                        Ok(Expression::FunctionCall(call))
                    }

                    // If the next token is anything else, we'll assume it's a variable value.
                    _ => {
                        if let Token {
                            kind: TokenKind::Identifier(var_name),
                            ..
                        } = token
                        {
                            Ok(Expression::VariableValue(var_name))
                        } else {
                            // This should be impossible because we know the token is an identifier.
                            Err(ParseError::new(
                                r#"Expected identifier, but got "{}""#,
                                Some(token),
                            ))
                        }
                    }
                }
            }

            // If the first token is a unary operator, we know the rest should be a composite
            // expression.
            Some(
                token @ Token {
                    kind: TokenKind::Not,
                    ..
                },
            ) => {
                let op = Operator::from(&token.kind).expect("operator should not be None");
                let expr = Expression::from(tokens)?;
                Ok(Expression::UnaryOperation(op, Box::new(expr)))
            }

            // Check if it's a bool literal.
            Some(Token {
                kind: TokenKind::BoolLiteral(b),
                ..
            }) => Ok(Expression::BoolLiteral(b)),

            // Check if it's an integer literal.
            Some(Token {
                kind: TokenKind::IntLiteral(i),
                ..
            }) => Ok(Expression::IntLiteral(i)),

            // Check if it's a string literal.
            Some(Token {
                kind: TokenKind::StringLiteral(s),
                ..
            }) => Ok(Expression::StringLiteral(s)),

            // If the token is anything else, error.
            Some(token) => Err(ParseError::new(
                format!(
                    r#"Invalid expression: Expected literal value, variable value, or function call, but got "{}""#,
                    token
                )
                .as_str(),
                Some(token),
            )),

            // If there is no token, error.
            None => Err(ParseError::new("Unexpected end of expression", None)),
        }
    }

    /// Parses a basic or composite expression from the given tokens. A basic expression can be any
    /// of the following:
    ///  - an identifier representing a variable value
    ///  - a literal value
    ///  - a function call
    ///  - a unary operator followed by a composite expression (`<unary_op> <comp_expr>`)
    /// whereas a composite expression can be any token sequence of the form
    ///
    ///     <basic_expr> <binary_op> <comp_expr>
    ///
    /// where
    ///  - `basic_expr` is a basic expression
    ///  - `binary_op` is a binary operator
    ///  - `comp_expr` is a composite expression
    pub fn from(tokens: &mut VecDeque<Token>) -> ParseResult<Expression> {
        // The first tokens should represent a basic expression.
        let left_expr = Expression::from_basic(tokens)?;

        // If the next token is a binary operator, this is a compound expression. Otherwise, we
        // assume that we have a basic expression and we're done parsing.
        match tokens.front() {
            Some(token) => {
                let binary_op = Operator::from(&token.kind);
                match binary_op {
                    Some(
                        Operator::Add
                        | Operator::Subtract
                        | Operator::Multiply
                        | Operator::Divide
                        | Operator::Modulo
                        | Operator::LogicalAnd
                        | Operator::LogicalOr
                        | Operator::EqualTo
                        | Operator::NotEqualTo
                        | Operator::GreaterThan
                        | Operator::LessThan
                        | Operator::GreaterThanOrEqual
                        | Operator::LessThanOrEqual,
                    ) => {
                        // The token is a binary operator, so what remains of the expression (the
                        // right side) can be parsed recursively. Pop the operator and parse the
                        // expression.
                        tokens.pop_front();
                        let right_expr = Expression::from(tokens)?;
                        Ok(Expression::BinaryOperation(
                            Box::new(left_expr),
                            binary_op.expect("binary op should not be None"),
                            Box::new(right_expr),
                        ))
                    }
                    Some(_) => {
                        // The token is an operator, but not a binary operator.
                        Err(ParseError::new(
                            format!(r#"Expected binary operator, but got "{}""#, token).as_str(),
                            Some(token.clone()),
                        ))
                    }
                    None => {
                        // The token is not an operator, so we assume we have a basic expression.
                        Ok(left_expr)
                    }
                }
            }
            None => Ok(left_expr),
        }
    }
}
