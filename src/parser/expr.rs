use crate::lexer::kind::TokenKind;
use crate::lexer::Token;
use crate::parser::error::ParseError;
use crate::parser::fn_call::FunctionCall;
use crate::parser::op::Operator;
use crate::parser::ParseResult;
use std::collections::{HashSet, VecDeque};

/// Represents basic and composite expressions. A basic expression can be any of the following:
///  - an identifier representing a variable value
///  - a literal value
///  - a function call
/// whereas a composite expression can be any token sequence of the form
///
///     <basic_expr> <op> <comp_expr>
///
/// where
///  - `basic_expr` is a basic expression
///  - `op` is an operator
///  - `comp_expr` is a composite expression
#[derive(Debug, PartialEq)]
pub enum Expression {
    // Basic expressions.
    VariableValue(String),
    BoolLiteral(bool),
    IntLiteral(i64),
    StringLiteral(String),
    FunctionCall(FunctionCall),

    // Composite expressions.
    Operator(Box<Expression>, Operator, Box<Expression>),
}

impl Expression {
    /// Parses a basic expression. A basic expression can be any of the following:
    ///  - an identifier representing a variable value
    ///  - a literal value
    ///  - a function call
    fn from_basic(tokens: &mut VecDeque<Token>) -> ParseResult<Expression> {
        match tokens.pop_front() {
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
                    &token
                ).as_str(),
                Some(token),
            )),

            // If there is no token, error.
            None => Err(ParseError::new("Unexpected end of expression", None)),
        }
    }

    /// Parses a basic or composite expression from the given tokens ending with any of the given
    /// terminator token kinds. Returns the parsed expression and the terminator token. A basic
    /// expression can be any of the following:
    ///  - an identifier representing a variable value
    ///  - a literal value
    ///  - a function call
    /// whereas a composite expression can be any token sequence of the form
    ///
    ///     <basic_expr> <op> <comp_expr>
    ///
    /// where
    ///  - `basic_expr` is a basic expression
    ///  - `op` is an operator
    ///  - `comp_expr` is a composite expression
    pub fn from(
        tokens: &mut VecDeque<Token>,
        terminators: HashSet<TokenKind>,
    ) -> ParseResult<(Expression, Token)> {
        // The first tokens should represent a basic expression.
        let left_expr = Expression::from_basic(tokens)?;

        // The next token should either be an operator or a terminator.
        match tokens.pop_front() {
            Some(token) => {
                if terminators.contains(&token.kind) {
                    // We've reached the end of the expression, so just return the basic expression
                    // we have.
                    return Ok((left_expr, token));
                }

                // At this point we know the token must be an operator.
                let bin_op = match token.kind {
                    TokenKind::Add => Operator::Add,
                    TokenKind::Subtract => Operator::Subtract,
                    TokenKind::Multiply => Operator::Multiply,
                    TokenKind::Divide => Operator::Divide,
                    TokenKind::Modulo => Operator::Modulo,
                    TokenKind::Equals => Operator::Equals,
                    TokenKind::GreaterThan => Operator::GreaterThan,
                    TokenKind::LessThan => Operator::LessThan,
                    TokenKind::GreaterThanOrEqual => Operator::GreaterThanOrEqual,
                    TokenKind::LessThanOrEqual => Operator::LessThanOrEqual,
                    _ => {
                        return Err(ParseError::new(
                            format!(r#"Expected operator, but got "{}""#, token).as_str(),
                            Some(token),
                        ))
                    }
                };

                // What remains of the expression (the right side) can be parsed recursively.
                let (right_expr, terminator) = Expression::from(tokens, terminators)?;
                Ok((
                    Expression::Operator(Box::new(left_expr), bin_op, Box::new(right_expr)),
                    terminator,
                ))
            }
            None => Err(ParseError::new("Unexpected end of expression", None)),
        }
    }
}
