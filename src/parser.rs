use crate::lexer::Token;
use crate::token_kind::TokenKind;
use crate::util;
use std::collections::{HashSet, VecDeque};
use std::fmt;

type ParseResult<T> = Result<T, ParseError>;

#[derive(Debug)]
pub struct ParseError {
    message: String,
    token: Option<Token>,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self.token {
            Some(token) => write!(f, "Parse error at token {}: {}.", token, self.message),
            None => write!(f, "Parse error: {}.", self.message),
        }
    }
}

impl ParseError {
    fn new(message: &str, token: Option<Token>) -> Self {
        ParseError {
            message: message.to_string(),
            token,
        }
    }
}

#[derive(Debug, PartialEq)]
enum Type {
    String,
    Int,
    Function(Box<FunctionSignature>),
}

impl Type {
    /// Parses types. Valid types are
    ///  - int
    ///  - string
    ///  - function
    fn from(tokens: &mut VecDeque<Token>) -> ParseResult<Self> {
        match tokens.pop_front() {
            Some(Token {
                kind: TokenKind::Int,
                start: _,
                end: _,
            }) => Ok(Type::Int),
            Some(Token {
                kind: TokenKind::String,
                start: _,
                end: _,
            }) => Ok(Type::String),
            Some(
                token @ Token {
                    kind: TokenKind::Function,
                    start: _,
                    end: _,
                },
            ) => {
                tokens.push_front(token);
                let sig = FunctionSignature::from_anon(tokens)?;
                Ok(Type::Function(Box::new(sig)))
            }
            None => return Err(ParseError::new("Expected type", None)),
            Some(other) => {
                return Err(ParseError::new(
                    format!(r#"Expected type, but got "{}""#, other).as_str(),
                    Some(other),
                ))
            }
        }
    }
}

#[derive(Debug, PartialEq)]
struct Argument {
    name: String,
    typ: Type,
}

impl Argument {
    fn new(name: &str, typ: Type) -> Self {
        Argument {
            name: name.to_string(),
            typ,
        }
    }

    /// Parses a function argument declaration. Expects token sequences of the form
    ///
    ///      <arg_type> <arg_name>
    ///
    /// where
    ///  - `arg_type` is the type of the argument
    ///  - `arg_name` is an identifier representing the argument name
    fn from(tokens: &mut VecDeque<Token>) -> ParseResult<Self> {
        // The first token should be the argument type.
        let arg_type = Type::from(tokens)?;

        // The second token should be the argument name.
        let name = Program::parse_identifier(tokens)?;

        Ok(Argument::new(name.as_str(), arg_type))
    }
}

#[derive(Debug)]
struct FunctionSignature {
    name: String,
    args: Vec<Argument>,
    return_type: Option<Type>,
}

impl PartialEq for FunctionSignature {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
            && util::vectors_are_equal(&self.args, &other.args)
            && self.return_type == other.return_type
    }
}

impl FunctionSignature {
    fn new(name: &str, args: Vec<Argument>, return_type: Option<Type>) -> Self {
        FunctionSignature {
            name: name.to_string(),
            args,
            return_type,
        }
    }

    fn new_anon(args: Vec<Argument>, return_type: Option<Type>) -> Self {
        FunctionSignature {
            name: "".to_string(),
            args,
            return_type,
        }
    }

    /// Parses function signatures. Expects token sequences of the forms
    ///
    ///      fn <fn_name>(<arg_type> <arg_name>, ...): (<return_type>, ...)
    ///      fn <fn_name>(<arg_type> <arg_name>, ...)
    ///
    /// where
    ///  - `fn_name` is an identifier representing the name of the function
    ///  - `arg_type` is the type of the argument
    ///  - `arg_name` is an identifier representing the argument name
    ///  - `return_type` is the type of the optional return type
    fn from(tokens: &mut VecDeque<Token>) -> ParseResult<Self> {
        // The first token should be "fn".
        Program::parse_expecting(tokens, HashSet::from([TokenKind::Function]))?;

        // The second token should be an identifier that represents the function name.
        let fn_name = Program::parse_identifier(tokens)?;

        // The next tokens should represent function arguments and optional return type.
        let fn_sig = FunctionSignature::from_args_and_return(tokens)?;

        Ok(FunctionSignature::new(
            fn_name.as_str(),
            fn_sig.args,
            fn_sig.return_type,
        ))
    }

    /// Parses function arguments and return value from a function signature. Expects token
    /// sequences of the forms
    ///
    ///     (<arg_type> <arg_name>, ...): <return_type>
    ///     (<arg_type> <arg_name>, ...)
    ///
    /// where
    ///  - `arg_type` is the type of the argument
    ///  - `arg_name` is an identifier representing the argument name
    ///  - `return_type` is the type of the optional return value
    fn from_args_and_return(tokens: &mut VecDeque<Token>) -> ParseResult<Self> {
        // The next tokens should represent function arguments.
        let args = Function::arg_declarations_from(tokens)?;

        // The next token should be ":" if there is a return type. Otherwise, there is no return
        // type and we're done.
        let mut return_type = None;
        match tokens.front() {
            Some(Token {
                kind: TokenKind::Colon,
                start: _,
                end: _,
            }) => {
                // Remove the ":" and parse the return type.
                tokens.pop_front();
                return_type = Some(Type::from(tokens)?);
            }
            _ => {}
        }

        Ok(FunctionSignature::new_anon(args, return_type))
    }

    /// Parses anonymous function signatures. Expects token sequences of the forms
    ///
    ///      fn (<arg_type> <arg_name>, ...): <return_type>
    ///      fn (<arg_type> <arg_name>, ...)
    ///
    /// where
    ///  - `arg_type` is the type of the argument
    ///  - `arg_name` is an identifier representing the argument name
    ///  - `return_type` is the type of the optional return type
    fn from_anon(tokens: &mut VecDeque<Token>) -> ParseResult<Self> {
        // The first token should be "fn".
        Program::parse_expecting(tokens, HashSet::from([TokenKind::Function]))?;

        // The next tokens should represent function arguments followed by the return type.
        let fn_sig = FunctionSignature::from_args_and_return(tokens)?;
        Ok(fn_sig)
    }
}

#[derive(Debug, PartialEq)]
pub enum BinaryOp {
    Add,
    Subtract,
    Multiply,
    Divide,
    Modulo,
}

#[derive(Debug, PartialEq)]
pub enum Expression {
    FunctionCall(FunctionCall),
    VariableValue(String),
    IntLiteral(i64),
    StringLiteral(String),
    BinaryOp(Box<Expression>, BinaryOp, Box<Expression>),
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
                    start: _,
                    end: _,
                },
            ) => {
                match tokens.front() {
                    // If the next token is "(", it's a function call.
                    Some(&Token {
                        kind: TokenKind::OpenParen,
                        start: _,
                        end: _,
                    }) => {
                        tokens.push_front(token);
                        let call = FunctionCall::from(tokens)?;
                        Ok(Expression::FunctionCall(call))
                    }

                    // If the next token is anything else, we'll assume it's a variable value.
                    _ => {
                        if let Token {
                            kind: TokenKind::Identifier(var_name),
                            start: _,
                            end: _,
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

            // Check if it's an integer literal.
            Some(Token {
                     kind: TokenKind::IntLiteral(i),
                     start: _,
                     end: _,
                 }) => Ok(Expression::IntLiteral(i)),

            // Check if it's a string literal.
            Some(Token {
                     kind: TokenKind::StringLiteral(s),
                     start: _,
                     end: _,
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
    /// terminator tokens. A basic expression can be any of the following:
    ///  - an identifier representing a variable value
    ///  - a literal value
    ///  - a function call
    /// whereas a composite expression can be any token sequence of the form
    ///
    ///     <basic_expr> <binary_op> <comp_expr>
    ///
    /// where
    ///  - `basic_expr` is a basic expression
    ///  - `binary_op` is a binary operator
    ///  - `comp_expr` is a composite expression
    fn from(
        tokens: &mut VecDeque<Token>,
        terminators: HashSet<TokenKind>,
    ) -> ParseResult<(Expression, TokenKind)> {
        // The first tokens should represent a basic expression.
        let left_expr = Expression::from_basic(tokens)?;

        // The next token should either be a binary operator or a terminator.
        match tokens.pop_front() {
            Some(token) => {
                if terminators.contains(&token.kind) {
                    // We've reached the end of the expression, so just return the basic expression
                    // we have.
                    return Ok((left_expr, token.kind));
                }

                // At this point we know the token must be a binary operator.
                let bin_op = match token.kind {
                    TokenKind::Add => BinaryOp::Add,
                    TokenKind::Subtract => BinaryOp::Subtract,
                    TokenKind::Multiply => BinaryOp::Multiply,
                    TokenKind::Divide => BinaryOp::Divide,
                    TokenKind::Modulo => BinaryOp::Modulo,
                    _ => {
                        return Err(ParseError::new(
                            format!(r#"Expected binary operator, but got "{}""#, token).as_str(),
                            Some(token),
                        ))
                    }
                };

                // What remains of the expression (the right side) can be parsed recursively.
                let (right_expr, terminator) = Expression::from(tokens, terminators)?;
                Ok((
                    Expression::BinaryOp(Box::new(left_expr), bin_op, Box::new(right_expr)),
                    terminator,
                ))
            }
            None => Err(ParseError::new("Unexpected end of expression", None)),
        }
    }
}

#[derive(Debug)]
pub struct FunctionCall {
    fn_name: String,
    args: Vec<Expression>,
}

impl PartialEq for FunctionCall {
    fn eq(&self, other: &Self) -> bool {
        self.fn_name == other.fn_name && util::vectors_are_equal(&self.args, &other.args)
    }
}

impl FunctionCall {
    fn new(fn_name: &str, args: Vec<Expression>) -> Self {
        FunctionCall {
            fn_name: fn_name.to_string(),
            args,
        }
    }

    /// Parses function calls. Expects token sequences of the form
    ///
    ///     <name>(<arg>, ...)
    ///
    /// where
    ///  - `name` is the name of the function being called
    ///  - `arg` is some expression that evaluates to the argument value
    fn from(tokens: &mut VecDeque<Token>) -> ParseResult<Self> {
        // The first token should be the function name.
        let fn_name = Program::parse_identifier(tokens)?;

        // The next token should be "(".
        Program::parse_expecting(tokens, HashSet::from([TokenKind::OpenParen]))?;

        // The remaining tokens should be expressions representing argument values separated by ","
        // and ending in ")".
        let mut args = vec![];
        let mut terminator = TokenKind::Comma;
        while terminator != TokenKind::CloseParen {
            // If the next token is ")", we're done parsing arguments.
            match tokens.front() {
                Some(&Token {
                    kind: TokenKind::CloseParen,
                    start: _,
                    end: _,
                }) => {
                    tokens.pop_front();
                    break;
                }
                _ => {}
            }

            // Try parse the next argument as an expression.
            let (expr, term) = Expression::from(
                tokens,
                HashSet::from([TokenKind::Comma, TokenKind::CloseParen]),
            )?;
            args.push(expr);
            terminator = term;
        }

        Ok(FunctionCall::new(fn_name.as_str(), args))
    }
}

#[derive(Debug, PartialEq)]
pub struct VariableAssignment {
    name: String,
    value: Expression,
}

impl VariableAssignment {
    fn new(name: &str, value: Expression) -> Self {
        VariableAssignment {
            name: name.to_string(),
            value,
        }
    }

    /// Parses variable assignments. Expects token sequences of the form
    ///
    ///     <name> = <expr>
    ///
    /// where
    ///  - `name` is the variable name
    ///  - `expr` is an expression representing the value assigned to the variable
    fn from(tokens: &mut VecDeque<Token>) -> ParseResult<Self> {
        // The next token should be an identifier representing the variable name.
        let name = Program::parse_identifier(tokens)?;

        // The next token should be an assignment "=".
        Program::parse_expecting(tokens, HashSet::from([TokenKind::Equal]))?;

        // The next tokens should be some expression ending in ";".
        let (expr, _) = Expression::from(tokens, HashSet::from([TokenKind::SemiColon]))?;

        Ok(VariableAssignment::new(name.as_str(), expr))
    }
}

#[derive(Debug, PartialEq)]
pub struct VariableDeclaration {
    typ: Type,
    name: String,
    value: Expression,
}

impl VariableDeclaration {
    fn new(typ: Type, name: String, value: Expression) -> Self {
        VariableDeclaration { typ, name, value }
    }

    /// Parses variable declarations. Expects token sequences of the form
    ///
    ///     <type> <name> = <expr>
    ///
    /// where
    ///  - `type` is the variable type
    ///  - `name` is the variable name
    ///  - `expr` is an expression representing the value assigned to the variable
    fn from(tokens: &mut VecDeque<Token>) -> ParseResult<Self> {
        // The first token(s) should be the variable type.
        let var_type = Type::from(tokens)?;

        // The next tokens should take the form of a variable assignment.
        let assign = VariableAssignment::from(tokens)?;

        Ok(VariableDeclaration::new(
            var_type,
            assign.name,
            assign.value,
        ))
    }
}

#[derive(Debug, PartialEq)]
pub enum Statement {
    VariableDeclaration(VariableDeclaration),
    VariableAssignment(VariableAssignment),
    FunctionDeclaration(Function),
    Closure(Closure),
    Expression(Expression),
    FunctionCall(FunctionCall),
}

impl Statement {
    /// Parses a statement. Statements can be any of the following:
    ///  - variable declaration (see VariableDeclaration::from)
    ///  - variable assignment (see VariableAssignment::from)
    ///  - function declaration (see Function::from)
    ///  - closure (see Closure::from)
    ///  - expression (see Expression::from)
    pub fn from(tokens: &mut VecDeque<Token>) -> ParseResult<Self> {
        // Try use the first two tokens to figure out what type of statement will follow. This works
        // because no valid statement can contain fewer than two tokens.
        let (first, second) = (tokens.front(), tokens.get(1));
        match (&first, &second) {
            (None, None) => return Err(ParseError::new("Unexpected end of of statement", None)),
            (None, Some(&ref token)) | (Some(&ref token), None) => {
                return Err(ParseError::new(
                    "Unexpected end of of statement",
                    Some(token.clone()),
                ))
            }
            _ => {}
        }

        match (
            first.expect("first token should not be None"),
            second.expect("second token should not be None"),
        ) {
            // If the first token is a type, it must be a variable declaration.
            (
                Token {
                    kind: TokenKind::Int | TokenKind::String,
                    start: _,
                    end: _,
                },
                _,
            ) => {
                let var_decl = VariableDeclaration::from(tokens)?;
                Ok(Statement::VariableDeclaration(var_decl))
            }

            // If the first two tokens are "<identifier> =", it must be a variable assignment.
            (
                Token {
                    kind: TokenKind::Identifier(_),
                    start: _,
                    end: _,
                },
                Token {
                    kind: TokenKind::Equal,
                    start: _,
                    end: _,
                },
            ) => {
                let assign = VariableAssignment::from(tokens)?;
                Ok(Statement::VariableAssignment(assign))
            }

            // If the first token is "fn", it must be a function declaration.
            (
                Token {
                    kind: TokenKind::Function,
                    start: _,
                    end: _,
                },
                _,
            ) => {
                let fn_decl = Function::from(tokens)?;
                Ok(Statement::FunctionDeclaration(fn_decl))
            }

            // If the first token is "{", it must be a closure.
            (
                Token {
                    kind: TokenKind::BeginClosure,
                    start: _,
                    end: _,
                },
                _,
            ) => {
                let closure = Closure::from(tokens)?;
                Ok(Statement::Closure(closure))
            }

            // If the first two tokens are "<identifier>(", it must be a function call.
            (
                Token {
                    kind: TokenKind::Identifier(_),
                    start: _,
                    end: _,
                },
                Token {
                    kind: TokenKind::OpenParen,
                    start: _,
                    end: _,
                },
            ) => {
                let call = FunctionCall::from(tokens)?;
                Ok(Statement::FunctionCall(call))
            }

            // If the tokens are anything else, we'll try parse as an expression.
            (_, _) => {
                let (expr, _) = Expression::from(tokens, HashSet::from([TokenKind::SemiColon]))?;
                Ok(Statement::Expression(expr))
            }
        }
    }
}

#[derive(Debug)]
pub struct Closure {
    statements: Vec<Statement>,
    result: Option<Expression>,
}

impl PartialEq for Closure {
    fn eq(&self, other: &Self) -> bool {
        util::vectors_are_equal(&self.statements, &other.statements) && self.result == other.result
    }
}

impl Closure {
    fn new(statements: Vec<Statement>, result: Option<Expression>) -> Self {
        Closure { statements, result }
    }

    /// Parses closures. Expects token sequences of the form
    ///
    ///      { <statement>; ... }
    ///
    /// where
    /// - `statement` is any valid statement (see Statement::from)
    fn from(tokens: &mut VecDeque<Token>) -> ParseResult<Self> {
        // The first token should be "{".
        Program::parse_expecting(tokens, HashSet::from([TokenKind::BeginClosure]))?;

        // The following nodes should be statements separated by ";".
        let mut statements = vec![];
        loop {
            match tokens.front() {
                // If the next token is "}", we've reached the end of the closure.
                Some(&Token {
                    kind: TokenKind::EndClosure,
                    start: _,
                    end: _,
                }) => {
                    // We've reached the end of the closure. Pop the "}" and break the loop.
                    tokens.pop_front();
                    break;
                }

                // If the next token is ";", we've reached the end of the statement.
                Some(&Token {
                    kind: TokenKind::SemiColon,
                    start: _,
                    end: _,
                }) => {
                    tokens.pop_front();
                }

                // If the next token is anything else, we expect it to be the beginning of a new
                // statement.
                _ => {
                    let statement = Statement::from(tokens)?;
                    statements.push(statement);
                }
            };
        }

        // If the last statement is an expression, we use it as the return type.
        // TODO.

        Ok(Closure::new(statements, None))
    }
}

#[derive(Debug, PartialEq)]
pub struct Function {
    signature: FunctionSignature,
    body: Closure,
}

impl Function {
    fn new(signature: FunctionSignature, body: Closure) -> Self {
        Function { signature, body }
    }

    /// Parses function declarations. Expects token sequences of the form
    ///
    ///      fn <fn_name>(<arg_type> <arg_name>, ...): <return_type> { <body> }
    ///      fn <fn_name>(<arg_type> <arg_name>, ...) { <body> }
    ///
    /// where
    ///  - `fn_name` is an identifier representing the name of the function
    ///  - `arg_type` is the type of the argument
    ///  - `arg_name` is an identifier representing the argument name
    ///  - `return_type` is the type of the optional return type
    ///  - `body` is the body of the function
    fn from(tokens: &mut VecDeque<Token>) -> ParseResult<Self> {
        // The first set of tokens should be the function signature.
        let sig = FunctionSignature::from(tokens)?;

        // The remaining tokens should be the function body.
        let body = Closure::from(tokens)?;

        // Now that we have the function name and args, create the node.
        Ok(Function::new(sig, body))
    }

    /// Parses anonymous function declarations. Expects token sequences of the forms
    ///
    ///      fn (<arg_type> <arg_name>, ...): <return_type> { <body> }
    ///      fn (<arg_type> <arg_name>, ...) { <body> }
    ///
    /// where
    ///  - `fn_name` is an identifier representing the name of the function
    ///  - `arg_type` is the type of the argument
    ///  - `arg_name` is an identifier representing the argument name
    ///  - `return_type` is the type of the optional return type
    ///  - `body` is the body of the function
    fn from_anon(tokens: &mut VecDeque<Token>) -> ParseResult<Self> {
        // The first set of tokens should be the function signature.
        let sig = FunctionSignature::from_anon(tokens)?;

        // The remaining tokens should be the function body.
        let body = Closure::from(tokens)?;

        // Now that we have the function name and args, create the node.
        Ok(Function::new(sig, body))
    }

    /// Parses argument declarations in function declarations. Expects token sequences of the form
    ///
    ///      (<arg_type> <arg_name>, ...)
    ///
    /// where
    ///  - `arg_type` is the type of the argument
    ///  - `arg_name` is an identifier representing the argument name
    fn arg_declarations_from(tokens: &mut VecDeque<Token>) -> ParseResult<Vec<Argument>> {
        // The first token should be the opening parenthesis.
        Program::parse_expecting(tokens, HashSet::from([TokenKind::OpenParen]))?;

        // The next token(s) should be arguments or a closing parenthesis.
        let mut args = vec![];
        loop {
            // The next token should be an argument, or ")".
            let token = tokens.pop_front();
            match token {
                Some(Token {
                    kind: TokenKind::CloseParen,
                    start: _,
                    end: _,
                }) => {
                    // We're done assembling arguments.
                    break;
                }
                Some(Token {
                    kind: TokenKind::String | TokenKind::Int | TokenKind::Function,
                    start: _,
                    end: _,
                }) => {
                    // The next few tokens represent an argument.
                    tokens.push_front(token.unwrap());
                    let arg = Argument::from(tokens)?;
                    args.push(arg);
                }
                None => {
                    return Err(ParseError::new(
                        r#"Expected argument or ")" (end of function arguments)"#,
                        None,
                    ))
                }
                Some(other) => {
                    return Err(ParseError::new(
                        format!(
                            r#"Expected argument or ")" (end of function arguments), but got "{}""#,
                            other
                        )
                        .as_str(),
                        Some(other),
                    ))
                }
            };

            // After the argument, the next token should be "," or ")".
            let kind = Program::parse_expecting(
                tokens,
                HashSet::from([TokenKind::Comma, TokenKind::CloseParen]),
            )?;
            match kind {
                TokenKind::Comma => {} // Nothing to do here. Just move onto the next arg.
                TokenKind::CloseParen => break, // We're done parsing args.
                _ => panic!("this should be impossible"),
            }
        }

        Ok(args)
    }
}

#[derive(Debug)]
pub struct Program {
    statements: Vec<Statement>,
}

impl Program {
    /// Attempts to parse a program from the deque of tokens. Expects token sequences of the form
    ///
    ///     <statement>; ...
    ///
    /// where
    ///  - `statement` is a valid statement (see Statement::from)
    pub fn from(tokens: &mut VecDeque<Token>) -> ParseResult<Self> {
        let mut statements = vec![];
        while !tokens.is_empty() {
            match Statement::from(tokens) {
                Ok(statement) => statements.push(statement),
                Err(err) => return Err(err),
            };
        }

        Ok(Program { statements })
    }

    /// Returns an error if the next token is not any of the given kinds, or the kind otherwise.
    fn parse_expecting(
        tokens: &mut VecDeque<Token>,
        expected: HashSet<TokenKind>,
    ) -> ParseResult<TokenKind> {
        match tokens.pop_front() {
            None => {
                return Err(ParseError::new(
                    format!(r#"Expected one of {:#?}"#, expected).as_str(),
                    None,
                ))
            }
            Some(token) => {
                if expected.contains(&token.kind) {
                    Ok(token.kind)
                } else {
                    Err(ParseError::new(
                        format!(r#"Expected one of {:#?}, but got "{}"#, expected, token).as_str(),
                        Some(token),
                    ))
                }
            }
        }
    }

    /// Parses an identifier, returning its name.
    fn parse_identifier(tokens: &mut VecDeque<Token>) -> ParseResult<String> {
        match tokens.pop_front() {
            Some(Token {
                kind: TokenKind::Identifier(name),
                start: _,
                end: _,
            }) => Ok(name),
            None => return Err(ParseError::new("Expected identifier", None)),
            Some(other) => {
                return Err(ParseError::new(
                    format!(r#"Expected identifier, but got "{}""#, other).as_str(),
                    Some(other),
                ))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::lexer::Token;
    use crate::parser::{
        Argument, Closure, Expression, Function, FunctionCall, FunctionSignature, Program,
        Statement, Type, VariableDeclaration,
    };

    #[test]
    fn parse_identifier() {
        let mut tokens = Token::tokenize_line("something", 0).expect("should not error");
        let result = Program::parse_identifier(&mut tokens).expect("should not error");
        assert_eq!(result, "something");
    }

    #[test]
    fn parse_function_declaration() {
        let mut tokens = Token::tokenize_line(
            r#"fn my_fn(string arg1, int arg2): string { string s = "hello world!"; }"#,
            0,
        )
        .expect("should not error");
        let result = Function::from(&mut tokens).expect("should not error");
        assert_eq!(
            result,
            Function::new(
                FunctionSignature::new(
                    "my_fn",
                    vec![
                        Argument::new("arg1", Type::String),
                        Argument::new("arg2", Type::Int)
                    ],
                    Some(Type::String),
                ),
                Closure::new(
                    vec![Statement::VariableDeclaration(VariableDeclaration::new(
                        Type::String,
                        "s".to_string(),
                        Expression::StringLiteral("hello world!".to_string()),
                    )),],
                    None
                ),
            )
        );

        let mut tokens = Token::tokenize_line(
            "fn bigboi(fn (string b1, int b2) f, int i): fn (int r): string {}",
            0,
        )
        .expect("should not error");
        let result = Function::from(&mut tokens).expect("should not error");
        assert_eq!(
            result,
            Function::new(
                FunctionSignature::new(
                    "bigboi",
                    vec![
                        Argument::new(
                            "f",
                            Type::Function(Box::new(FunctionSignature::new_anon(
                                vec![
                                    Argument::new("b1", Type::String),
                                    Argument::new("b2", Type::Int)
                                ],
                                None,
                            ))),
                        ),
                        Argument::new("i", Type::Int)
                    ],
                    Some(Type::Function(Box::new(FunctionSignature::new_anon(
                        vec![Argument::new("r", Type::Int)],
                        Some(Type::String),
                    )))),
                ),
                Closure::new(vec![], None),
            )
        );
    }

    #[test]
    fn parse_function_call() {
        let mut tokens =
            Token::tokenize_line(r#"do_thing("one", "two")"#, 0).expect("should not error");
        let result = FunctionCall::from(&mut tokens).expect("should not error");
        assert_eq!(
            result,
            FunctionCall::new(
                "do_thing",
                vec![
                    Expression::StringLiteral("one".to_string()),
                    Expression::StringLiteral("two".to_string()),
                ]
            )
        );
    }
}
