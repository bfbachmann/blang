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
enum Value {
    String(String),
    Int(i64),
    Function(Function),
    Expression(Expression),
}

#[derive(Debug, PartialEq)]
enum Type {
    String,
    Int,
    Function(Box<FunctionSignature>),
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
}

#[derive(Debug, PartialEq)]
pub struct Expression {
    typ: Type,
}

impl Expression {
    fn new(typ: Type) -> Self {
        Expression { typ }
    }
}

#[derive(Debug)]
struct FunctionCall {
    fn_name: String,
    args: Vec<Value>,
}

impl PartialEq for FunctionCall {
    fn eq(&self, other: &Self) -> bool {
        self.fn_name == other.fn_name && util::vectors_are_equal(&self.args, &other.args)
    }
}

impl FunctionCall {
    fn new(fn_name: &str, args: Vec<Value>) -> Self {
        FunctionCall {
            fn_name: fn_name.to_string(),
            args,
        }
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
}

#[derive(Debug, PartialEq)]
pub enum Statement {
    VariableDeclaration(VariableDeclaration),
    VariableAssignment(VariableAssignment),
    FunctionDeclaration(Function),
    Closure(Closure),
    Expression(Expression),
}

#[derive(Debug)]
struct Closure {
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
}

pub enum ASTNode {}

impl ASTNode {
    // TODO
    fn parse_expression(
        tokens: &mut VecDeque<Token>,
        terminators: HashSet<TokenKind>,
    ) -> ParseResult<(Expression, TokenKind)> {
        // Collect up all the tokens until we hit one of the given terminator tokens.
        // TODO: This algorithm doesn't actually work.
        let mut expr_tokens = VecDeque::new();
        let terminator_kind: TokenKind;
        loop {
            match tokens.pop_front() {
                Some(token) => {
                    if terminators.contains(&token.kind) {
                        terminator_kind = token.kind;
                        break;
                    }

                    expr_tokens.push_back(token);
                }
                None => return Err(ParseError::new("Unexpected end of expression", None)),
            };
        }

        Ok((Expression::new(Type::String), terminator_kind))
    }

    /// Parses function calls. Expects token sequences of the form
    ///
    ///     <name>(<arg>, ...)
    ///
    /// where
    ///  - `name` is the name of the function being called
    ///  - `arg` is some expression that evaluates to the argument value
    fn parse_function_call(tokens: &mut VecDeque<Token>) -> ParseResult<FunctionCall> {
        // The first token should be the function name.
        let fn_name = ASTNode::parse_identifier(tokens)?;

        // The next token should be "(".
        ASTNode::parse_expecting(tokens, HashSet::from([TokenKind::OpenParen]))?;

        // The remaining tokens should be expressions representing argument values separated by ","
        // and ending in ")".
        let mut args = vec![];
        loop {
            let (expr, terminator) = ASTNode::parse_expression(
                tokens,
                HashSet::from([TokenKind::Comma, TokenKind::CloseParen]),
            )?;
            args.push(Value::Expression(expr));

            match terminator {
                TokenKind::CloseParen => break, // We've reached the end of the arguments.
                _ => {}                         // Move on to the next argument.
            }
        }

        Ok(FunctionCall::new(fn_name.as_str(), args))
    }

    /// Parses variable assignments. Expects token sequences of the form
    ///
    ///     <name> = <expr>
    ///
    /// where
    ///  - `name` is the variable name
    ///  - `expr` is an expression representing the value assigned to the variable
    fn parse_variable_assignment(tokens: &mut VecDeque<Token>) -> ParseResult<VariableAssignment> {
        // The next token should be an identifier representing the variable name.
        let name = ASTNode::parse_identifier(tokens)?;

        // The next token should be an assignment "=".
        ASTNode::parse_expecting(tokens, HashSet::from([TokenKind::Equal]))?;

        // The next tokens should be some expression ending in ";".
        let (expr, _) = ASTNode::parse_expression(tokens, HashSet::from([TokenKind::SemiColon]))?;

        Ok(VariableAssignment::new(name.as_str(), expr))
    }

    /// Parses variable declarations. Expects token sequences of the form
    ///
    ///     <type> <name> = <expr>
    ///
    /// where
    ///  - `type` is the variable type
    ///  - `name` is the variable name
    ///  - `expr` is an expression representing the value assigned to the variable
    fn parse_variable_declaration(
        tokens: &mut VecDeque<Token>,
    ) -> ParseResult<VariableDeclaration> {
        // The first token(s) should be the variable type.
        let var_type = ASTNode::parse_type(tokens)?;

        // The next tokens should take the form of a variable assignment.
        let assign = ASTNode::parse_variable_assignment(tokens)?;

        Ok(VariableDeclaration::new(
            var_type,
            assign.name,
            assign.value,
        ))
    }

    /// Parses a statement. Statements can be any of the following:
    ///  - variable declaration (see parse_variable_declaration)
    ///  - variable assignment (see parse_variable_assignment)
    ///  - function declaration (see parse_function)
    ///  - closure (see parse_closure)
    ///  - expression (see parse_expression)
    pub fn parse_statement(tokens: &mut VecDeque<Token>) -> ParseResult<Statement> {
        // Try use the first token to figure out what type of statement will follow.
        match tokens.front() {
            // If the first token is a type, it must be a variable declaration.
            Some(Token {
                kind: TokenKind::Int | TokenKind::String,
                start: _,
                end: _,
            }) => {
                let var_decl = ASTNode::parse_variable_declaration(tokens)?;
                Ok(Statement::VariableDeclaration(var_decl))
            }

            // If the first token is "fn", it must be a function declaration.
            Some(Token {
                kind: TokenKind::Function,
                start: _,
                end: _,
            }) => {
                let fn_decl = ASTNode::parse_function(tokens)?;
                Ok(Statement::FunctionDeclaration(fn_decl))
            }

            // If the first token is "{", it must be a closure.
            Some(Token {
                kind: TokenKind::BeginClosure,
                start: _,
                end: _,
            }) => {
                let closure = ASTNode::parse_closure(tokens)?;
                Ok(Statement::Closure(closure))
            }

            // If the token is anything else, we'll try parse it as an expression.
            Some(_) => {
                let (expr, _) =
                    ASTNode::parse_expression(tokens, HashSet::from([TokenKind::SemiColon]))?;
                Ok(Statement::Expression(expr))
            }

            // If there is no token, we error.
            None => Err(ParseError::new("Expected statement", None)),
        }
    }

    /// Parses closures. Expects token sequences of the form
    ///
    ///      { <statement> ... }
    ///
    /// where
    /// - `statement` is any valid statement (see parse_statement)
    fn parse_closure(tokens: &mut VecDeque<Token>) -> ParseResult<Closure> {
        // The first token should be "{".
        ASTNode::parse_expecting(tokens, HashSet::from([TokenKind::BeginClosure]))?;

        // The following nodes should be statements.
        let mut statements = vec![];
        loop {
            match tokens.front() {
                Some(Token {
                    kind: TokenKind::EndClosure,
                    start: _,
                    end: _,
                }) => {
                    // We've reached the end of the closure. Pop the "}" and break the loop.
                    tokens.pop_front();
                    break;
                }
                _ => {
                    let statement = ASTNode::parse_statement(tokens)?;
                    statements.push(statement);
                }
            };
        }

        // If the last statement is an expression, we use it as the return type.
        // TODO.

        Ok(Closure::new(statements, None))
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
    fn parse_args_and_return(tokens: &mut VecDeque<Token>) -> ParseResult<FunctionSignature> {
        // The next tokens should represent function arguments.
        let args = ASTNode::parse_argument_declarations(tokens)?;

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
                return_type = Some(ASTNode::parse_type(tokens)?);
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
    fn parse_anon_function_signature(
        tokens: &mut VecDeque<Token>,
    ) -> ParseResult<FunctionSignature> {
        // The first token should be "fn".
        ASTNode::parse_expecting(tokens, HashSet::from([TokenKind::Function]))?;

        // The next tokens should represent function arguments followed by the return type.
        let fn_sig = ASTNode::parse_args_and_return(tokens)?;
        Ok(fn_sig)
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
    fn parse_function_signature(tokens: &mut VecDeque<Token>) -> ParseResult<FunctionSignature> {
        // The first token should be "fn".
        ASTNode::parse_expecting(tokens, HashSet::from([TokenKind::Function]))?;

        // The second token should be an identifier that represents the function name.
        let fn_name = ASTNode::parse_identifier(tokens)?;

        // The next tokens should represent function arguments and optional return type.
        let fn_sig = ASTNode::parse_args_and_return(tokens)?;

        Ok(FunctionSignature::new(
            fn_name.as_str(),
            fn_sig.args,
            fn_sig.return_type,
        ))
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
    fn parse_function(tokens: &mut VecDeque<Token>) -> ParseResult<Function> {
        // The first set of tokens should be the function signature.
        let sig = ASTNode::parse_function_signature(tokens)?;

        // The remaining tokens should be the function body.
        let body = ASTNode::parse_closure(tokens)?;

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
    fn parse_anon_function(tokens: &mut VecDeque<Token>) -> ParseResult<Function> {
        // The first set of tokens should be the function signature.
        let sig = ASTNode::parse_anon_function_signature(tokens)?;

        // The remaining tokens should be the function body.
        let body = ASTNode::parse_closure(tokens)?;

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
    fn parse_argument_declarations(tokens: &mut VecDeque<Token>) -> ParseResult<Vec<Argument>> {
        // The first token should be the opening parenthesis.
        ASTNode::parse_expecting(tokens, HashSet::from([TokenKind::OpenParen]))?;

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
                    let arg = ASTNode::parse_argument_declaration(tokens)?;
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
            let kind = ASTNode::parse_expecting(
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

    /// Parses a function argument declaration. Expects token sequences of the form
    ///
    ///      <arg_type> <arg_name>
    ///
    /// where
    ///  - `arg_type` is the type of the argument
    ///  - `arg_name` is an identifier representing the argument name
    fn parse_argument_declaration(tokens: &mut VecDeque<Token>) -> ParseResult<Argument> {
        // The first token should be the argument type.
        let arg_type = ASTNode::parse_type(tokens)?;

        // The second token should be the argument name.
        let name = ASTNode::parse_identifier(tokens)?;

        Ok(Argument::new(name.as_str(), arg_type))
    }

    /// Parses types.
    fn parse_type(tokens: &mut VecDeque<Token>) -> ParseResult<Type> {
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
                let sig = ASTNode::parse_anon_function_signature(tokens)?;
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

    /// Parses identifiers.
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
        ASTNode, Argument, Closure, Expression, Function, FunctionCall, FunctionSignature,
        Statement, Type, Value, VariableDeclaration,
    };

    #[test]
    fn parse_identifier() {
        let mut tokens = Token::tokenize_line("something", 0).expect("should not error");
        let result = ASTNode::parse_identifier(&mut tokens).expect("should not error");
        assert_eq!(result, "something");
    }

    #[test]
    fn parse_function() {
        let mut tokens = Token::tokenize_line(
            r#"fn my_fn(string arg1, int arg2): string { string s = "hello world!"; }"#,
            0,
        )
        .expect("should not error");
        let result = ASTNode::parse_function(&mut tokens).expect("should not error");
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
                        Expression::new(Type::String),
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
        let result = ASTNode::parse_function(&mut tokens).expect("should not error");
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
        let result = ASTNode::parse_function_call(&mut tokens).expect("should not error");
        assert_eq!(
            result,
            FunctionCall::new(
                "do_thing",
                vec![
                    Value::Expression(Expression::new(Type::String)),
                    Value::Expression(Expression::new(Type::String)),
                ]
            )
        );
    }
}
