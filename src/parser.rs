use crate::lexer::{Token, TokenKind};
use crate::util;
use std::collections::VecDeque;
use std::fmt;

#[derive(Debug)]
struct ParseError {
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

#[derive(Debug)]
enum Type {
    String,
    Int,
    Function(FunctionSignature),
}

impl PartialEq for Type {
    fn eq(&self, other: &Self) -> bool {
        match (&self, other) {
            (Type::String, Type::String) | (Type::Int, Type::Int) => true,
            (Type::Function(f1), Type::Function(f2)) => f1 == f2,
            _ => false,
        }
    }
}

#[derive(Debug)]
struct Argument {
    name: String,
    arg_type: Type,
}

impl PartialEq for Argument {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name && self.arg_type == other.arg_type
    }
}

impl Argument {
    fn new(name: &str, arg_type: Type) -> Self {
        Argument {
            name: name.to_string(),
            arg_type,
        }
    }
}

#[derive(Debug)]
struct FunctionSignature {
    name: String,
    args: Vec<Argument>,
    return_types: Vec<Type>,
}

impl PartialEq for FunctionSignature {
    fn eq(&self, other: &Self) -> bool {
        if self.name != other.name {
            return false;
        }

        if !util::vectors_are_equal(&self.args, &other.args) {
            return false;
        }

        if !util::vectors_are_equal(&self.return_types, &other.return_types) {
            return false;
        }

        true
    }
}

impl FunctionSignature {
    fn new(name: &str, args: Vec<Argument>, return_types: Vec<Type>) -> Self {
        FunctionSignature {
            name: name.to_string(),
            args,
            return_types,
        }
    }

    fn new_anon(args: Vec<Argument>, return_types: Vec<Type>) -> Self {
        FunctionSignature {
            name: "".to_string(),
            args,
            return_types,
        }
    }
}

#[derive(Debug)]
struct Closure {
    // TODO
}

impl PartialEq for Closure {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}

impl Closure {
    fn new() -> Self {
        Closure {}
    }
}

#[derive(Debug)]
struct Function {
    signature: FunctionSignature,
    body: Closure,
}

impl PartialEq for Function {
    fn eq(&self, other: &Self) -> bool {
        self.signature == other.signature && self.body == other.body
    }
}

impl Function {
    fn new(signature: FunctionSignature, body: Closure) -> Self {
        Function { signature, body }
    }
}

enum ASTNode {}

impl ASTNode {
    // Parses closures.
    // Expects token sequences of the form
    //      { [<statement> ... ] }
    // where
    //      statement is any valid statement (see parse_statement)
    fn parse_closure(tokens: &mut VecDeque<Token>) -> Result<Closure, ParseError> {
        // The first token should be "{".
        ASTNode::parse_expecting(tokens, vec![TokenKind::BeginClosure])?;

        // The following nodes should be statements.
        // TODO

        // The last node should be "}".
        ASTNode::parse_expecting(tokens, vec![TokenKind::EndClosure])?;

        Ok(Closure::new())
    }

    // Parses anonymous function signatures.
    // Expects token sequences of the form
    //      fn ([<arg_type> <arg_name>, ...]) (<return_type>, ...)
    // where
    //      arg_type is the type of the argument
    //      arg_name is an identifier representing the argument name
    //      return_type is the type of the return value
    fn parse_anon_function_signature(
        tokens: &mut VecDeque<Token>,
    ) -> Result<FunctionSignature, ParseError> {
        // The first token should be "fn".
        ASTNode::parse_expecting(tokens, vec![TokenKind::Function])?;

        // The next tokens should represent function arguments.
        let args = ASTNode::parse_arguments(tokens)?;

        // The next tokens should represent function return types.
        let return_types = ASTNode::parse_return_types(tokens)?;

        Ok(FunctionSignature::new_anon(args, return_types))
    }

    // Parses function signatures.
    // Expects token sequences of the form
    //      fn <fn_name>([<arg_type> <arg_name>, ...]) (<return_type>, ...)
    // where
    //      fn_name is an identifier representing the name of the function
    //      arg_type is the type of the argument
    //      arg_name is an identifier representing the argument name
    //      return_type is the type of the return value
    fn parse_function_signature(
        tokens: &mut VecDeque<Token>,
    ) -> Result<FunctionSignature, ParseError> {
        // The first token should be "fn".
        ASTNode::parse_expecting(tokens, vec![TokenKind::Function])?;

        // The second token should be an identifier that represents the function name.
        let fn_name = ASTNode::parse_identifier(tokens)?;

        // The next tokens should represent function arguments.
        let args = ASTNode::parse_arguments(tokens)?;

        // The next tokens should represent function return types.
        let return_types = ASTNode::parse_return_types(tokens)?;

        Ok(FunctionSignature::new(fn_name.as_str(), args, return_types))
    }

    // Parses function return types.
    // Expects token sequences of the form
    //      ([<return_type>, ...])
    // where
    //      return_type is the type of the return value
    fn parse_return_types(tokens: &mut VecDeque<Token>) -> Result<Vec<Type>, ParseError> {
        // The first token should be "(".
        ASTNode::parse_expecting(tokens, vec![TokenKind::OpenParen])?;

        let mut return_types = vec![];
        loop {
            // The next token should either be a return type, or ")".
            match tokens.pop_front() {
                Some(Token {
                    kind: TokenKind::CloseParen,
                    start: _,
                    end: _,
                }) => break,
                Some(other) => {
                    tokens.push_front(other);
                    let return_type = ASTNode::parse_type(tokens)?;
                    return_types.push(return_type);
                }
                None => return Err(ParseError::new(r#"Expected ")" or type"#, None)),
            };

            // After the return type, the next token should be "," or ")".
            let kind =
                ASTNode::parse_expecting(tokens, vec![TokenKind::Comma, TokenKind::CloseParen])?;
            match kind {
                TokenKind::Comma => {} // Nothing to do here. Just move onto the next type.
                TokenKind::CloseParen => break, // We're done parsing return types.
                _ => {
                    panic!("this should be impossible")
                }
            }
        }

        Ok(return_types)
    }

    // Parses anonymous function declarations.
    // Expects token sequences of the form
    //      ([<arg_type> <arg_name>, ...]) (<return_type>, ...) { ... }
    // where
    //      arg_type is the type of the argument
    //      arg_name is an identifier representing the argument name
    //      return_type is the type of the return value
    fn parse_anon_function(tokens: &mut VecDeque<Token>) -> Result<Function, ParseError> {
        // The first set of tokens should be the anonymous function signature.
        let sig = ASTNode::parse_anon_function_signature(tokens)?;

        // The remaining tokens should be the function body.
        let body = ASTNode::parse_closure(tokens)?;

        Ok(Function::new(sig, body))
    }

    // Parses function declarations.
    // Expects token sequences of the form "
    //      <fn_name>([<arg_type> <arg_name>, ...]) (<return_type>, ...) { ... }
    // where
    //      fn_name is an identifier representing the name of the function
    //      arg_type is the type of the argument
    //      arg_name is an identifier representing the argument name
    //      return_type is the type of the return value
    fn parse_function(tokens: &mut VecDeque<Token>) -> Result<Function, ParseError> {
        // The first set of tokens should be the function signature.
        let sig = ASTNode::parse_function_signature(tokens)?;

        // The remaining tokens should be the function body.
        let body = ASTNode::parse_closure(tokens)?;

        // Now that we have the function name and args, create the node.
        Ok(Function::new(sig, body))
    }

    // Parses arguments in function declarations.
    // Expects token sequences of the form
    //      ([<arg_type> <arg_name>, ...])
    // where
    //      arg_type is the type of the argument
    //      arg_name is an identifier representing the argument name
    fn parse_arguments(tokens: &mut VecDeque<Token>) -> Result<Vec<Argument>, ParseError> {
        // The first token should be the opening parenthesis.
        ASTNode::parse_expecting(tokens, vec![TokenKind::OpenParen])?;

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
                    let arg = ASTNode::parse_argument(tokens)?;
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
            let kind =
                ASTNode::parse_expecting(tokens, vec![TokenKind::Comma, TokenKind::CloseParen])?;
            match kind {
                TokenKind::Comma => {} // Nothing to do here. Just move onto the next arg.
                TokenKind::CloseParen => break, // We're done parsing args.
                _ => {
                    panic!("this should be impossible")
                }
            }
        }

        Ok(args)
    }

    // Returns an error if the next token is not any of the given kinds, or the kind otherwise.
    fn parse_expecting(
        tokens: &mut VecDeque<Token>,
        expected: Vec<TokenKind>,
    ) -> Result<TokenKind, ParseError> {
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

    // Parses a function argument.
    // Expects token sequences of the form
    //      <arg_type> <arg_name>
    // where
    //      arg_type is the type of the argument
    //      arg_name is an identifier representing the argument name
    fn parse_argument(tokens: &mut VecDeque<Token>) -> Result<Argument, ParseError> {
        // The first token should be the argument type.
        let arg_type = ASTNode::parse_type(tokens)?;

        // The second token should be the argument name.
        let name = ASTNode::parse_identifier(tokens)?;

        Ok(Argument::new(name.as_str(), arg_type))
    }

    // Parses type names.
    // Expects token sequences of the form
    //      <type>
    // where
    //      type is a valid type
    fn parse_type(tokens: &mut VecDeque<Token>) -> Result<Type, ParseError> {
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
                Ok(Type::Function(sig))
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

    // Parses identifiers.
    // Expects token sequences of the form
    //      <identifier>
    fn parse_identifier(tokens: &mut VecDeque<Token>) -> Result<String, ParseError> {
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
    use crate::parser::{ASTNode, Argument, Closure, Function, FunctionSignature, Type};

    #[test]
    fn parse_identifier() {
        let mut tokens = Token::tokenize_line("something", 0).expect("should not error");
        let result = ASTNode::parse_identifier(&mut tokens).expect("should not error");
        assert_eq!(result, "something");
    }

    #[test]
    fn parse_function() {
        let mut tokens =
            Token::tokenize_line("fn my_fn(string arg1, int arg2) (string, int) {}", 0)
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
                    vec![Type::String, Type::Int]
                ),
                Closure::new()
            )
        );

        let mut tokens = Token::tokenize_line(
            "fn bigboi(fn (string b1, int b2) () f, int i) (fn (int r) (string)) {}",
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
                            Type::Function(FunctionSignature::new_anon(
                                vec![
                                    Argument::new("b1", Type::String),
                                    Argument::new("b2", Type::Int)
                                ],
                                vec![]
                            ),),
                        ),
                        Argument::new("i", Type::Int)
                    ],
                    vec![Type::Function(FunctionSignature::new_anon(
                        vec![Argument::new("r", Type::Int)],
                        vec![Type::String]
                    ))],
                ),
                Closure::new()
            )
        );
    }
}
