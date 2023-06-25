use crate::lexer::{Token, TokenKind};
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
    Function(Function),
}

impl PartialEq for Type {
    fn eq(&self, other: &Self) -> bool {
        match (&self, other) {
            (Type::String, Type::String) | (Type::Int, Type::Int) => true,
            (
                Type::Function(Function {
                    name: name1,
                    args: args1,
                }),
                Type::Function(Function {
                    name: name2,
                    args: args2,
                }),
            ) => name1 == name2 && args1 == args2,
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
struct Function {
    name: String,
    args: Vec<Argument>,
}

impl PartialEq for Function {
    fn eq(&self, other: &Self) -> bool {
        if self.name != other.name {
            return false;
        }

        if self.args.len() != other.args.len() {
            return false;
        }

        for (a1, a2) in self.args.iter().zip(other.args.iter()) {
            if a1 != a2 {
                return false;
            }
        }

        true
    }
}

impl Function {
    fn new(name: &str, args: Vec<Argument>) -> Self {
        Function {
            name: name.to_string(),
            args,
        }
    }

    fn new_anon(args: Vec<Argument>) -> Self {
        Function {
            name: "".to_string(),
            args,
        }
    }
}

enum ASTNode {}

impl ASTNode {
    // Parses anonymous functions.
    // Expects token sequences of the form
    //      ([<arg_type> <arg_name>, ...])
    // where
    //      arg_type is the type of the argument
    //      arg_name is an identifier representing the argument name
    fn parse_anon_function(tokens: &mut VecDeque<Token>) -> Result<Function, ParseError> {
        // Just parse arguments since the function has no name.
        let args = ASTNode::parse_arguments(tokens)?;
        Ok(Function::new_anon(args))
    }

    // Parses function declarations.
    // Expects token sequences of the form "
    //      fn <fn_name>([<arg_type> <arg_name>, ...])
    // where
    //      fn_name is an identifier representing the name of the function
    //      arg_type is the type of the argument
    //      arg_name is an identifier representing the argument name
    fn parse_function(tokens: &mut VecDeque<Token>) -> Result<Function, ParseError> {
        // The first token should be an identifier that represents the function name.
        let fn_name = ASTNode::parse_identifier(tokens)?;

        // The next tokens should represent function arguments.
        let args = ASTNode::parse_arguments(tokens)?;

        // Now that we have the function name and args, create the node.
        Ok(Function::new(fn_name.as_str(), args))
    }

    // Parses arguments in function declarations.
    // Expects token sequences of the form
    //      ([<arg_type> <arg_name>, ...])
    // where
    //      arg_type is the type of the argument
    //      arg_name is an identifier representing the argument name
    fn parse_arguments(tokens: &mut VecDeque<Token>) -> Result<Vec<Argument>, ParseError> {
        // The first token should be the opening parenthesis.
        let token = tokens.pop_front();
        match token {
            Some(Token {
                kind: TokenKind::BeginArgs,
                start: _,
                end: _,
            }) => {}
            None => {
                return Err(ParseError::new(
                    r#"Expected "(" (beginning of function arguments)"#,
                    None,
                ))
            }
            Some(other) => {
                return Err(ParseError::new(
                    format!(
                        r#"Expected "(" (beginning of function arguments), but got "{}""#,
                        other,
                    )
                    .as_str(),
                    Some(other),
                ))
            }
        };

        // The next token(s) should be arguments or a closing parenthesis.
        let mut args = vec![];
        loop {
            // The next token should be an argument, or ")".
            let token = tokens.pop_front();
            match token {
                Some(Token {
                    kind: TokenKind::EndArgs,
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
            match tokens.pop_front() {
                Some(Token {
                    kind: TokenKind::Comma,
                    start: _,
                    end: _,
                }) => {
                    // Nothing to do here. Just move onto the next arg.
                }
                Some(Token {
                    kind: TokenKind::EndArgs,
                    start: _,
                    end: _,
                }) => {
                    // We're done parsing args.
                    break;
                }
                None => return Err(ParseError::new(r#"Expected "," or ")""#, None)),
                Some(other) => {
                    return Err(ParseError::new(
                        format!(r#"Expected "," or ")", but got "{}""#, other).as_str(),
                        Some(other),
                    ))
                }
            }
        }

        Ok(args)
    }

    // Parses a function argument.
    // Expects token sequences of the form
    //      <arg_type> <arg_name>
    // where
    //      arg_type is the type of the argument
    //      arg_name is an identifier representing the argument name
    fn parse_argument(tokens: &mut VecDeque<Token>) -> Result<Argument, ParseError> {
        // The first token should be the argument type.
        let arg_type = match tokens.pop_front() {
            Some(Token {
                kind: TokenKind::Int,
                start: _,
                end: _,
            }) => Type::Int,
            Some(Token {
                kind: TokenKind::String,
                start: _,
                end: _,
            }) => Type::String,
            Some(Token {
                kind: TokenKind::Function,
                start: _,
                end: _,
            }) => Type::Function(ASTNode::parse_anon_function(tokens)?),
            None => return Err(ParseError::new("Expected type (for argument)", None)),
            Some(other) => {
                return Err(ParseError::new(
                    format!(r#"Expected type (for argument), but got "{}""#, other).as_str(),
                    Some(other),
                ))
            }
        };

        // The second token should be the argument name.
        let name = ASTNode::parse_identifier(tokens)?;
        Ok(Argument::new(name.as_str(), arg_type))
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
    use crate::parser::{ASTNode, Argument, Function, Type};

    #[test]
    fn parse_identifier() {
        let mut tokens = Token::tokenize_line("something", 0).expect("should not error");
        let result = ASTNode::parse_identifier(&mut tokens).expect("should not error");
        assert_eq!(result, "something");
    }

    #[test]
    fn parse_function() {
        let mut tokens =
            Token::tokenize_line("my_fn(string arg1, int arg2)", 0).expect("should not error");
        let result = ASTNode::parse_function(&mut tokens).expect("should not error");
        assert_eq!(
            result,
            Function::new(
                "my_fn",
                vec![
                    Argument::new("arg1", Type::String),
                    Argument::new("arg2", Type::Int)
                ]
            )
        );

        let mut tokens = Token::tokenize_line("my_fn(fn (string b1, int b2) a1, int a2)", 0)
            .expect("should not error");
        let result = ASTNode::parse_function(&mut tokens).expect("should not error");
        assert_eq!(
            result,
            Function::new(
                "my_fn",
                vec![
                    Argument::new(
                        "a1",
                        Type::Function(Function::new_anon(vec![
                            Argument::new("b1", Type::String),
                            Argument::new("b2", Type::Int)
                        ]))
                    ),
                    Argument::new("a2", Type::Int)
                ]
            )
        );
    }

    #[test]
    fn parse_anon_function() {
        let mut tokens =
            Token::tokenize_line("(int the_int, string the_string)", 0).expect("should not error");
        let result = ASTNode::parse_anon_function(&mut tokens).expect("should not error");
        assert_eq!(
            result,
            Function::new_anon(vec![
                Argument::new("the_int", Type::Int),
                Argument::new("the_string", Type::String)
            ])
        );
    }
}
