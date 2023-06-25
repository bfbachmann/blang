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

enum Value {
    String(String),
    Int(i64),
    Function, // TODO
}

#[derive(Debug)]
struct Argument {
    name: String,
    kind: TokenKind,
}

impl PartialEq for Argument {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name && self.kind == other.kind
    }
}

impl Argument {
    fn new(name: &str, kind: TokenKind) -> Self {
        Argument {
            name: name.to_string(),
            kind,
        }
    }
}

struct Statement {}

struct Expression {}

struct Conditional {}

struct Loop {}

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

    fn new_no_args(name: &str) -> Self {
        Function {
            name: name.to_string(),
            args: vec![],
        }
    }

    fn new_anon(args: Vec<Argument>) -> Self {
        Function {
            name: "".to_string(),
            args,
        }
    }
}

enum ASTNode {
    Statement,
    Expression,
    Conditional,
    Loop,
    Function,
}

impl ASTNode {
    // Parses anonymous functions.
    // Expects token sequences of the form "(<arg_type> <arg_name>, ...)".
    fn parse_anon_function(tokens: &mut VecDeque<Token>) -> Result<Function, ParseError> {
        // Just parse arguments since the function has no name.
        let args = ASTNode::parse_arguments(tokens)?;
        Ok(Function::new_anon(args))
    }

    // Parses function declarations.
    // Expects token sequences of the form "fn <fn_name>(<arg_type> <arg_name>, ...)".
    fn parse_function(tokens: &mut VecDeque<Token>) -> Result<Function, ParseError> {
        // The first token should be an identifier that represents the function name.
        let fn_name = ASTNode::parse_identifier(tokens)?;

        // The next tokens should represent function arguments.
        let args = ASTNode::parse_arguments(tokens)?;

        // Now that we have the function name and args, create the node.
        Ok(Function::new(fn_name.as_str(), args))
    }

    // Parses arguments in function declarations.
    // Expects token sequences of the form "(<arg_type> <arg_name>, ...)".
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
    // Expects token sequences of the form "<arg_type> <arg_name>".
    fn parse_argument(tokens: &mut VecDeque<Token>) -> Result<Argument, ParseError> {
        // The first token should be the argument type.
        let kind = match tokens.pop_front() {
            Some(Token {
                kind: k @ (TokenKind::Int | TokenKind::String),
                start: _,
                end: _,
            }) => k,
            Some(Token {
                kind: TokenKind::Function,
                start: _,
                end: _,
            }) => {
                // TODO
                return Err(ParseError::new("Unimplemented", None));
            }
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
        Ok(Argument::new(name.as_str(), kind))
    }

    // Parses identifiers.
    // Expects token sequences of the form "<identifier>".
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
    use crate::lexer::{Token, TokenKind};
    use crate::parser::{ASTNode, Argument, Function};

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
                    Argument::new("arg1", TokenKind::String),
                    Argument::new("arg2", TokenKind::Int)
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
                Argument::new("the_int", TokenKind::Int),
                Argument::new("the_string", TokenKind::String)
            ])
        );
    }
}
