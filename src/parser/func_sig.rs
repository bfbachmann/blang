use std::collections::{HashSet, VecDeque};
use std::fmt;

use crate::lexer::kind::TokenKind;
use crate::lexer::token::Token;
use crate::parser::arg::Argument;
use crate::parser::error::{ErrorKind, ParseError};
use crate::parser::program::Program;
use crate::parser::{ParseResult, Type};
use crate::util;

/// Represents the name, arguments, and return type of a function. Anonymous functions have empty
/// names.
#[derive(Debug, Clone)]
pub struct FunctionSignature {
    pub name: String,
    pub args: Vec<Argument>,
    pub return_type: Option<Type>,
}

impl fmt::Display for FunctionSignature {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "fn {}(", self.name)?;

        for arg in self.args.iter() {
            write!(f, "{}", arg)?;

            if arg != self.args.last().unwrap() {
                write!(f, ", ")?;
            }
        }

        if let Some(typ) = &self.return_type {
            write!(f, "): {}", typ)
        } else {
            write!(f, ")")
        }
    }
}

impl PartialEq for FunctionSignature {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
            && util::vectors_are_equal(&self.args, &other.args)
            && self.return_type == other.return_type
    }
}

impl FunctionSignature {
    pub fn new(name: &str, args: Vec<Argument>, return_type: Option<Type>) -> Self {
        FunctionSignature {
            name: name.to_string(),
            args,
            return_type,
        }
    }

    pub fn new_anon(args: Vec<Argument>, return_type: Option<Type>) -> Self {
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
    pub fn from(tokens: &mut VecDeque<Token>) -> ParseResult<Self> {
        // The first token should be "fn".
        Program::parse_expecting(tokens, HashSet::from([TokenKind::Function]))?;

        // The second token should be an identifier that represents the function name.
        let fn_name = Program::parse_identifier(tokens)?;

        // The next tokens should represent function arguments and optional return type.
        let fn_sig = FunctionSignature::from_args_and_return(tokens, true)?;

        Ok(FunctionSignature::new(
            fn_name.as_str(),
            fn_sig.args,
            fn_sig.return_type,
        ))
    }

    /// Parses anonymous function signatures. If `named` is true, expects token sequences of the
    /// forms
    ///
    ///      fn (<arg_type> <arg_name>, ...): <return_type>
    ///      fn (<arg_type> <arg_name>, ...)
    ///
    /// Otherwise, expects token sequences of the forms
    ///
    ///      fn (<arg_type>, ...): <return_type>
    ///      fn (<arg_type>, ...)
    ///
    /// where
    ///  - `arg_type` is the type of the argument
    ///  - `arg_name` is an identifier representing the argument name
    ///  - `return_type` is the type of the optional return type
    pub fn from_anon(tokens: &mut VecDeque<Token>, named: bool) -> ParseResult<Self> {
        // The first token should be "fn".
        Program::parse_expecting(tokens, HashSet::from([TokenKind::Function]))?;

        // The next tokens should represent function arguments followed by the return type.
        let fn_sig = FunctionSignature::from_args_and_return(tokens, named)?;
        Ok(fn_sig)
    }

    /// Parses function arguments and return value from a function signature. If `named` is true,
    /// expects token sequences of the forms
    ///
    ///     (<arg_type> <arg_name>, ...): <return_type>
    ///     (<arg_type> <arg_name>, ...)
    ///
    /// Otherwise, expects token sequences of the form
    ///
    ///     (<arg_type>, ...)
    ///
    /// where
    ///  - `arg_type` is the type of the argument
    ///  - `arg_name` is an identifier representing the argument name
    ///  - `return_type` is the type of the optional return value
    fn from_args_and_return(tokens: &mut VecDeque<Token>, named: bool) -> ParseResult<Self> {
        // The next tokens should represent function arguments.
        let args = FunctionSignature::arg_declarations_from(tokens, named)?;

        // The next token should be ":" if there is a return type. Otherwise, there is no return
        // type and we're done.
        let mut return_type = None;
        match tokens.front() {
            Some(Token {
                kind: TokenKind::Colon,
                ..
            }) => {
                // Remove the ":" and parse the return type.
                tokens.pop_front();
                return_type = Some(Type::from(tokens)?);
            }
            _ => {}
        }

        Ok(FunctionSignature::new_anon(args, return_type))
    }

    /// Parses argument declarations in function declarations. If `named` is true, expects token
    /// sequences of the form
    ///
    ///      (<arg_type> <arg_name>, ...)
    ///
    /// Otherwise, expects token sequences of the form
    ///
    ///      (<arg_type>, ...)
    ///
    /// where
    ///  - `arg_type` is the type of the argument
    ///  - `arg_name` is an identifier representing the argument name
    fn arg_declarations_from(
        tokens: &mut VecDeque<Token>,
        named: bool,
    ) -> ParseResult<Vec<Argument>> {
        // The first token should be the opening parenthesis.
        Program::parse_expecting(tokens, HashSet::from([TokenKind::LeftParen]))?;

        // The next token(s) should be arguments or a closing parenthesis.
        let mut args = vec![];
        let mut arg_names = HashSet::new();
        loop {
            // The next token should be an argument, or ")".
            let token = tokens.pop_front();
            match token {
                Some(Token {
                    kind: TokenKind::RightParen,
                    ..
                }) => {
                    // We're done assembling arguments.
                    break;
                }

                Some(Token {
                    kind:
                        TokenKind::String
                        | TokenKind::I64
                        | TokenKind::Bool
                        | TokenKind::Function
                        | TokenKind::Identifier(_),
                    ..
                }) => {
                    // The next few tokens represent an argument.
                    tokens.push_front(token.clone().unwrap());
                    let arg = if named {
                        let arg = Argument::from(tokens)?;

                        // Make sure the arg name isn't already used.
                        if !arg_names.insert(arg.name.clone()) {
                            return Err(ParseError::new(
                                ErrorKind::DuplicateArgName,
                                format!("duplicate argument name {}", arg.name).as_str(),
                                token,
                            ));
                        }

                        arg
                    } else {
                        Argument::unnamed_from(tokens)?
                    };

                    args.push(arg);
                }

                None => {
                    return Err(ParseError::new(
                        ErrorKind::ExpectedArgOrEndOfArgs,
                        r#"expected argument or ")""#,
                        None,
                    ))
                }

                Some(other) => {
                    return Err(ParseError::new(
                        ErrorKind::ExpectedArgOrEndOfArgs,
                        format!(r#"expected argument or ")", but found "{}""#, other).as_str(),
                        Some(other),
                    ))
                }
            };

            // After the argument, the next token should be "," or ")".
            let kind = Program::parse_expecting(
                tokens,
                HashSet::from([TokenKind::Comma, TokenKind::RightParen]),
            )?;
            match kind {
                TokenKind::Comma => {} // Nothing to do here. Just move onto the next arg.
                TokenKind::RightParen => break, // We're done parsing args.
                _ => panic!("this should be impossible"),
            }
        }

        Ok(args)
    }
}

#[cfg(test)]
mod tests {
    use std::io::{BufRead, Cursor};

    use crate::lexer::token::Token;
    use crate::parser::error::ErrorKind;
    use crate::parser::error::ParseError;
    use crate::parser::program::Program;

    #[test]
    fn duplicate_arg_name() {
        let raw = r#"fn one(i64 a, i64 b, i64 a) {}"#;
        let mut tokens = Token::tokenize(Cursor::new(raw).lines()).expect("should not error");
        let result = Program::from(&mut tokens);
        assert!(matches!(
            result,
            Err(ParseError {
                kind: ErrorKind::DuplicateArgName,
                ..
            })
        ));
    }
}
