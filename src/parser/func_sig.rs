use std::collections::HashSet;
use std::fmt;
use std::hash::{Hash, Hasher};

use colored::Colorize;

use crate::lexer::pos::{Locatable, Position};
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::parser::arg::Argument;
use crate::parser::error::{ErrorKind, ParseError, ParseResult};
use crate::parser::program::Program;
use crate::parser::stream::Stream;
use crate::parser::tmpl_params::TmplParams;
use crate::parser::Type;
use crate::{locatable_impl, util};

/// Represents the name, arguments, and return type of a function. Anonymous functions have empty
/// names.
#[derive(Debug, Clone, Eq)]
pub struct FunctionSignature {
    pub name: String,
    pub args: Vec<Argument>,
    pub return_type: Option<Type>,
    /// Function template parameters will be Some if this is a templated function (a function with
    /// generics).
    pub tmpl_params: Option<TmplParams>,
    start_pos: Position,
    end_pos: Position,
}

impl Hash for FunctionSignature {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.name.hash(state);

        for arg in &self.args {
            arg.hash(state);
        }

        if let Some(typ) = &self.return_type {
            typ.hash(state);
        }

        if let Some(tmpl_params) = &self.tmpl_params {
            tmpl_params.hash(state);
        }
    }
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
            write!(f, ") ~ {}", typ)
        } else {
            write!(f, ")")
        }
    }
}

impl PartialEq for FunctionSignature {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
            && util::vecs_eq(&self.args, &other.args)
            && self.return_type == other.return_type
            && util::opts_eq(&self.tmpl_params, &other.tmpl_params)
    }
}

locatable_impl!(FunctionSignature);

impl FunctionSignature {
    /// Creates a new function signature with default start and end positions.
    #[cfg(test)]
    pub fn new_with_default_pos(
        name: &str,
        args: Vec<Argument>,
        return_type: Option<Type>,
    ) -> Self {
        FunctionSignature {
            name: name.to_string(),
            tmpl_params: None,
            args,
            return_type,
            start_pos: Position::default(),
            end_pos: Position::default(),
        }
    }

    /// Creates a new function signature for a named function.
    pub fn new(
        name: &str,
        args: Vec<Argument>,
        return_type: Option<Type>,
        start_pos: Position,
        end_pos: Position,
    ) -> Self {
        FunctionSignature {
            name: name.to_string(),
            tmpl_params: None,
            args,
            return_type,
            start_pos,
            end_pos,
        }
    }

    /// Creates a new function signature for an anonymous function.
    pub fn new_anon(
        args: Vec<Argument>,
        return_type: Option<Type>,
        start_pos: Position,
        end_pos: Position,
    ) -> Self {
        FunctionSignature {
            name: "".to_string(),
            tmpl_params: None,
            args,
            return_type,
            start_pos,
            end_pos,
        }
    }

    /// Parses function signatures. Expects token sequences of the forms
    ///
    ///      fn <fn_name>(<arg_name>: <arg_type>, ...) ~ <return_type>
    ///      fn <fn_name>(<arg_name>: <arg_type>, ...)
    ///      fn <fn_name>(<arg_name>: <arg_type>, ...) ~ <return_type> with <tmpl_params>
    ///      fn <fn_name>(<arg_name>: <arg_type>, ...) with <tmpl_params>
    ///
    /// where
    ///  - `tmpl_params` are optional template parameters (see `TmplParams::from`)
    ///  - `fn_name` is an identifier representing the name of the function
    ///  - `arg_type` is the type of the argument
    ///  - `arg_name` is an identifier representing the argument name
    ///  - `return_type` is the type of the optional return type
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        // Record the function signature starting position.
        let start_pos = Program::parse_expecting(tokens, TokenKind::Fn)?.start;

        // Parse the rest of the function signature.
        let mut sig = FunctionSignature::from_name_args_and_return(tokens)?;

        // Parse the optional template parameters.
        let tmpl_params = match Program::parse_optional(tokens, TokenKind::With) {
            Some(_) => {
                tokens.rewind(1);
                Some(TmplParams::from(tokens)?)
            }
            None => None,
        };

        sig.start_pos = start_pos;
        sig.tmpl_params = tmpl_params;

        Ok(sig)
    }

    /// Parses the name, arguments, and return type of a function signature. Expects token
    /// sequences of the same forms as `from`, only without the leading `fn` token.
    pub fn from_name_args_and_return(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        let start_pos = Program::current_position(tokens);
        let fn_name = Program::parse_identifier(tokens)?;

        // The next tokens should represent function arguments and optional return type.
        let fn_sig = FunctionSignature::from_args_and_return(tokens, true)?;

        Ok(FunctionSignature::new(
            fn_name.as_str(),
            fn_sig.args,
            fn_sig.return_type,
            start_pos,
            fn_sig.end_pos,
        ))
    }

    /// Parses anonymous function signatures. If `named` is true, expects token sequences of the
    /// forms
    ///
    ///      fn (<arg_name>: <arg_type>, ...) ~ <return_type>
    ///      fn (<arg_name>: <arg_type>, ...)
    ///
    /// Otherwise, expects token sequences of the forms
    ///
    ///      fn (<arg_type>, ...) ~ <return_type>
    ///      fn (<arg_type>, ...)
    ///
    /// where
    ///  - `arg_type` is the type of the argument
    ///  - `arg_name` is an identifier representing the argument name
    ///  - `return_type` is the type of the optional return type
    pub fn from_anon(tokens: &mut Stream<Token>, named: bool) -> ParseResult<Self> {
        let start_pos = Program::current_position(tokens);

        // The first token should be `fn`.
        Program::parse_expecting(tokens, TokenKind::Fn)?;

        // The next tokens should represent function arguments followed by the return type.
        let mut fn_sig = FunctionSignature::from_args_and_return(tokens, named)?;
        fn_sig.start_pos = start_pos;
        Ok(fn_sig)
    }

    /// Parses function arguments and return value from a function signature. If `named` is true,
    /// expects token sequences of the forms
    ///
    ///     (<arg_name>: <arg_type>, ...) ~ <return_type>
    ///     (<arg_name>: <arg_type>, ...)
    ///
    /// Otherwise, expects token sequences of the form
    ///
    ///     (<arg_type>, ...)
    ///
    /// where
    ///  - `arg_type` is the type of the argument
    ///  - `arg_name` is an identifier representing the argument name
    ///  - `return_type` is the type of the optional return value
    fn from_args_and_return(tokens: &mut Stream<Token>, named: bool) -> ParseResult<Self> {
        // The next tokens should represent function arguments.
        let (args, args_end_pos) = FunctionSignature::arg_declarations_from(tokens, named)?;

        // The next token should be `~` if there is a return type. Otherwise, there is no return
        // type and we're done.
        let mut return_type = None;
        match tokens.peek_next() {
            Some(Token {
                kind: TokenKind::Tilde,
                ..
            }) => {
                // Remove the `~` and parse the return type.
                tokens.next();
                return_type = Some(Type::from(tokens)?);
            }
            _ => {}
        }

        Ok(FunctionSignature::new_anon(
            args,
            return_type,
            // We can leave the start position as default here because it will be set by the caller.
            Position::default(),
            args_end_pos,
        ))
    }

    /// Parses argument declarations in function declarations. If `named` is true, expects token
    /// sequences of the form
    ///
    ///      (<arg_name>: <arg_type>, ...)
    ///
    /// Otherwise, expects token sequences of the form
    ///
    ///      (<arg_type>, ...)
    ///
    /// where
    ///  - `arg_type` is the type of the argument
    ///  - `arg_name` is an identifier representing the argument name
    fn arg_declarations_from(
        tokens: &mut Stream<Token>,
        named: bool,
    ) -> ParseResult<(Vec<Argument>, Position)> {
        // Record the starting position of the arguments.
        let start_pos = Program::current_position(tokens);
        let end_pos: Position;

        // The first token should be the opening parenthesis.
        Program::parse_expecting(tokens, TokenKind::LeftParen)?;

        // The next token(s) should be arguments or a closing parenthesis.
        let mut args = vec![];
        loop {
            // The next token should be an argument, or `)`.
            let token = tokens.next();
            match token {
                Some(
                    token @ Token {
                        kind: TokenKind::RightParen,
                        ..
                    },
                ) => {
                    // We're done assembling arguments. Record the ending position of the arguments.
                    end_pos = token.end;
                    break;
                }

                Some(Token {
                    kind:
                        TokenKind::Fn
                        | TokenKind::Identifier(_)
                        | TokenKind::Struct
                        | TokenKind::Mut
                        | TokenKind::This,
                    ..
                }) => {
                    // The next few tokens represent an argument.
                    tokens.rewind(1);
                    let arg = if named {
                        Argument::from(tokens)?
                    } else {
                        Argument::unnamed_from(tokens)?
                    };

                    args.push(arg);
                }

                None => {
                    return Err(ParseError::new(
                        ErrorKind::UnexpectedEOF,
                        format_code!(
                            r#"expected argument or {}, but found EOF"#,
                            TokenKind::RightParen
                        )
                        .as_str(),
                        None,
                        // TODO: These positions are technically wrong.
                        start_pos,
                        start_pos.clone(),
                    ));
                }

                Some(other) => {
                    return Err(ParseError::new_with_token(
                        ErrorKind::ExpectedArgOrEndOfArgs,
                        format_code!(
                            r#"expected argument or {}, but found {}"#,
                            TokenKind::RightParen,
                            other
                        )
                        .as_str(),
                        other.clone(),
                    ))
                }
            };

            // After the argument, the next token should be `,` or `)`.
            let token = Program::parse_expecting_any(
                tokens,
                HashSet::from([TokenKind::Comma, TokenKind::RightParen]),
            )?;
            match token {
                Token {
                    kind: TokenKind::Comma,
                    ..
                } => {} // Nothing to do here. Just move onto the next arg.
                token @ Token {
                    kind: TokenKind::RightParen,
                    ..
                } => {
                    // We're done parsing args. Record the position of the `)`.
                    end_pos = token.end;
                    break;
                }
                _ => unreachable!(),
            }
        }

        Ok((args, end_pos))
    }
}

#[cfg(test)]
mod tests {
    use std::io::{BufRead, Cursor};

    use crate::lexer::token::Token;
    use crate::parser::program::Program;
    use crate::parser::stream::Stream;

    #[test]
    fn inline_struct_types_in_fn_sig() {
        let raw = r#"fn one(a: struct {one: i64, two: bool}, b: i64) ~ struct {thing: str} {}"#;
        let tokens = Token::tokenize(Cursor::new(raw).lines()).expect("should not error");
        let result = Program::from(&mut Stream::from(tokens));
        assert!(matches!(result, Ok(_)));
    }
}
