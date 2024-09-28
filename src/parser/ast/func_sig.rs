use std::fmt;
use std::hash::{Hash, Hasher};

use crate::lexer::pos::{Locatable, Position, Span};
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::parser::ast::arg::Argument;
use crate::parser::ast::params::Params;
use crate::parser::ast::r#type::Type;
use crate::parser::error::{ErrorKind, ParseError, ParseResult};
use crate::parser::module::Module;
use crate::{locatable_impl, util};

/// Represents the name, arguments, and return type of a function. Anonymous functions
/// have empty names.
#[derive(Debug, Clone, Eq)]
pub struct FunctionSignature {
    pub name: String,
    pub args: Vec<Argument>,
    pub maybe_ret_type: Option<Type>,
    pub params: Option<Params>,
    span: Span,
}

impl Hash for FunctionSignature {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.name.hash(state);

        for arg in &self.args {
            arg.hash(state);
        }

        if let Some(typ) = &self.maybe_ret_type {
            typ.hash(state);
        }

        if let Some(params) = &self.params {
            params.hash(state);
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

        if let Some(typ) = &self.maybe_ret_type {
            write!(f, ") -> {}", typ)
        } else {
            write!(f, ")")
        }
    }
}

impl PartialEq for FunctionSignature {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
            && util::vecs_eq(&self.args, &other.args)
            && self.maybe_ret_type == other.maybe_ret_type
            && util::opts_eq(&self.params, &other.params)
    }
}

locatable_impl!(FunctionSignature);

impl FunctionSignature {
    /// Creates a new function signature with default start and end positions.
    pub fn new_with_default_pos(
        name: &str,
        args: Vec<Argument>,
        return_type: Option<Type>,
    ) -> Self {
        FunctionSignature {
            name: name.to_string(),
            params: None,
            args,
            maybe_ret_type: return_type,
            span: Default::default(),
        }
    }

    /// Creates a new function signature for a named function.
    #[cfg(test)]
    pub fn new(name: &str, args: Vec<Argument>, return_type: Option<Type>, span: Span) -> Self {
        FunctionSignature {
            name: name.to_string(),
            params: None,
            args,
            maybe_ret_type: return_type,
            span,
        }
    }

    /// Creates a new parameterized function signature for a named function.
    pub fn new_parameterized(
        name: &str,
        args: Vec<Argument>,
        return_type: Option<Type>,
        params: Params,
        span: Span,
    ) -> Self {
        FunctionSignature {
            name: name.to_string(),
            params: Some(params),
            args,
            maybe_ret_type: return_type,
            span,
        }
    }

    /// Creates a new function signature for an anonymous function.
    pub fn new_anon(args: Vec<Argument>, return_type: Option<Type>, span: Span) -> Self {
        FunctionSignature {
            name: "".to_string(),
            params: None,
            args,
            maybe_ret_type: return_type,
            span,
        }
    }

    /// Parses function signatures. Expects token sequences of the forms
    ///
    ///      fn <fn_name><params>(<arg_name>: <arg_type>, ...) -> <return_type>
    ///      fn <fn_name><params>(<arg_name>: <arg_type>, ...)
    ///      fn <fn_name><params>(<arg_name>: <arg_type>, ...) -> <return_type>
    ///
    /// where
    ///  - `params` are optional generic parameters (see `Params::from`)
    ///  - `fn_name` is an identifier representing the name of the function
    ///  - `arg_type` is the type of the argument
    ///  - `arg_name` is an identifier representing the argument name
    ///  - `return_type` is the type of the optional return type
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        // Record the function signature starting position.
        let start_pos = Module::parse_expecting(tokens, TokenKind::Fn)?
            .span
            .start_pos;

        let fn_name = Module::parse_identifier(tokens)?;

        // Parse the optional generic parameters.
        let params = match Module::next_token_is(tokens, &TokenKind::LeftBracket) {
            true => Some(Params::from(tokens)?),
            false => None,
        };

        // The next tokens should represent function arguments and optional return type.
        let fn_sig = FunctionSignature::from_args_and_return(tokens, true)?;

        Ok(FunctionSignature {
            name: fn_name,
            args: fn_sig.args,
            maybe_ret_type: fn_sig.maybe_ret_type,
            params,
            span: Span {
                start_pos,
                end_pos: fn_sig.span.end_pos,
            },
        })
    }

    /// Parses anonymous function signatures. If `named` is true, expects token sequences of the
    /// forms
    ///
    ///      fn (<arg_name>: <arg_type>, ...) -> <return_type>
    ///      fn (<arg_name>: <arg_type>, ...)
    ///
    /// Otherwise, expects token sequences of the forms
    ///
    ///      fn (<arg_type>, ...) -> <return_type>
    ///      fn (<arg_type>, ...)
    ///
    /// where
    ///  - `arg_type` is the type of the argument
    ///  - `arg_name` is an identifier representing the argument name
    ///  - `return_type` is the type of the optional return type
    pub fn from_anon(tokens: &mut Stream<Token>, named: bool) -> ParseResult<Self> {
        let start_pos = Module::current_position(tokens);

        // The first token should be `fn`.
        Module::parse_expecting(tokens, TokenKind::Fn)?;

        // The next tokens should represent function arguments followed by the return type.
        let mut fn_sig = FunctionSignature::from_args_and_return(tokens, named)?;
        fn_sig.span.start_pos = start_pos;
        Ok(fn_sig)
    }

    /// Parses function arguments and return value from a function signature. If `named` is true,
    /// expects token sequences of the forms
    ///
    ///     (<arg_name>: <arg_type>, ...) -> <return_type>
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
        let (args, mut end_pos) = FunctionSignature::arg_declarations_from(tokens, named)?;

        // The next token should be `->` if there is a return type. Otherwise, there is no return
        // type and we're done.
        let mut maybe_ret_type = None;
        match tokens.peek_next() {
            Some(Token {
                kind: TokenKind::Arrow,
                ..
            }) => {
                // Remove the `->` and parse the return type.
                tokens.next();
                let return_type = Type::from(tokens)?;
                end_pos = return_type.end_pos().clone();
                maybe_ret_type = Some(return_type);
            }
            _ => {}
        }

        Ok(FunctionSignature::new_anon(
            args,
            maybe_ret_type,
            Span {
                // We can leave the start position as default here because it will
                // be set by the caller.
                start_pos: Position::default(),
                end_pos,
            },
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
        let start_pos = Module::current_position(tokens);
        let end_pos: Position;

        // The first token should be the opening parenthesis.
        Module::parse_expecting(tokens, TokenKind::LeftParen)?;

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
                    end_pos = token.span.end_pos;
                    break;
                }

                Some(_) => {
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
                        Span {
                            start_pos,
                            end_pos: start_pos,
                        },
                    ));
                }
            };

            // After the argument, the next token should be `,` or `)`.
            let token =
                Module::parse_expecting_any(tokens, vec![TokenKind::Comma, TokenKind::RightParen])?;
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
                    end_pos = token.span.end_pos;
                    break;
                }
                _ => unreachable!(),
            }
        }

        Ok((args, end_pos))
    }
}
