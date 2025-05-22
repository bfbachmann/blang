use std::fmt;

use crate::lexer::pos::{Position, Span};
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::ast::arg::Argument;
use crate::parser::ast::params::Params;
use crate::parser::ast::r#type::Type;
use crate::parser::ast::symbol::Name;
use crate::parser::error::{ErrorKind, ParseError, ParseResult};
use crate::parser::file_parser::FileParser;
use crate::Locatable;

/// Represents the name, arguments, and return type of a function. Anonymous functions
/// have empty names.
#[derive(Debug, Clone)]
pub struct FunctionSignature {
    pub name: Name,
    pub args: Vec<Argument>,
    pub maybe_ret_type: Option<Type>,
    pub params: Option<Params>,
    pub span: Span,
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
            && self.args == other.args
            && self.maybe_ret_type == other.maybe_ret_type
            && self.params == other.params
    }
}

locatable_impl!(FunctionSignature);

impl FunctionSignature {
    /// Creates a new function signature for a named function.
    #[cfg(test)]
    pub fn new(name: Name, args: Vec<Argument>, return_type: Option<Type>, span: Span) -> Self {
        FunctionSignature {
            name,
            params: None,
            args,
            maybe_ret_type: return_type,
            span,
        }
    }

    /// Creates a new function signature for an anonymous function.
    pub fn new_anon(args: Vec<Argument>, return_type: Option<Type>, span: Span) -> Self {
        FunctionSignature {
            name: Name {
                value: "".to_string(),
                span,
            },
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
    ///  - `params` are optional generic parameters
    ///  - `fn_name` is an identifier representing the name of the function
    ///  - `arg_type` is the type of the argument
    ///  - `arg_name` is an identifier representing the argument name
    ///  - `return_type` is the type of the optional return type
    pub fn from(parser: &mut FileParser) -> ParseResult<Self> {
        // Record the function signature starting position.
        let start_pos = parser.parse_expecting(TokenKind::Fn)?.span.start_pos;

        let fn_name = Name::parse(parser)?;

        // Parse the optional generic parameters.
        let params = match parser.next_token_is(&TokenKind::LeftBracket) {
            true => Some(Params::parse(parser)?),
            false => None,
        };

        // The next tokens should represent function arguments and optional return type.
        let fn_sig = FunctionSignature::parse_args_and_return(parser, true)?;

        Ok(FunctionSignature {
            name: fn_name,
            args: fn_sig.args,
            maybe_ret_type: fn_sig.maybe_ret_type,
            params,
            span: parser.new_span(start_pos, fn_sig.span.end_pos),
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
    pub fn parse_anon(parser: &mut FileParser, named: bool) -> ParseResult<Self> {
        let start_pos = parser.current_position();

        // The first token should be `fn`.
        parser.parse_expecting(TokenKind::Fn)?;

        // The next tokens should represent function arguments followed by the return type.
        let mut fn_sig = FunctionSignature::parse_args_and_return(parser, named)?;
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
    fn parse_args_and_return(parser: &mut FileParser, named: bool) -> ParseResult<Self> {
        // The next tokens should represent function arguments.
        let (args, mut end_pos) = FunctionSignature::parse_arg_declarations(parser, named)?;

        // The next token should be `->` if there is a return type. Otherwise, there is no return
        // type and we're done.
        let mut maybe_ret_type = None;
        if let Some(Token {
            kind: TokenKind::Arrow,
            ..
        }) = parser.tokens.peek_next()
        {
            // Remove the `->` and parse the return type.
            parser.tokens.next();
            let return_type = Type::parse(parser)?;
            end_pos = return_type.span().end_pos;
            maybe_ret_type = Some(return_type);
        }

        Ok(FunctionSignature::new_anon(
            args,
            maybe_ret_type,
            parser.new_span(
                // We can leave the start position as default here because it will
                // be set by the caller.
                Position::default(),
                end_pos,
            ),
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
    fn parse_arg_declarations(
        parser: &mut FileParser,
        named: bool,
    ) -> ParseResult<(Vec<Argument>, Position)> {
        // Record the starting position of the arguments.
        let start_pos = parser.current_position();
        let end_pos: Position;

        // The first token should be the opening parenthesis.
        parser.parse_expecting(TokenKind::LeftParen)?;

        // The next token(s) should be arguments or a closing parenthesis.
        let mut args = vec![];
        loop {
            // The next token should be an argument, or `)`.
            let token = parser.tokens.next();
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
                    parser.tokens.rewind(1);
                    let arg = if named {
                        Argument::parse(parser)?
                    } else {
                        Argument::parse_unnamed(parser)?
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
                        parser.new_span(start_pos, start_pos),
                    ));
                }
            };

            // After the argument, the next token should be `,` or `)`.
            let token = parser.parse_expecting_any(&[TokenKind::Comma, TokenKind::RightParen])?;
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
