use crate::lexer::pos::Span;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::ast::symbol::Symbol;
use crate::parser::error::ParseResult;
use crate::parser::file_parser::FileParser;
use crate::Locatable;

/// Represents a generic compile-time parameter. A parameter has a name and has
/// a set of associated specs that any type used in its place must implement.
#[derive(Debug, PartialEq, Clone)]
pub struct Param {
    /// The name given to the parameter.
    pub name: String,
    /// The specs that this parameter requires.
    pub required_specs: Vec<Symbol>,
    pub span: Span,
}

impl Param {
    /// Parses a parameter. Expects token sequences of the forms
    ///
    ///     <name>: <spec> + ...
    ///
    /// where
    ///  - `name` is an identifier representing the parameter name
    ///  - `spec` is any spec that a type satisfying the requirements must implement. Note that the
    ///    specs are being parsed as types, because specs and types are represented the same way.
    ///    The set of specs may be empty.
    ///
    /// In the first example, one or more specs are provided. Only types that implement all of these
    /// specs can satisfy the parameter's requirements.
    pub fn parse(parser: &mut FileParser) -> ParseResult<Self> {
        // Find the start position and (maybe) the end position of this param.
        let span = match parser.tokens.peek_next() {
            Some(token) => token.span,
            None => Default::default(),
        };

        // Parse the param name.
        let mut param = Param {
            name: parser.parse_identifier()?,
            required_specs: vec![],
            span,
        };

        // Parse the optional `: <spec> + ...`.
        if parser.parse_optional(TokenKind::Colon).is_some() {
            loop {
                let spec = Symbol::parse(parser)?;
                param.required_specs.push(spec);

                // Stop parsing specs if the next token is not a `+`.
                if parser.parse_optional(TokenKind::Plus).is_none() {
                    param.span.end_pos = param.required_specs.last().unwrap().span.end_pos;
                    break;
                }
            }
        }

        Ok(param)
    }
}

locatable_impl!(Param);

/// Represents generic parameters. A set of generic parameters is just a set of
/// types.
#[derive(Debug, Clone, PartialEq)]
pub struct Params {
    pub params: Vec<Param>,
    pub span: Span,
}

locatable_impl!(Params);

impl Params {
    /// Parses a set of parameters. Expects token sequences of the forms
    ///
    ///     [<param>,...]
    ///
    /// where
    ///  - `param` is a generic parameter.
    pub fn parse(parser: &mut FileParser) -> ParseResult<Self> {
        // Parse `[`.
        let start_pos = parser
            .parse_expecting(TokenKind::LeftBracket)?
            .span
            .start_pos;

        // Parse all params and the closing bracket.
        let mut params = vec![];
        let end_pos = loop {
            // Parse the param (there must be at least one).
            params.push(Param::parse(parser)?);

            // The next token should either be a comma or the closing bracket.
            match parser.parse_expecting_any(vec![TokenKind::Comma, TokenKind::RightBracket])? {
                Token {
                    kind: TokenKind::RightBracket,
                    span,
                    ..
                } => {
                    break span.end_pos;
                }

                _ => {
                    // Allow trailing commas.
                    if let Some(token) = parser.parse_optional(TokenKind::RightBracket) {
                        break token.span.end_pos;
                    }
                }
            };
        };

        Ok(Params {
            params,
            span: parser.new_span(start_pos, end_pos),
        })
    }
}
