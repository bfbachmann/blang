use std::hash::{Hash, Hasher};

use crate::lexer::pos::Span;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::ast::func_sig::FunctionSignature;
use crate::parser::ast::params::Params;
use crate::parser::ast::symbol::Name;
use crate::parser::error::ParseResult;
use crate::parser::file_parser::FileParser;
use crate::Locatable;

/// Represents a spec declaration.
#[derive(Debug, Eq, Clone)]
pub struct SpecType {
    pub name: Name,
    pub fn_sigs: Vec<FunctionSignature>,
    pub maybe_params: Option<Params>,
    pub is_pub: bool,
    pub span: Span,
}

impl Hash for SpecType {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.name.hash(state);
        self.fn_sigs.hash(state);
        self.maybe_params.hash(state);
    }
}

impl PartialEq for SpecType {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
            && self.fn_sigs == other.fn_sigs
            && self.maybe_params == other.maybe_params
    }
}

locatable_impl!(SpecType);

impl SpecType {
    /// Parses a spec declaration. Expects token sequences of the form
    ///
    ///     pub spec <name><params> {
    ///         <fn_sig>...
    ///     }
    ///
    /// where
    ///  - `name` is an identifier representing the name of the spec
    ///  - `params` are generic parameters (optional)
    ///  - `fn_sig` is a function signature in the spec
    ///  - the `pub` keyword is optional.
    pub fn parse(parser: &mut FileParser) -> ParseResult<Self> {
        let is_pub = parser.parse_optional(TokenKind::Pub).is_some();

        // Parse `spec` and get this spec declaration starting position.
        let start_pos = parser.parse_expecting(TokenKind::Spec)?.span.start_pos;

        // Parse the spec name and left brace.
        let name = Name::parse(parser)?;

        // Parse optional generic parameters.
        let maybe_params = match parser.next_token_is(&TokenKind::LeftBracket) {
            true => Some(Params::parse(parser)?),
            false => None,
        };

        parser.parse_expecting(TokenKind::LeftBrace)?;

        // Parse all the function signatures in the spec, followed by the closing brace.
        let mut fn_sigs = vec![];
        let end_pos = loop {
            if let Some(token) = parser.parse_optional(TokenKind::RightBrace) {
                break token.span.end_pos;
            }

            fn_sigs.push(FunctionSignature::from(parser)?);
        };

        Ok(SpecType {
            name,
            fn_sigs,
            maybe_params,
            is_pub,
            span: parser.new_span(start_pos, end_pos),
        })
    }
}
