use std::fmt::{Display, Formatter};

use crate::lexer::pos::Span;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::ast::func_sig::FunctionSignature;
use crate::parser::error::ParseResult;
use crate::parser::file_parser::FileParser;
use crate::Locatable;

/// Represents a set of external function declarations.
#[derive(Clone, Debug)]
pub struct ExternFn {
    pub signature: FunctionSignature,
    pub maybe_link_name: Option<String>,
    pub is_pub: bool,
    pub span: Span,
}

impl PartialEq for ExternFn {
    fn eq(&self, other: &Self) -> bool {
        self.signature == other.signature
    }
}

impl Display for ExternFn {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "extern {}", self.signature)
    }
}

locatable_impl!(ExternFn);

impl ExternFn {
    /// Attempts to parse an external function declaration from the token sequence.
    /// Expects token sequences of one of the following forms:
    ///
    ///     pub extern <fn_sig>
    ///     pub extern "name" <fn_sig>
    ///
    /// where
    ///  - `fn_sig` is a function signature
    ///  - `name` is the optional name to link against in codegen
    ///  - `pub` is optional.
    pub fn parse(parser: &mut FileParser) -> ParseResult<Self> {
        let is_pub = parser.parse_optional(TokenKind::Pub).is_some();
        let start_pos = parser.current_position();

        // Parse the `extern` token.
        parser.parse_expecting(TokenKind::Extern)?;

        // Parse the optional extern name.
        let maybe_link_name = match parser.tokens.peek_next() {
            Some(Token {
                kind: TokenKind::StrLiteral(name),
                ..
            }) => {
                let result = Some(name.clone());
                parser.tokens.next();
                result
            }
            _ => None,
        };

        // Parse the function signature.
        let fn_sig = FunctionSignature::parse(parser)?;
        let end_pos = fn_sig.span().end_pos;

        Ok(ExternFn {
            signature: fn_sig,
            maybe_link_name,
            is_pub,
            span: parser.new_span(start_pos, end_pos),
        })
    }
}
