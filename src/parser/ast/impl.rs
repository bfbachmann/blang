use std::hash::{Hash, Hasher};

use crate::lexer::pos::Span;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::ast::func::Function;
use crate::parser::ast::symbol::Symbol;
use crate::parser::ast::unresolved::UnresolvedType;
use crate::parser::error::ParseResult;
use crate::parser::file_parser::FileParser;
use crate::Locatable;

/// Represents the implementation of a series of member functions on a type.
#[derive(Clone, Debug, Eq)]
pub struct Impl {
    pub typ: UnresolvedType,
    /// The spec being implemented for the type.
    pub maybe_spec: Option<Symbol>,
    pub member_fns: Vec<Function>,
    pub span: Span,
}

impl PartialEq for Impl {
    fn eq(&self, other: &Self) -> bool {
        self.member_fns == other.member_fns
    }
}

impl Hash for Impl {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.typ.hash(state);
        self.member_fns.hash(state);
    }
}

locatable_impl!(Impl);

impl Impl {
    /// Parses an implementation (a set of member functions) for a type. Expects token sequences
    /// of the forms
    ///
    ///     impl <type> {
    ///         <member_fn>...
    ///     }
    ///
    ///     impl <type>: <spec> {
    ///         <member_fn>...
    ///     }
    ///
    /// where
    ///  - `type` is the name of the type for which member functions are being implemented
    ///  - `member_fn` is one of a series of member functions in the implementation
    ///  - `spec` is the optional symbol representing a spec this `impl` implements.
    pub fn parse(parser: &mut FileParser) -> ParseResult<Self> {
        let start_pos = parser.current_position();
        let end_pos;

        // The first token should be `impl`.
        parser.parse_expecting(TokenKind::Impl)?;

        // The next tokens should form a type.
        let typ = UnresolvedType::from_symbol(Symbol::parse(parser)?);

        // Check for an optional spec.
        let maybe_spec = match parser.parse_optional(TokenKind::Colon) {
            Some(_) => Some(Symbol::parse(parser)?),
            None => None,
        };

        // The remaining tokens should be `{` followed by a set of function signatures and a `}`.
        parser.parse_expecting(TokenKind::LeftBrace)?;

        let mut member_fns = vec![];
        loop {
            if let Some(token) = parser.parse_optional(TokenKind::RightBrace) {
                end_pos = token.span.end_pos;
                break;
            }

            member_fns.push(Function::parse(parser)?);
        }

        Ok(Impl {
            typ,
            maybe_spec,
            member_fns,
            span: parser.new_span(start_pos, end_pos),
        })
    }

    /// Returns the span on the impl header.
    pub fn header_span(&self) -> Span {
        Span {
            file_id: self.span.file_id,
            start_pos: self.span.start_pos,
            end_pos: match &self.maybe_spec {
                Some(spec) => spec.span.end_pos,
                None => self.typ.span.end_pos,
            },
        }
    }
}
