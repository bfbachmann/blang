use std::hash::{Hash, Hasher};

use crate::lexer::pos::{Locatable, Position, Span};
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::parser::ast::func::Function;
use crate::parser::ast::symbol::Symbol;
use crate::parser::ast::unresolved::UnresolvedType;
use crate::parser::error::ParseResult;
use crate::parser::module::Module;
use crate::{locatable_impl, util};

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
        util::vecs_eq(&self.member_fns, &other.member_fns)
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
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        let start_pos = Module::current_position(tokens);
        let end_pos;

        // The first token should be `impl`.
        Module::parse_expecting(tokens, TokenKind::Impl)?;

        // The next tokens should form a type.
        let typ = UnresolvedType::from_symbol(Symbol::from(tokens)?);

        // Check for an optional spec.
        let maybe_spec = match Module::parse_optional(tokens, TokenKind::Colon) {
            Some(_) => Some(Symbol::from(tokens)?),
            None => None,
        };

        // The remaining tokens should be `{` followed by a set of function signatures and a `}`.
        Module::parse_expecting(tokens, TokenKind::LeftBrace)?;

        let mut member_fns = vec![];
        loop {
            if let Some(token) = Module::parse_optional(tokens, TokenKind::RightBrace) {
                end_pos = token.span.end_pos;
                break;
            }

            member_fns.push(Function::from(tokens)?);
        }

        Ok(Impl {
            typ,
            maybe_spec,
            member_fns,
            span: Span { start_pos, end_pos },
        })
    }
}
