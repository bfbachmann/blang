use std::hash::{Hash, Hasher};

use crate::lexer::pos::{Locatable, Position};
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::parser::ast::func::Function;
use crate::parser::ast::r#type::Type;
use crate::parser::error::ParseResult;
use crate::parser::module::Module;
use crate::{locatable_impl, util};

/// Represents the implementation of a series of member functions on a type.
#[derive(Debug, Eq)]
pub struct Impl {
    pub typ: Type,
    pub member_fns: Vec<Function>,
    start_pos: Position,
    end_pos: Position,
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

impl Clone for Impl {
    fn clone(&self) -> Self {
        Impl {
            typ: self.typ.clone(),
            member_fns: self.member_fns.iter().map(|s| s.clone()).collect(),
            start_pos: self.start_pos.clone(),
            end_pos: self.end_pos.clone(),
        }
    }
}

locatable_impl!(Impl);

impl Impl {
    /// Parses an implementation (a set of member functions) for a type. Expects token sequences
    /// of the form
    ///
    ///     impl <type> {
    ///         <member_fn>...
    ///     }
    ///
    /// where
    ///  - `type` is the type for which member functions are being implemented
    ///  - `member_fn` is one of a series of member functions in the implementation.
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        let start_pos = Module::current_position(tokens);
        let end_pos;

        // The first token should be `impl`.
        Module::parse_expecting(tokens, TokenKind::Impl)?;

        // The next tokens should form a type.
        let typ = Type::from(tokens)?;

        // The remaining tokens should be `{` followed by a set of function signatures and a `}`.
        Module::parse_expecting(tokens, TokenKind::LeftBrace)?;

        let mut member_fns = vec![];
        loop {
            if let Some(token) = Module::parse_optional(tokens, TokenKind::RightBrace) {
                end_pos = token.end;
                break;
            }

            member_fns.push(Function::from(tokens)?);
        }

        Ok(Impl {
            typ,
            member_fns,
            start_pos,
            end_pos,
        })
    }
}
