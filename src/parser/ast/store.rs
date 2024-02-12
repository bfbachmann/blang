use std::hash::{Hash, Hasher};

use crate::lexer::pos::{Locatable, Position};
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::ast::expr::Expression;
use crate::parser::error::ParseResult;
use crate::parser::source::Source;

/// A store statement that writes a value to memory.
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct Store {
    pub dest_expr: Expression,
    pub source_expr: Expression,
    start_pos: Position,
    end_pos: Position,
}

impl Hash for Store {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.dest_expr.hash(state);
        self.source_expr.hash(state);
    }
}

locatable_impl!(Store);

impl Store {
    /// Parses a store statement (writing a value to memory addressed by a pointer). Expects token
    /// sequences of the form
    ///
    ///     `<dest_expr> <- <source_expr>`
    ///
    /// where
    /// - `dest_expr` is an expression representing the pointer addressing the memory that will
    ///   be written to (see `Expression::from`)
    /// - `source_expr` is an expression representing the value being written to memory.
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Store> {
        let dest_expr = Expression::from(tokens)?;
        let start_pos = dest_expr.start_pos().clone();
        Source::parse_expecting(tokens, TokenKind::Store)?;
        let source_expr = Expression::from(tokens)?;
        let end_pos = source_expr.end_pos().clone();

        Ok(Store {
            dest_expr,
            source_expr,
            start_pos,
            end_pos,
        })
    }
}
