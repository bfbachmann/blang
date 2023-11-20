use crate::lexer::pos::{Locatable, Position};
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::error::ParseResult;
use crate::parser::expr::Expression;
use crate::parser::program::Program;

/// A store statement that writes a value to memory.
#[derive(PartialEq, Clone, Debug)]
pub struct Store {
    pub dest_expr: Expression,
    pub source_expr: Expression,
    start_pos: Position,
    end_pos: Position,
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
        let dest_expr = Expression::from(tokens, false)?;
        let start_pos = dest_expr.start_pos().clone();
        Program::parse_expecting(tokens, TokenKind::Store)?;
        let source_expr = Expression::from(tokens, false)?;
        let end_pos = source_expr.end_pos().clone();

        Ok(Store {
            dest_expr,
            source_expr,
            start_pos,
            end_pos,
        })
    }
}
