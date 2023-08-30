use std::collections::{HashSet, VecDeque};
use std::fmt::{Display, Formatter};

use crate::lexer::kind::TokenKind;
use crate::lexer::pos::{Locatable, Position};
use crate::lexer::token::Token;
use crate::parser::error::ParseResult;
use crate::parser::program::Program;

/// Represents access to a member or field on a type or an instance of a type.
#[derive(Debug, Clone)]
pub struct MemberAccess {
    /// The name of the object member being accessed.
    pub member_name: String,
    /// Any sub-member accesses are chained here.
    pub submember: Option<Box<MemberAccess>>,
    start_pos: Position,
    end_pos: Position,
}

impl Locatable for MemberAccess {
    fn start_pos(&self) -> &Position {
        &self.start_pos
    }

    fn end_pos(&self) -> &Position {
        &self.end_pos
    }
}

impl PartialEq for MemberAccess {
    fn eq(&self, other: &Self) -> bool {
        if self.member_name != other.member_name {
            return false;
        }

        match (&self.submember, &other.submember) {
            (Some(a), Some(b)) => *a == *b,
            (None, None) => true,
            _ => false,
        }
    }
}

impl Display for MemberAccess {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.member_name)?;

        if let Some(member) = &self.submember {
            write!(f, ".{}", *member)?;
        }

        Ok(())
    }
}

impl MemberAccess {
    /// Attempts to parse an object member access from the token token sequence. Expects token
    /// sequences of the form:
    ///
    ///         .<member>...
    ///
    /// where
    ///  - `member` is the name of the member being accessed.
    /// Member accesses can be chained (e.g. `my_struct.child.child.child`).
    pub fn from(tokens: &mut VecDeque<Token>) -> ParseResult<Self> {
        let start_pos = Program::current_position(tokens);

        // The first token should be ".".
        Program::parse_expecting(tokens, HashSet::from([TokenKind::Dot]))?;

        // Get the end position of the next token (the member name).
        let mut end_pos = match tokens.front() {
            Some(&Token { end, .. }) => end.clone(),
            // If this happens, we'll error on the next line while parsing the identifier anyway.
            _ => Position::default(),
        };

        // The second token should be the member name.
        let member_name = Program::parse_identifier(tokens)?;

        // Recursively parse the sub-members, if necessary.
        let mut submember = None;
        match tokens.front() {
            Some(&Token {
                kind: TokenKind::Dot,
                end,
                ..
            }) => {
                submember = Some(Box::new(MemberAccess::from(tokens)?));
                end_pos = end.clone();
            }
            _ => {}
        }

        Ok(MemberAccess {
            member_name,
            submember,
            start_pos,
            end_pos,
        })
    }
}
