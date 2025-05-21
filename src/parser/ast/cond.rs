use std::fmt;
use std::fmt::Formatter;

use crate::lexer::pos::Span;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::ast::branch::Branch;
use crate::parser::error::ParseResult;
use crate::parser::file_parser::FileParser;
use crate::Locatable;

/// Represents a conditional (i.e. branching if/else if/else statements).
#[derive(Debug, Clone)]
pub struct Conditional {
    pub branches: Vec<Branch>,
    pub span: Span,
}

impl fmt::Display for Conditional {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "if ...",)
    }
}

impl PartialEq for Conditional {
    fn eq(&self, other: &Self) -> bool {
        self.branches == other.branches && self.span == other.span
    }
}

locatable_impl!(Conditional);

impl Conditional {
    /// Creates a new conditional.
    pub fn new(branches: Vec<Branch>) -> Self {
        let start_span = branches.first().unwrap().condition.as_ref().unwrap().span();
        let end_pos = branches.last().unwrap().body.span().end_pos;
        Conditional {
            span: Span {
                file_id: start_span.file_id,
                start_pos: start_span.start_pos,
                end_pos,
            },
            branches,
        }
    }

    /// Parses conditionals. Expects token sequences of the forms
    ///
    ///     if <if_cond> <body>
    ///     else if <else_if_cond> <body>
    ///     else <body>
    ///
    /// where
    ///  - the `else if` and `else` branches are optional, and the `else if` branch is repeatable
    ///  - `if_cond` is an expression that represents the `if` branch condition
    ///  - `else_if_cond` is an expression that represents the `else if` branch condition
    ///  - `body` is a statement that represents the branch body.
    pub fn parse(parser: &mut FileParser) -> ParseResult<Self> {
        // The first token should be `if`.
        parser.parse_expecting(TokenKind::If)?;

        // Parse the rest of the branch (the expression and the closure).
        let branch = Branch::from(parser, true)?;

        // We now have the first `if` branch. Continue by adding other `else if` branches until
        // there are none left.
        let mut branches = vec![branch];
        while let Some(&Token {
            kind: TokenKind::Else,
            ..
        }) = parser.tokens.peek_next()
        {
            // Move past the `else` token.
            parser.tokens.next();

            match parser.tokens.peek_next() {
                // `else if` branch
                Some(Token {
                    kind: TokenKind::If,
                    ..
                }) => {
                    // Move past the `if` token.
                    parser.tokens.next();
                    let branch = Branch::from(parser, true)?;
                    branches.push(branch);
                }

                // `else` branch.
                _ => {
                    // Parse the rest of the branch and add it to the list of branches, then break
                    // because we're reached the end of the conditional.
                    let branch = Branch::from(parser, false)?;
                    branches.push(branch);
                    break;
                }
            }
        }

        Ok(Conditional::new(branches))
    }
}
