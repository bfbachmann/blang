use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};

use crate::lexer::pos::{Position, Span};
use crate::lexer::token_kind::TokenKind;
use crate::parser::ast::expr::Expression;
use crate::parser::ast::params::Params;
use crate::parser::ast::r#type::Type;
use crate::parser::ast::symbol::{Name, Symbol};
use crate::parser::ast::unresolved::UnresolvedType;
use crate::parser::error::ParseResult;
use crate::parser::file_parser::FileParser;
use crate::Locatable;
use crate::{locatable_impl, util};

/// A variant of an enumerated type.
#[derive(Clone, Debug, Eq)]
pub struct EnumTypeVariant {
    pub name: String,
    pub maybe_type: Option<Type>,
    pub span: Span,
}

impl PartialEq for EnumTypeVariant {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name && util::opts_eq(&self.maybe_type, &other.maybe_type)
    }
}

impl Hash for EnumTypeVariant {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.name.hash(state);

        if let Some(typ) = &self.maybe_type {
            typ.hash(state);
        }
    }
}

impl Display for EnumTypeVariant {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)?;

        if let Some(typ) = &self.maybe_type {
            write!(f, "({})", typ)?;
        }

        Ok(())
    }
}

locatable_impl!(EnumTypeVariant);

impl EnumTypeVariant {
    /// Parses an enum type variant declaration. Expects token sequences of the forms
    ///
    ///     <name>
    ///     <name>(<type>)
    ///
    /// where
    ///  - `name` is the variant name
    ///  - `type` is the optional variant type.
    pub fn from(parser: &mut FileParser) -> ParseResult<Self> {
        let start_pos = parser.current_position();
        let name = parser.parse_identifier()?;

        // Parse the optional variant type.
        let (typ, end_pos) = match parser.parse_optional(TokenKind::LeftParen) {
            Some(_) => {
                // Parse `<type>)`.
                let typ = Type::parse(parser)?;
                let token = parser.parse_expecting(TokenKind::RightParen)?;
                (Some(typ), token.span.end_pos)
            }
            None => {
                let mut end_pos = start_pos;
                end_pos.col += name.len() as u32;
                (None, end_pos)
            }
        };

        Ok(EnumTypeVariant {
            name,
            maybe_type: typ,
            span: parser.new_span(start_pos, end_pos),
        })
    }
}

/// An enumerated type.
#[derive(Debug, Eq, Clone)]
pub struct EnumType {
    pub name: Name,
    pub maybe_params: Option<Params>,
    pub variants: Vec<EnumTypeVariant>,
    pub is_pub: bool,
    pub span: Span,
}

impl PartialEq for EnumType {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
            && self.maybe_params == other.maybe_params
            && util::vecs_eq(&self.variants, &other.variants)
    }
}

impl Display for EnumType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {} {{", TokenKind::Enum, self.name)?;

        for (i, variant) in self.variants.iter().enumerate() {
            match i {
                0 => write!(f, "{}", variant)?,
                _ => write!(f, ", {}", variant)?,
            }
        }

        write!(f, "}}")
    }
}

impl Hash for EnumType {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.name.hash(state);

        for variant in &self.variants {
            variant.hash(state);
        }
    }
}

locatable_impl!(EnumType);

impl EnumType {
    /// Parses enum type declarations. Expects token sequences of the form
    ///
    ///     pub enum <name><params> {
    ///         <variant_name>(<variant_type>)
    ///         ...
    ///     }
    ///
    /// where
    ///  - `name` is the name of the enum type
    ///  - `params` are optional generic parameters
    ///  - `variant_name` is the name of a variant of the enum type
    ///  - `variant_type` is the optional variant type
    ///  - `pub` is optional.
    pub fn parse(parser: &mut FileParser) -> ParseResult<Self> {
        let is_pub = parser.parse_optional(TokenKind::Pub).is_some();
        let start_pos = parser.current_position();

        // Parse `enum <name>`.
        parser.parse_expecting(TokenKind::Enum)?;
        let name = Name::parse(parser)?;

        // Parse optional parameters.
        let maybe_params = match parser.next_token_is(&TokenKind::LeftBracket) {
            true => Some(Params::parse(parser)?),
            false => None,
        };

        parser.parse_expecting(TokenKind::LeftBrace)?;

        // Parse the enum variants ending with `}`.
        let mut variants = vec![];
        let end_pos = loop {
            if let Some(token) = parser.parse_optional(TokenKind::RightBrace) {
                break token.span.end_pos;
            }

            variants.push(EnumTypeVariant::from(parser)?);

            // Parse the optional comma.
            parser.parse_optional(TokenKind::Comma);
        };

        Ok(EnumType {
            name,
            maybe_params,
            variants,
            is_pub,
            span: parser.new_span(start_pos, end_pos),
        })
    }
}

/// Represents enum variant initialization.
#[derive(Debug, Clone, Eq)]
pub struct EnumVariantInit {
    pub typ: UnresolvedType,
    pub variant_name: String,
    pub maybe_value: Option<Box<Expression>>,
    pub span: Span,
}

impl PartialEq for EnumVariantInit {
    fn eq(&self, other: &Self) -> bool {
        self.typ == other.typ
            && self.variant_name == other.variant_name
            && self.maybe_value == other.maybe_value
    }
}

impl Display for EnumVariantInit {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}{}{}",
            self.typ,
            TokenKind::DoubleColon,
            self.variant_name
        )?;

        if let Some(value) = &self.maybe_value {
            write!(f, "({})", value)?;
        }

        Ok(())
    }
}

impl Hash for EnumVariantInit {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.typ.hash(state);
        self.variant_name.hash(state);
        self.maybe_value.hash(state);
    }
}

impl EnumVariantInit {
    /// Parses enum variant initialization. Expects token sequences of the forms
    ///
    ///     <type>::<variant_name>
    ///     <type>::<variant_name>(<value>)
    ///
    /// where
    ///  - `type` is the enum type symbol
    ///  - `variant_name` is an identifier representing the enum type variant
    ///  - `value` is an expression representing the optional value associated with the enum
    ///    variant.
    pub fn parse(parser: &mut FileParser) -> ParseResult<Self> {
        let start_pos = parser.current_position();

        // Parse the enum type symbol followed by `::`.
        let typ = UnresolvedType::from_symbol(Symbol::parse(parser)?);
        parser.parse_expecting(TokenKind::DoubleColon)?;

        // In case there is no value in this initialization, compute the end position now.
        let mut end_pos = match parser.tokens.peek_next() {
            Some(t) => t.span.end_pos,
            None => Position::default(),
        };
        let variant_name = parser.parse_identifier()?;

        // Parse the optional `(<value>)`.
        let maybe_value = match parser.parse_optional(TokenKind::LeftParen) {
            Some(_) => {
                let expr = Expression::parse(parser)?;
                end_pos = parser.parse_expecting(TokenKind::RightParen)?.span.end_pos;
                Some(Box::new(expr))
            }
            None => None,
        };

        Ok(EnumVariantInit {
            typ,
            variant_name,
            maybe_value,
            span: parser.new_span(start_pos, end_pos),
        })
    }
}

locatable_impl!(EnumVariantInit);
