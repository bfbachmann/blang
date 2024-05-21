use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};

use crate::lexer::pos::{Locatable, Position, Span};
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::parser::ast::expr::Expression;
use crate::parser::ast::r#type::Type;
use crate::parser::error::ParseResult;
use crate::parser::module::Module;
use crate::{locatable_impl, util};

/// A variant of an enumerated type.
#[derive(Clone, Debug, Eq)]
pub struct EnumTypeVariant {
    pub name: String,
    pub maybe_type: Option<Type>,
    span: Span,
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
    ///  - `type` is the optional variant type (see `Type::from`).
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        let start_pos = Module::current_position(tokens);
        let name = Module::parse_identifier(tokens)?;

        // Parse the optional variant type.
        let (typ, end_pos) = match Module::parse_optional(tokens, TokenKind::LeftParen) {
            Some(_) => {
                // Parse `<type>)`.
                let typ = Type::from(tokens)?;
                let token = Module::parse_expecting(tokens, TokenKind::RightParen)?;
                (Some(typ), token.span.end_pos)
            }
            None => {
                let mut end_pos = start_pos.clone();
                end_pos.col += name.len();
                (None, end_pos)
            }
        };

        Ok(EnumTypeVariant {
            name,
            maybe_type: typ,
            span: Span { start_pos, end_pos },
        })
    }
}

/// An enumerated type.
#[derive(Debug, Eq, Clone)]
pub struct EnumType {
    pub name: String,
    pub variants: Vec<EnumTypeVariant>,
    pub is_pub: bool,
    span: Span,
}

impl PartialEq for EnumType {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name && util::vecs_eq(&self.variants, &other.variants)
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
    ///     pub enum <name> {
    ///         <variant_name>(<variant_type>)
    ///         ...
    ///     }
    ///
    /// where
    ///  - `name` is the name of the enum type
    ///  - `variant_name` is the name of a variant of the enum type
    ///  - `variant_type` is the optional variant type (see `Type::from`)
    ///  - `pub` is optional.
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        let is_pub = Module::parse_optional(tokens, TokenKind::Pub).is_some();
        let start_pos = Module::current_position(tokens);

        // Parse `enum <name> {`.
        Module::parse_expecting(tokens, TokenKind::Enum)?;
        let name = Module::parse_identifier(tokens)?;
        Module::parse_expecting(tokens, TokenKind::LeftBrace)?;

        // Parse the enum variants ending with `}`.
        let mut variants = vec![];
        let end_pos = loop {
            if let Some(token) = Module::parse_optional(tokens, TokenKind::RightBrace) {
                break token.span.end_pos;
            }

            variants.push(EnumTypeVariant::from(tokens)?);

            // Parse the optional comma.
            Module::parse_optional(tokens, TokenKind::Comma);
        };

        Ok(EnumType {
            name,
            variants,
            is_pub,
            span: Span { start_pos, end_pos },
        })
    }
}

/// Represents enum variant initialization.
#[derive(Debug, Clone, Eq)]
pub struct EnumVariantInit {
    pub enum_type: Type,
    pub variant_name: String,
    pub maybe_value: Option<Box<Expression>>,
    span: Span,
}

impl PartialEq for EnumVariantInit {
    fn eq(&self, other: &Self) -> bool {
        self.enum_type == other.enum_type
            && self.variant_name == other.variant_name
            && util::opts_eq(&self.maybe_value, &other.maybe_value)
    }
}

impl Display for EnumVariantInit {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}{}{}",
            self.enum_type,
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
        self.enum_type.hash(state);
        self.variant_name.hash(state);
        self.maybe_value.hash(state);
    }
}

impl EnumVariantInit {
    /// Parses enum variant initialization. Expects token sequences of the forms
    ///
    ///     <enum_type>::<variant_name>
    ///     <enum_type>::<variant_name>(<value>)
    ///
    /// where
    ///  - `enum_name` is an identifier representing the name of the enum type
    ///  - `variant_name` is an identifier representing the enum type variant
    ///  - `value` is an expression representing the optional value associated with the enum
    ///    variant (see `Expression::from`).
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        let start_pos = Module::current_position(tokens);

        // Parse `<enum_type>::`.
        let enum_type = Type::from(tokens)?;
        Module::parse_expecting(tokens, TokenKind::DoubleColon)?;

        // In case there is no value in this initialization, compute the end position now.
        let mut end_pos = match tokens.peek_next() {
            Some(t) => t.span.end_pos,
            None => Position::default(),
        };
        let variant_name = Module::parse_identifier(tokens)?;

        // Parse the optional `(<value>)`.
        let maybe_value = match Module::parse_optional(tokens, TokenKind::LeftParen) {
            Some(_) => {
                let expr = Expression::from(tokens)?;
                end_pos = Module::parse_expecting(tokens, TokenKind::RightParen)?
                    .span
                    .end_pos;
                Some(Box::new(expr))
            }
            None => None,
        };

        Ok(EnumVariantInit {
            enum_type,
            variant_name,
            maybe_value,
            span: Span { start_pos, end_pos },
        })
    }
}

locatable_impl!(EnumVariantInit);
