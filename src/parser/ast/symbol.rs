use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};

use crate::fmt::vec_to_string;
use crate::lexer::pos::{Locatable, Position, Span};
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::ast::r#type::Type;
use crate::parser::error::ParseResult;
use crate::parser::module::Module;

/// Represents a named value. These can be variables, variable member accesses, functions,
/// constants, or types. The value can also optionally include parameters (generics).
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Symbol {
    /// Some symbols will be accessed from other imported modules. For example:
    ///
    ///     use "my_project/my_file.bl"
    ///     // ...
    ///         @my_file.some_fn(...)
    ///
    /// In these cases, the module path specified with `@<mod_name>` is included
    /// in the symbol name and will be available via this field.
    pub maybe_mod_name: Option<String>,
    pub name: String,
    pub params: Vec<Type>,
    pub span: Span,
}

impl Display for Symbol {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let params = format!("[{}]", vec_to_string(&self.params, ", "));

        write!(
            f,
            "{}{}{}",
            match &self.maybe_mod_name {
                Some(name) => format!("@{}.", name),
                None => "".to_string(),
            },
            self.name,
            match self.params.is_empty() {
                true => "",
                false => params.as_str(),
            }
        )
    }
}

impl Hash for Symbol {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.name.hash(state);
    }
}

locatable_impl!(Symbol);

impl Symbol {
    /// Creates a new symbol.
    pub fn new(name: &str, span: Span) -> Self {
        Symbol {
            maybe_mod_name: None,
            name: name.to_string(),
            params: vec![],
            span,
        }
    }

    /// Creates a new symbol with default (zero) start and end positions.
    #[cfg(test)]
    pub fn new_with_default_pos(name: &str) -> Self {
        Symbol {
            maybe_mod_name: None,
            name: name.to_string(),
            params: vec![],
            span: Default::default(),
        }
    }

    /// Attempts to parse a symbol from a single identifier.
    pub fn from_identifier(tokens: &mut Stream<Token>) -> ParseResult<Symbol> {
        let start_pos = Module::current_position(tokens);
        let ident = Module::parse_identifier(tokens)?;
        Ok(Symbol::new(
            ident.as_str(),
            Span {
                start_pos,
                end_pos: Module::prev_position(tokens),
            },
        ))
    }

    /// Attempts to parse a symbol from the given token sequence. Expects token
    /// sequences of the forms:
    ///
    ///     <ident>
    ///     <ident>[<param>, ...]
    ///     @<mod_name>.<ident>
    ///     @<mod_name>.<ident>[<param>, ...]
    ///
    /// where
    /// - `ident` is an identifier
    /// - `mod_name` is an identifier that represents the module the symbol comes from
    /// - `param` is an expression representing a compile-time parameter (either a
    ///   generic type or a constant.
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Symbol> {
        let start_pos = Module::current_position(tokens);

        // Parse the optional module name.
        let maybe_mod_name = if Module::parse_optional(tokens, TokenKind::At).is_some() {
            let mod_name = Module::parse_identifier(tokens)?;
            Module::parse_expecting(tokens, TokenKind::Dot)?;
            Some(mod_name)
        } else {
            None
        };

        // Parse the symbol name.
        let name = Module::parse_identifier(tokens)?;

        // Parse optional parameters.
        let mut params = vec![];
        if Module::parse_optional(tokens, TokenKind::LeftBracket).is_some() {
            while !Module::next_token_is(tokens, &TokenKind::RightBracket) {
                params.push(Type::from(tokens)?);
                if Module::parse_optional(tokens, TokenKind::Comma).is_none() {
                    Module::parse_expecting(tokens, TokenKind::RightBracket)?;
                    break;
                }
            }
        }

        Ok(Symbol {
            maybe_mod_name,
            name,
            params,
            span: Span {
                start_pos,
                end_pos: Module::prev_position(tokens),
            },
        })
    }
}
