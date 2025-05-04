use crate::fmt::vec_to_string;
use crate::lexer::pos::Span;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::ast::r#type::Type;
use crate::parser::ast::unresolved::UnresolvedType;
use crate::parser::error::ParseResult;
use crate::parser::file_parser::FileParser;
use crate::Locatable;
use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct Name {
    pub value: String,
    pub span: Span,
}

impl Display for Name {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

impl Name {
    pub fn parse(parser: &mut FileParser) -> ParseResult<Name> {
        let start_pos = parser.current_position();
        let name = parser.parse_identifier()?;
        let end_pos = parser.prev_position();
        Ok(Name {
            value: name,
            span: Span {
                file_id: parser.file_id,
                start_pos,
                end_pos,
            },
        })
    }
}

/// Represents a named value. These can be variables, variable member accesses, functions,
/// constants, or types. The value can also optionally include parameters (generics).
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Symbol {
    /// Some symbols will be accessed from other imported modules. For example:
    ///
    ///     use "my_project/my_mod" @my_mod
    ///     // ...
    ///         @my_mod.some_fn(...)
    ///
    /// In these cases, the module path specified with `@<mod_name>` is included
    /// in the symbol name and will be available via this field.
    pub maybe_mod_name: Option<Name>,
    pub name: Name,
    pub params: Vec<Type>,
    pub span: Span,
}

impl Display for Symbol {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let params = format!("[{}]", vec_to_string(&self.params, ", "));

        write!(
            f,
            "{}{}{}",
            match self.maybe_mod_name.as_ref() {
                Some(sym) => format!("@{}.", sym.value),
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
    pub fn new(name: Name, span: Span) -> Self {
        Symbol {
            maybe_mod_name: None,
            name,
            params: vec![],
            span,
        }
    }

    /// Attempts to parse a symbol from a single identifier.
    pub fn parse_as_identifier(parser: &mut FileParser) -> ParseResult<Symbol> {
        let name = Name::parse(parser)?;
        let span = name.span;
        Ok(Symbol::new(name, span))
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
    pub fn parse(parser: &mut FileParser) -> ParseResult<Symbol> {
        let start_pos = parser.current_position();

        // Parse the optional module name.
        let maybe_mod_name = if parser.parse_optional(TokenKind::At).is_some() {
            let mod_name = Name::parse(parser)?;
            parser.parse_expecting(TokenKind::Dot)?;
            Some(mod_name)
        } else {
            None
        };

        // Parse the symbol name.
        let name = Name::parse(parser)?;

        // Parse optional parameters.
        let mut params = vec![];
        if parser.parse_optional(TokenKind::LeftBracket).is_some() {
            while !parser.next_token_is(&TokenKind::RightBracket) {
                params.push(Type::parse(parser)?);
                if parser.parse_optional(TokenKind::Comma).is_none() {
                    parser.parse_expecting(TokenKind::RightBracket)?;
                    break;
                }
            }
        }

        Ok(Symbol {
            maybe_mod_name,
            name,
            params,
            span: parser.new_span(start_pos, parser.prev_position()),
        })
    }

    /// Returns the symbol as an unresolved type.
    pub fn as_unresolved_type(&self) -> Type {
        Type::Unresolved(UnresolvedType::from_symbol(self.clone()))
    }

    /// Returns true if the symbol is the wildcard symbol `_`.
    pub fn is_wildcard(&self) -> bool {
        self.name.value == "_" && self.maybe_mod_name.is_none() && self.params.is_empty()
    }

    /// Returns true if the symbol is just a simple identifier (i.e. no params or mod name).
    pub fn is_name_only(&self) -> bool {
        self.params.is_empty() && self.maybe_mod_name.is_none()
    }
}
