use std::fmt::{Display, Formatter};

use colored::Colorize;

use crate::analyzer::ast::r#type::AType;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::scope::ScopedSymbol;
use crate::analyzer::type_store::TypeKey;
use crate::lexer::pos::{Locatable, Position};
use crate::parser::member::MemberAccess;
use crate::parser::symbol::Symbol;
use crate::{format_code, locatable_impl, util};

/// A symbol that can represent a variable, variable access, function, type, or constant.
#[derive(Debug, Clone)]
pub struct ASymbol {
    pub name: String,
    /// The type key of the parent symbol (i.e. not the member(s) being accessed).
    pub parent_type_key: TypeKey,
    pub member_access: Option<AMemberAccess>,
    /// This will be set to true if the name of this symbol matches a type name and no variable
    /// names. If this is the case, the `var_type_key` field will hold the ID of the matching type.
    pub is_type: bool,
    /// This will be set to true if this symbol actually resolves to a constant.
    pub is_const: bool,
    /// This will be set to true if the top-level member of this symbol is an actual variable
    /// that was declared inside a function (or is a function argument). In other words, it will
    /// be false if the top-level symbol refers to a declared function, type, or constant.
    pub is_var: bool,
    /// This will be true if this symbol refers to a method (either on a type or an instance of
    /// a type).
    is_method: bool,
    start_pos: Position,
    end_pos: Position,
}

locatable_impl!(ASymbol);

impl Display for ASymbol {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)?;

        if let Some(access) = &self.member_access {
            write!(f, ".{}", access)?;
        }

        Ok(())
    }
}

impl PartialEq for ASymbol {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
            && self.parent_type_key == other.parent_type_key
            && util::opts_eq(&self.member_access, &other.member_access)
    }
}

impl ASymbol {
    /// Creates a new symbol with default start and end positions.
    pub fn new_with_default_pos(
        name: &str,
        type_key: TypeKey,
        member_access: Option<AMemberAccess>,
    ) -> Self {
        ASymbol {
            name: name.to_string(),
            parent_type_key: type_key,
            member_access,
            is_type: false,
            is_const: false,
            is_var: true,
            is_method: false,
            start_pos: Position::default(),
            end_pos: Position::default(),
        }
    }

    /// Attempts to analyze the symbol (including member accesses). If `include_fns` is
    /// `true`, functions and extern functions will also be searched for the symbol name.
    /// Otherwise, only variables, types, and constants will be searched.
    pub fn from(
        ctx: &mut ProgramContext,
        symbol: &Symbol,
        include_fns: bool,
        maybe_impl_type_key: Option<TypeKey>,
    ) -> Self {
        let var_name = symbol.name.as_str();

        // Find the type key for the symbol or member being accessed.
        // Return a placeholder value if we failed to resolve the symbol type key.
        // TODO: Refactor
        let (mut maybe_type_key, maybe_symbol) =
            ASymbol::get_type_key_by_symbol_name(ctx, symbol.name.as_str(), include_fns);

        let mut is_method = false;
        if maybe_type_key.is_none() && include_fns {
            // We could not find the variable, constant, or function with the given name, so if
            // there is an impl_type_key, check if this function is defined as a member function on
            // that type.
            if let Some(impl_type_key) = maybe_impl_type_key {
                if let Some(mem_fn) = ctx.get_member_fn(impl_type_key, var_name) {
                    maybe_type_key = Some(mem_fn.type_key);
                    is_method = true;
                }
            }
        };

        // If the symbol still has not been resolved, check if it's a type.
        let mut var_is_type = false;
        if maybe_type_key.is_none() && include_fns {
            match ctx.get_type_key_by_type_name(var_name) {
                Some(tk) if !ctx.must_get_type(tk).is_unknown() => {
                    maybe_type_key = Some(tk);
                    var_is_type = true;
                }
                _ => {}
            }
        }

        // At this point the symbol must be resolved, or it doesn't exist in this scope.
        let var_type_key = match maybe_type_key {
            Some(t) => t,
            None => {
                // We could not find the value with the given name, so record the error and return
                // a placeholder value.
                ctx.insert_err(AnalyzeError::new(
                    ErrorKind::UndefSymbol,
                    format_code!("symbol {} is not defined in this scope", var_name).as_str(),
                    symbol,
                ));

                return ASymbol::new_with_default_pos(
                    symbol.name.as_str(),
                    ctx.unknown_type_key(),
                    None,
                );
            }
        };

        // Recursively analyze member accesses, if any.
        let member_access = match &symbol.member_access {
            Some(access) => Some(AMemberAccess::from(ctx, var_type_key, access)),
            None => None,
        };

        // If there is no member access, we need to make sure the symbol is not just a type. This
        // prevents types from being valid expressions.
        if var_is_type && member_access.is_none() {
            ctx.insert_err(AnalyzeError::new(
                ErrorKind::ExpectedExpr,
                format_code!(
                    "expected expression, but found type {}",
                    ctx.display_type_for_key(var_type_key)
                )
                .as_str(),
                symbol,
            ));

            return ASymbol::new_with_default_pos(
                symbol.name.as_str(),
                ctx.unknown_type_key(),
                None,
            );
        }

        // Check if this symbol is actually a constant.
        let (is_const, is_var) = match maybe_symbol {
            Some(var) => (var.is_const, true),
            None => (false, false),
        };

        ASymbol {
            name: var_name.to_string(),
            parent_type_key: var_type_key,
            member_access,
            is_type: var_is_type,
            is_const,
            is_var,
            is_method,
            start_pos: symbol.start_pos().clone(),
            end_pos: symbol.end_pos().clone(),
        }
    }

    /// Analyzes `symbol`, where `symbol` must be a type and nothing else.
    pub fn from_type(ctx: &mut ProgramContext, symbol: &Symbol) -> Self {
        // Try resolve the type from the symbol name.
        let maybe_type_key = ctx.get_type_key_by_type_name(symbol.name.as_str());

        // Make sure we could resolve the type.
        // Since we're expecting a type here, also make sure there is no member access.
        if maybe_type_key.is_none() || symbol.member_access.is_some() {
            ctx.insert_err(AnalyzeError::new(
                ErrorKind::ExpectedType,
                format_code!("expected type, but found {}", symbol).as_str(),
                symbol,
            ));

            return ASymbol::new_with_default_pos(
                symbol.name.as_str(),
                ctx.unknown_type_key(),
                None,
            );
        }

        ASymbol {
            name: symbol.name.clone(),
            parent_type_key: maybe_type_key.unwrap(),
            member_access: None,
            is_type: true,
            is_const: false,
            is_var: false,
            is_method: false,
            start_pos: symbol.start_pos.clone(),
            end_pos: symbol.end_pos.clone(),
        }
    }

    /// Returns the type key of the accessed submember (i.e. the type of the member at the end of
    /// the member access chain), or of the symbol itself if there is no member access.
    pub fn get_type_key(&self) -> TypeKey {
        match &self.member_access {
            Some(ma) => ma.get_type_key(),
            None => self.parent_type_key,
        }
    }

    /// Returns the name of the lowest level member on this variable access, or just the symbol
    /// name if there is no member access.
    pub fn get_last_member_name(&self) -> String {
        match &self.member_access {
            Some(access) => access.get_last_member_name(),
            None => self.name.to_string(),
        }
    }

    /// Attempts to find the type key of a symbol with the given name. Additionally, if `name`
    /// can be resolved to an actual variable, the variable will be returned.
    fn get_type_key_by_symbol_name(
        ctx: &ProgramContext,
        name: &str,
        include_fns: bool,
    ) -> (Option<TypeKey>, Option<ScopedSymbol>) {
        // Search for a variable with the given name. Variables take precedence over functions.
        if let Some(symbol) = ctx.get_symbol(name) {
            return (Some(symbol.type_key), Some(symbol.clone()));
        }

        if include_fns {
            // Search for a function with the given name. Functions take precedence over extern
            // functions.
            if let Some(func) = ctx.get_fn(name) {
                return (Some(func.signature.type_key), None);
            };

            // Search for an extern function with the given name.
            if let Some(fn_sig) = ctx.get_defined_fn_sig(name) {
                return (Some(fn_sig.type_key), None);
            }
        }

        (None, None)
    }

    /// Removes the last member on this member access chain, or does nothing if there are no
    /// members.
    pub fn without_last_member(mut self) -> Self {
        if let Some(member_access) = &mut self.member_access {
            if member_access.submember.is_none() {
                self.member_access = None;
            } else {
                self.member_access = Some(self.member_access.unwrap().without_last_member());
            }
        }

        self
    }

    /// Returns true if the last member on this symbol refers to a method on a type or instance.
    pub fn is_method(&self) -> bool {
        match &self.member_access {
            Some(access) => access.is_method(),
            None => self.is_method,
        }
    }
}

/// Represents a member access on a variable or type.
#[derive(Debug, Clone)]
pub struct AMemberAccess {
    pub member_name: String,
    pub member_type_key: TypeKey,
    pub submember: Option<Box<AMemberAccess>>,
    /// This will be true if this member access refers to a method (either on an instance or a
    /// type).
    is_method: bool,
}

impl Display for AMemberAccess {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.member_name)?;

        if let Some(access) = &self.submember {
            write!(f, ".{}", access)?;
        }

        Ok(())
    }
}

impl PartialEq for AMemberAccess {
    fn eq(&self, other: &Self) -> bool {
        self.member_name == other.member_name
            && self.member_type_key == other.member_type_key
            && util::opts_eq(&self.submember, &other.submember)
    }
}

impl AMemberAccess {
    /// Attempts to recursively analyze a member access on the given type.
    fn from(ctx: &mut ProgramContext, type_key: TypeKey, member_access: &MemberAccess) -> Self {
        let typ = ctx.must_get_type(type_key);
        let member_name = &member_access.member_name;

        // Check if the member access is accessing a field on a struct or tuple type.
        let maybe_field_type_key = match typ {
            AType::Struct(struct_type) => struct_type.get_field_type_key(member_name.as_str()),
            AType::Tuple(tuple_type) => {
                let field_index = member_name.parse::<usize>().unwrap();
                match tuple_type.get_field_type_key(field_index) {
                    Some(i) => Some(i),
                    None => None,
                }
            }
            _ => None,
        };

        // If we failed to find a field on this type with a matching name, check for a member
        // function with a matching name.
        let mut is_method = false;
        let maybe_field_type_key = if maybe_field_type_key.is_none() {
            match ctx.get_member_fn(type_key, member_name) {
                Some(member_fn_sig) => {
                    is_method = true;
                    Some(member_fn_sig.type_key)
                }
                None => None,
            }
        } else {
            maybe_field_type_key
        };

        // Error and return a placeholder value if we couldn't locate the member being accessed.
        if maybe_field_type_key.is_none() {
            ctx.insert_err(AnalyzeError::new(
                ErrorKind::UndefMember,
                format_code!("type {} has no member {}", typ.display(ctx), member_name).as_str(),
                member_access,
            ));

            return AMemberAccess {
                member_name: member_name.to_string(),
                member_type_key: ctx.unknown_type_key(),
                submember: None,
                is_method,
            };
        }

        // If a submember is being accessed, continue resolving it recursively. Otherwise,
        // just return the field type.
        let field_type_key = maybe_field_type_key.unwrap();
        match &member_access.submember {
            Some(submember) => {
                let submember_access = AMemberAccess::from(ctx, field_type_key, submember.as_ref());
                AMemberAccess {
                    member_name: member_name.to_string(),
                    member_type_key: field_type_key,
                    submember: Some(Box::new(submember_access)),
                    is_method,
                }
            }
            None => AMemberAccess {
                member_name: member_name.to_string(),
                member_type_key: field_type_key,
                submember: None,
                is_method,
            },
        }
    }

    /// Returns the type key of the accessed submember (i.e. the type of the member at the end
    /// of the member access chain).
    fn get_type_key(&self) -> TypeKey {
        match &self.submember {
            Some(sub) => sub.get_type_key(),
            None => self.member_type_key,
        }
    }

    /// Returns the name of the lowest level member on this member access, or just the member
    /// name if there is no sub-member access.
    pub fn get_last_member_name(&self) -> String {
        match &self.submember {
            Some(sub) => sub.get_last_member_name(),
            None => self.member_name.to_string(),
        }
    }

    /// Removes the last member on this member access chain, or does nothing if there is no
    /// sub-member.
    pub fn without_last_member(mut self) -> Self {
        if let Some(sub) = &mut self.submember {
            if sub.submember.is_none() {
                self.submember = None;
            } else {
                self.submember = Some(Box::new(self.submember.unwrap().without_last_member()));
            }
        }

        self
    }

    /// Returns true if the last member on this member access chain is a method on a type or
    /// instance.
    pub fn is_method(&self) -> bool {
        match &self.submember {
            Some(sub) => sub.is_method(),
            None => self.is_method,
        }
    }
}
