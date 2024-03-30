use std::fmt::{Display, Formatter};

use crate::analyzer::ast::r#const::AConst;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::scope::ScopedSymbol;
use crate::analyzer::type_store::TypeKey;
use crate::lexer::pos::{Locatable, Position};
use crate::parser::ast::symbol::Symbol;
use crate::{format_code, locatable_impl};

/// A symbol that can represent a variable, variable access, function, type, or constant.
#[derive(Debug, Clone)]
pub struct ASymbol {
    pub name: String,
    /// The type key of the symbol.
    pub type_key: TypeKey,
    /// This will be set to true if the name of this symbol matches a type name and no variable
    /// names. If this is the case, the `var_type_key` field will hold the ID of the matching type.
    pub is_type: bool,
    /// This will be set to true if this symbol actually resolves to a constant.
    pub is_const: bool,
    /// This will be set to true if this symbol is an actual variable that was declared inside a
    /// function (or is a function argument). In other words, it will be false if the symbol
    /// refers to a declared function, type, or constant.
    pub is_var: bool,
    /// This will be true if this symbol refers to a method (either on a type or an instance of
    /// a type).
    pub is_method: bool,
    start_pos: Position,
    end_pos: Position,
}

locatable_impl!(ASymbol);

impl Display for ASymbol {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}

impl PartialEq for ASymbol {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name && self.type_key == other.type_key
    }
}

impl ASymbol {
    /// Creates a new symbol with default start and end positions.
    pub fn new_with_default_pos(name: &str, type_key: TypeKey) -> Self {
        ASymbol {
            name: name.to_string(),
            type_key,
            is_type: false,
            is_const: true,
            is_var: false,
            is_method: false,
            start_pos: Position::default(),
            end_pos: Position::default(),
        }
    }

    /// Attempts to analyze the symbol. If `include_fns` is
    /// `true`, functions and extern functions will also be searched for the symbol name.
    /// Otherwise, only variables, types, and constants will be searched.
    /// If `allow_type` is true, the symbol can refer to a type. Otherwise, an error
    /// will be raised if the symbol refers to a type rather than a value.
    pub fn from(
        ctx: &mut ProgramContext,
        symbol: &Symbol,
        include_fns: bool,
        allow_type: bool,
        maybe_impl_type_key: Option<TypeKey>,
    ) -> Self {
        let mut var_name = symbol.name.as_str();

        // Find the type key for the symbol.
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
            Some(t) => {
                // If the variable refers to a function, be sure to update its name to
                // match the function name. We have to do this because function names
                // get mangled, and we have to be sure that the variables that reference
                // them get mangled too.
                let typ = ctx.must_get_type(t);
                if typ.is_fn() {
                    let manged_name = typ.to_fn_sig().mangled_name.as_str();
                    if !manged_name.is_empty() {
                        var_name = manged_name;
                    }
                }
                t
            }
            None => {
                // We could not find the value with the given name, so record the error and return
                // a placeholder value.
                ctx.insert_err(AnalyzeError::new(
                    ErrorKind::UndefSymbol,
                    format_code!("{} is not defined in this scope", var_name).as_str(),
                    symbol,
                ));

                return ASymbol::new_with_default_pos(symbol.name.as_str(), ctx.unknown_type_key());
            }
        };

        // We need to make sure the symbol is not just a type. This prevents types from being valid expressions.
        if !allow_type && var_is_type {
            ctx.insert_err(AnalyzeError::new(
                ErrorKind::ExpectedExpr,
                format_code!(
                    "expected expression, but found type {}",
                    ctx.display_type_for_key(var_type_key)
                )
                .as_str(),
                symbol,
            ));

            return ASymbol::new_with_default_pos(symbol.name.as_str(), ctx.unknown_type_key());
        }

        // Check if this symbol is actually a constant.
        let (is_const, is_var) = match maybe_symbol {
            Some(var) => (var.is_const, true),
            None => (false, false),
        };

        ASymbol {
            name: var_name.to_string(),
            type_key: var_type_key,
            is_type: var_is_type,
            is_const,
            is_var,
            is_method,
            start_pos: symbol.start_pos().clone(),
            end_pos: symbol.end_pos().clone(),
        }
    }

    /// Attempts to find the type key of a symbol with the given name. Additionally, if `name`
    /// can be resolved to an actual variable, the variable will be returned.
    fn get_type_key_by_symbol_name(
        ctx: &mut ProgramContext,
        name: &str,
        include_fns: bool,
    ) -> (Option<TypeKey>, Option<ScopedSymbol>) {
        // Search for a variable with the given name. Variables take precedence over functions.
        if let Some(symbol) = ctx.get_symbol(name) {
            return (Some(symbol.type_key), Some(symbol.clone()));
        }

        // Check if the symbol refers to a constant that has not yet been analyzed.
        if let Some(const_) = ctx.get_unchecked_const(name) {
            let a_const = AConst::from(ctx, &const_.clone());
            let symbol = ctx.get_symbol(a_const.name.as_str()).unwrap();
            return (Some(symbol.type_key), Some(symbol.clone()));
        }

        if include_fns {
            // Search for a function with the given name. Functions take precedence over extern
            // functions.
            if let Some(func) = ctx.get_fn(ctx.mangle_name(name).as_str()) {
                return (Some(func.signature.type_key), None);
            };

            // Search for an extern function with the given name.
            if let Some(fn_sig) = ctx.get_defined_fn_sig(name) {
                return (Some(fn_sig.type_key), None);
            }
        }

        (None, None)
    }
}
