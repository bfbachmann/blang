use std::fmt::{Display, Formatter};

use crate::analyzer::ast::r#const::AConst;
use crate::analyzer::ast::r#type::AType;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::scope::ScopedSymbol;
use crate::analyzer::type_store::TypeKey;
use crate::fmt::format_code_vec;
use crate::lexer::pos::{Locatable, Position, Span};
use crate::parser::ast::pointer::PointerType;
use crate::parser::ast::r#type::Type;
use crate::parser::ast::symbol::Symbol;
use crate::parser::ast::unresolved::UnresolvedType;
use crate::{format_code, locatable_impl};

/// A symbol that can represent a variable, variable access, function, type, or constant.
#[derive(Debug, Clone)]
pub struct ASymbol {
    pub name: String,
    /// The type key of the symbol.
    pub type_key: TypeKey,
    pub maybe_param_tks: Option<Vec<TypeKey>>,
    /// This will be set to true if the name of this symbol matches a type name and no variable
    /// names. If this is the case, the `type_key` field will hold the ID of the matching type.
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
    /// The path of the module from whence the symbol comes.
    pub maybe_mod_path: Option<String>,
    span: Span,
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
            maybe_param_tks: None,
            is_type: false,
            is_const: true,
            is_var: false,
            is_method: false,
            maybe_mod_path: None,
            span: Default::default(),
        }
    }

    /// Attempts to analyze the symbol. If `include_fns` is
    /// `true`, functions and extern functions will also be searched for the symbol name.
    /// Otherwise, only variables, types, and constants will be searched.
    /// If `allow_type` is true, the symbol can refer to a type. Otherwise, an error
    /// will be raised if the symbol refers to a type rather than a value.
    /// If `no_params` is true, an error will be raised if the symbol includes generic
    /// parameters.
    pub fn from(
        ctx: &mut ProgramContext,
        symbol: &Symbol,
        include_fns: bool,
        allow_type: bool,
        no_params: bool,
        maybe_impl_type_key: Option<TypeKey>,
    ) -> Self {
        let mut var_name = symbol.name.clone();

        // Check for intrinsic symbols like `null`.
        if let Some(intrinsic) = maybe_get_intrinsic(ctx, symbol) {
            return intrinsic;
        }

        // Return early if the mod name is invalid.
        let maybe_mod_path = if let Some(mod_name) = symbol.maybe_mod_name.as_ref() {
            if !ctx.check_mod_name(mod_name, symbol) {
                return ASymbol::new_with_default_pos(symbol.name.as_str(), ctx.unknown_type_key());
            }

            ctx.get_mod_path(mod_name).cloned()
        } else {
            Some(ctx.get_cur_mod_path().to_owned())
        };

        // Find the type key for the symbol.
        // Return a placeholder value if we failed to resolve the symbol type key.
        // TODO: Refactor
        let (mut maybe_type_key, maybe_symbol) = get_type_key_for_symbol(ctx, symbol, include_fns);

        let mut is_method = false;
        if maybe_type_key.is_none() && include_fns {
            // We could not find the variable, constant, or function with the given name, so if
            // there is an impl_type_key, check if this function is defined as a member function on
            // that type.
            if let Some(impl_type_key) = maybe_impl_type_key {
                match ctx.get_or_monomorphize_member_fn(impl_type_key, var_name.as_str()) {
                    // There is exactly one matching member function.
                    Ok(Some(fn_sig)) => {
                        maybe_type_key = Some(fn_sig.type_key);
                        is_method = true;
                    }

                    // There are many member functions by that name.
                    Err(_) => {
                        let type_display = ctx.display_type(impl_type_key);
                        ctx.insert_err(
                            AnalyzeError::new(
                                ErrorKind::AmbiguousAccess,
                                format_code!(
                                    "ambiguous access to member {} on type {}",
                                    var_name,
                                    type_display
                                )
                                .as_str(),
                                symbol,
                            )
                            .with_detail(
                                format_code!(
                                    "There are multiple methods named {} on type {}.",
                                    var_name,
                                    type_display
                                )
                                .as_str(),
                            )
                            .with_help("Consider referring to the method via its type or spec."),
                        );

                        return ASymbol::new_with_default_pos(
                            symbol.name.as_str(),
                            ctx.unknown_type_key(),
                        );
                    }

                    // There are no matching member functions.
                    Ok(None) => {}
                }
            }
        };

        // If the symbol still has not been resolved, check if it's a type.
        let mut is_type = false;
        if maybe_type_key.is_none() {
            match ctx.get_type_key_by_type_name(symbol.maybe_mod_name.as_ref(), var_name.as_str()) {
                Some(tk) if !ctx.must_get_type(tk).is_unknown() => {
                    maybe_type_key = Some(tk);
                    is_type = true;
                }
                _ => {}
            }
        }

        // At this point the symbol must be resolved, or it doesn't exist in this scope.
        let var_type_key = match maybe_type_key {
            Some(tk) => {
                // If the symbol refers to a function, be sure to update its name to
                // match the function name. We have to do this because function names
                // get mangled, and we have to be sure that the variables that reference
                // them get mangled too.
                match ctx.must_get_type(tk) {
                    AType::Function(fn_sig) if !fn_sig.name.is_empty() => {
                        var_name = fn_sig.mangled_name.clone();
                    }
                    _ => {}
                }
                tk
            }
            None => {
                // We could not find the value with the given name, so record the error and return
                // a placeholder value.
                ctx.insert_err(AnalyzeError::new(
                    ErrorKind::UndefSymbol,
                    format_code!("{} is not defined", symbol).as_str(),
                    symbol,
                ));

                return ASymbol::new_with_default_pos(symbol.name.as_str(), ctx.unknown_type_key());
            }
        };

        // We need to make sure the symbol is not just a type. This prevents types from being valid expressions.
        if is_type && !allow_type {
            ctx.insert_err(AnalyzeError::new(
                ErrorKind::ExpectedExpr,
                format_code!(
                    "expected expression, but found type {}",
                    ctx.display_type(var_type_key)
                )
                .as_str(),
                symbol,
            ));

            return ASymbol::new_with_default_pos(symbol.name.as_str(), ctx.unknown_type_key());
        }

        // Check if this symbol is actually a constant.
        let (is_const, is_var, maybe_mod_path) = match maybe_symbol {
            Some(var) => (var.is_const, true, var.maybe_mod_path),
            None => (false, false, maybe_mod_path),
        };

        // Analyze any generic parameters on this symbol and use them to monomorphize
        // the generic value, if it is generic. We don't do this if it's a type
        // because it would have already been done during type resolution.
        let (mono_type_key, maybe_param_tks) = match symbol.params.is_empty() {
            false => {
                if no_params {
                    ctx.insert_err(AnalyzeError::new(
                        ErrorKind::UnexpectedParams,
                        "parameters not allowed here",
                        symbol,
                    ));
                }

                if is_type {
                    let mono_tk = ctx.resolve_type(&Type::Unresolved(UnresolvedType::from_symbol(
                        symbol.clone(),
                    )));
                    (mono_tk, None)
                } else {
                    // We're only including parameter type keys here so the symbol
                    // resolver in the code generator can figure out which concrete
                    // type this symbol maps to.
                    let mono_tk =
                        ctx.monomorphize_parameterized_type(var_type_key, &symbol.params, symbol);
                    let param_tks = symbol.params.iter().map(|t| ctx.resolve_type(t)).collect();
                    (mono_tk, Some(param_tks))
                }
            }

            true => {
                // No parameters were provided, so the type had better not be
                // parameterized unless `no_params` is false or the symbol type is the current
                // `impl` type.
                let poly_type = ctx.must_get_type(var_type_key);
                if !no_params
                    && !ctx
                        .get_cur_self_type_key()
                        .is_some_and(|tk| tk == var_type_key)
                {
                    if let Some(params) = poly_type.params() {
                        let param_names = params.params.iter().map(|p| p.name.as_str()).collect();
                        ctx.insert_err(
                            AnalyzeError::new(
                                ErrorKind::UnresolvedParams,
                                "unresolved parameters",
                                symbol,
                            )
                            .with_detail(
                                format!(
                                    "{} has polymorphic type {} which requires that types \
                                    be specified for parameters: {}.",
                                    format_code!(symbol),
                                    format_code!(ctx.display_type(var_type_key)),
                                    format_code_vec(&param_names, ", "),
                                )
                                .as_str(),
                            ),
                        )
                    }
                }

                (var_type_key, None)
            }
        };

        ASymbol {
            name: var_name,
            type_key: mono_type_key,
            maybe_param_tks,
            is_type,
            is_const,
            is_var,
            is_method,
            maybe_mod_path,
            span: symbol.span,
        }
    }

    /// Returns true if this symbol represents the `null` intrinsic value.
    pub fn is_null_intrinsic(&self) -> bool {
        self.name == "null" && !self.is_method && self.is_const && !self.is_var
    }

    /// Creates a new symbol representing the `null` intrinsic.
    pub fn new_null(
        ctx: &mut ProgramContext,
        maybe_type_key: Option<TypeKey>,
        span: Span,
    ) -> ASymbol {
        // Use type `*mut u8` for the null symbol by default. In most cases, its
        // type will be coerced to the appropriate pointer type anyway.
        let type_key = match maybe_type_key {
            Some(tk) => tk,
            None => ctx.resolve_type(&Type::Pointer(Box::new(PointerType::new_with_default_pos(
                Type::new_unresolved("u8"),
                true,
            )))),
        };

        ASymbol {
            name: "null".to_string(),
            type_key,
            maybe_param_tks: None,
            is_type: false,
            is_const: true,
            is_var: false,
            is_method: false,
            maybe_mod_path: None,
            span,
        }
    }
}

/// Attempts to find the type key of a symbol. Additionally, if `symbol`
/// can be resolved to an actual variable, the variable will be returned.
fn get_type_key_for_symbol(
    ctx: &mut ProgramContext,
    symbol: &Symbol,
    include_fns: bool,
) -> (Option<TypeKey>, Option<ScopedSymbol>) {
    let maybe_mod_name = symbol.maybe_mod_name.as_ref();
    let name = symbol.name.as_str();

    // Search for a variable with the given name. Variables take precedence over functions.
    if let Some(scoped_symbol) = ctx.get_scoped_symbol(maybe_mod_name, name) {
        return (Some(scoped_symbol.type_key), Some(scoped_symbol.clone()));
    }

    // Check if the symbol refers to a constant that has not yet been analyzed.
    if let Some(const_) = ctx.get_unchecked_const(name) {
        let a_const = AConst::from(ctx, &const_.clone());
        let symbol = ctx.get_scoped_symbol(None, a_const.name.as_str()).unwrap();
        return (Some(symbol.type_key), Some(symbol.clone()));
    }

    if include_fns {
        // Search for a function with the given name. Functions take precedence over extern
        // functions.
        let mangled_name_with_path = ctx.mangle_name(maybe_mod_name, None, None, name, true);
        if let Some(func) = ctx.get_fn(maybe_mod_name, mangled_name_with_path.as_str()) {
            return (Some(func.signature.type_key), None);
        };

        // Search for an extern function with the given name.
        let mangled_name_without_path = ctx.mangle_name(maybe_mod_name, None, None, name, false);
        if let Some(fn_sig) =
            ctx.get_fn_sig_by_mangled_name(maybe_mod_name, mangled_name_without_path.as_str())
        {
            return (Some(fn_sig.type_key), None);
        }
    }

    (None, None)
}

/// Tries to locate an intrinsic that matches the given symbol and returns it
/// if one exists.
fn maybe_get_intrinsic(ctx: &mut ProgramContext, symbol: &Symbol) -> Option<ASymbol> {
    // Check for the `null` intrinsic.
    if symbol.maybe_mod_name.is_none() && symbol.name == "null" {
        return Some(ASymbol::new_null(ctx, None, symbol.span));
    }

    None
}
