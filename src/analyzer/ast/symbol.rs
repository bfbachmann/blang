use std::fmt::{Display, Formatter};

use crate::analyzer::ast::params::AParam;
use crate::analyzer::ast::r#const::AConst;
use crate::analyzer::ast::r#type::AType;
use crate::analyzer::error::{AnalyzeError, AnalyzeResult, ErrorKind};
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::scope::ScopedSymbol;
use crate::analyzer::type_store::TypeKey;
use crate::fmt::format_code_vec;
use crate::lexer::pos::{Locatable, Position, Span};
use crate::parser::ast::pointer::PointerType;
use crate::parser::ast::r#type::Type;
use crate::parser::ast::symbol::Symbol;
use crate::{format_code, locatable_impl};

/// A symbol that can represent a variable, variable access, function, type, or constant.
#[derive(Debug, Clone)]
pub struct ASymbol {
    pub name: String,
    /// The type key of the symbol.
    pub type_key: TypeKey,
    /// The type key for the symbol's polymorphic type before it was monomorphized.
    pub poly_type_key: TypeKey,
    pub maybe_param_tks: Option<Vec<TypeKey>>,
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
            poly_type_key: type_key,
            maybe_param_tks: None,
            is_type: false,
            is_const: true,
            is_var: false,
            is_method: false,
            span: Default::default(),
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
        let mut var_name = symbol.name.clone();

        // Check for intrinsic symbols like `null`.
        if let Some(intrinsic) = maybe_get_intrinsic(ctx, symbol) {
            return intrinsic;
        }

        // Return early if the mod name is invalid.
        if let Some(mod_name) = symbol.maybe_mod_name.as_ref() {
            if !ctx.check_mod_name(mod_name, symbol) {
                return ASymbol::new_with_default_pos(symbol.name.as_str(), ctx.unknown_type_key());
            }
        }

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
                if let Some(mem_fn) = ctx.get_member_fn(impl_type_key, var_name.as_str()) {
                    maybe_type_key = Some(mem_fn.type_key);
                    is_method = true;
                }
            }
        };

        // If the symbol still has not been resolved, check if it's a type.
        let mut is_type = false;
        if maybe_type_key.is_none() && include_fns {
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
        if !allow_type && is_type {
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

        // Analyze any generic parameters on this symbol and use them to monomorphize
        // the generic type, if it is generic.
        let (var_type_key, poly_type_key, maybe_param_tks) =
            match analyze_params(ctx, symbol, var_type_key) {
                Ok(param_tks) if !param_tks.is_empty() => {
                    // Monomorphize the type using the provided parameter values.
                    (
                        ctx.monomorphize_type(var_type_key, &param_tks),
                        var_type_key,
                        Some(param_tks),
                    )
                }
                _ => (var_type_key, var_type_key, None),
            };

        ASymbol {
            name: var_name,
            type_key: var_type_key,
            poly_type_key,
            maybe_param_tks,
            is_type,
            is_const,
            is_var,
            is_method,
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
            poly_type_key: type_key,
            maybe_param_tks: None,
            is_type: false,
            is_const: true,
            is_var: false,
            is_method: false,
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
        if let Some(func) = ctx.get_fn(maybe_mod_name, ctx.mangle_fn_name(name).as_str()) {
            return (Some(func.signature.type_key), None);
        };

        // Search for an extern function with the given name.
        if let Some(fn_sig) = ctx.get_defined_fn_sig(maybe_mod_name, name) {
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

/// Analyzes generic parameters on a symbol and returns them, if there are any.
/// Returns an empty error if parameter analysis failed.
fn analyze_params(
    ctx: &mut ProgramContext,
    symbol: &Symbol,
    var_type_key: TypeKey,
) -> Result<Vec<TypeKey>, ()> {
    let typ = ctx.must_get_type(var_type_key);
    let type_display = typ.display(ctx);
    let mut param_types = vec![];
    let mut param_errs = vec![];

    // If the symbol refers to a generic type or function, we need to make sure that
    // all the required params were provided.
    if let Some(type_params) = typ.params() {
        // Raise error if the wrong number of params were provided.
        let expected_num_params = type_params.params.len();
        let passed_num_params = symbol.params.len();
        if passed_num_params != expected_num_params {
            param_errs.push(
                AnalyzeError::new(
                    ErrorKind::UnresolvedParams,
                    format!(
                        "expected {} generic parameter{}, but found {}",
                        expected_num_params,
                        match expected_num_params > 1 {
                            true => "s",
                            false => "",
                        },
                        passed_num_params
                    )
                    .as_str(),
                    symbol,
                )
                .with_detail(
                    format_code!(
                        "Some generic parameters for {} could not be resolved in this context.",
                        type_display,
                    )
                    .as_str(),
                ),
            );
        }

        // Make sure parameter values are of the right types.
        for (passed_param_type, expected_param) in symbol
            .params
            .clone()
            .into_iter()
            .zip(type_params.params.clone().into_iter())
        {
            match analyze_param(ctx, passed_param_type, expected_param, &type_display) {
                Ok(param_value) => {
                    param_types.push(param_value);
                }
                Err(e) => {
                    param_errs.push(e);
                }
            };
        }
    } else if !symbol.params.is_empty() {
        param_errs.push(
            AnalyzeError::new(
                ErrorKind::UnexpectedParams,
                "unexpected generic parameters",
                symbol,
            )
            .with_detail(
                format_code!("{} does not accept generic parameters.", type_display).as_str(),
            ),
        );
    }

    let result = match param_errs.is_empty() {
        true => Ok(param_types),
        false => Err(()),
    };

    for err in param_errs {
        ctx.insert_err(err);
    }

    result
}

/// Analyzed a passed parameter value and checks that it matches the expected
/// parameter constraints.
fn analyze_param(
    ctx: &mut ProgramContext,
    passed_type: Type,
    expected_param: AParam,
    type_display: &String,
) -> AnalyzeResult<TypeKey> {
    let param_type_key = ctx.resolve_type(&passed_type);
    let passed_param_type = ctx.must_get_type(param_type_key);

    // Skip further validation if the param value already failed analysis.
    if passed_param_type.is_unknown() {
        return Ok(param_type_key);
    }

    // Make sure the type passed as the parameter is not a spec.
    if passed_param_type.is_spec() {
        return Err(AnalyzeError::new(
            ErrorKind::MismatchedTypes,
            "expected concrete or generic type, but found spec",
            &passed_type,
        )
        .with_detail(
            format_code!(
                "Expected a concrete or generic type in place of parameter {} on \
                {}, but found spec {}.",
                expected_param.name,
                type_display,
                passed_param_type.to_spec_type().name,
            )
            .as_str(),
        ));
    }

    // Make sure that the type passed as the parameter value implements
    // the required specs.
    let missing_spec_type_keys =
        ctx.get_missing_spec_impls(param_type_key, expected_param.generic_type_key);
    let missing_spec_names: Vec<String> = missing_spec_type_keys
        .into_iter()
        .map(|tk| ctx.display_type_for_key(tk))
        .collect();
    if !missing_spec_names.is_empty() {
        let param_type_display = ctx.display_type_for_key(param_type_key);
        return Err(AnalyzeError::new(
            ErrorKind::SpecNotSatisfied,
            format_code!("type {} violates parameter constraints", param_type_display).as_str(),
            &passed_type,
        )
        .with_detail(
            format!(
                "Type {} does not implement the following specs required \
                by parameter {} on {}: {}",
                format_code!(param_type_display),
                format_code!(expected_param.name),
                format_code!(type_display),
                format_code_vec(&missing_spec_names, ", ")
            )
            .as_str(),
        ));
    }

    Ok(param_type_key)
}
