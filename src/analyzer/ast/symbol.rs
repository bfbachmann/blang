use crate::analyzer::error::{
    err_expected_expr_found_type, err_not_pub, err_undef_foreign_symbol, err_undef_local_symbol,
    err_undef_mod_alias, err_unresolved_params,
};
use crate::analyzer::ident::{IdentKind, Usage};
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::type_store::TypeKey;
use crate::lexer::pos::Span;
use crate::locatable_impl;
use crate::parser::ast::pointer::PointerType;
use crate::parser::ast::r#type::Type;
use crate::parser::ast::symbol::Symbol;
use crate::parser::ast::unresolved::UnresolvedType;
use crate::parser::ModID;
use crate::Locatable;
use std::fmt::{Display, Formatter};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SymbolKind {
    Const,
    Static,
    Type,
    Variable,
    Fn,
}

/// A symbol that can represent a variable, variable access, function, type, or constant.
#[derive(Debug, Clone)]
pub struct ASymbol {
    pub name: String,
    /// The type key of the symbol.
    pub type_key: TypeKey,
    pub maybe_param_tks: Option<Vec<TypeKey>>,
    pub kind: SymbolKind,
    /// The ID of the module from whence the symbol comes. Will be `None` for primitives.
    pub maybe_mod_id: Option<ModID>,
    pub span: Span,
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
    /// Creates a new symbol with default span.
    pub fn new_with_default_span(name: &str, type_key: TypeKey) -> Self {
        ASymbol {
            name: name.to_string(),
            type_key,
            maybe_param_tks: None,
            kind: SymbolKind::Const,
            maybe_mod_id: None,
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
        allow_type: bool,
        allow_polymorph: bool,
    ) -> Self {
        let placeholder =
            ASymbol::new_with_default_span(symbol.name.value.as_str(), ctx.unknown_type_key());

        // Check for intrinsic symbols like `null`.
        if let Some(intrinsic) = maybe_get_intrinsic(ctx, symbol) {
            return intrinsic;
        }

        let mut name = symbol.name.value.clone();

        // Locate the identifier.
        let ident = match &symbol.maybe_mod_name {
            Some(mod_name) => {
                let mod_id = match ctx.get_mod_alias(mod_name) {
                    Some(alias) => alias.target_mod_id,
                    None => {
                        ctx.insert_err(err_undef_mod_alias(&mod_name.value, mod_name.span));
                        return placeholder;
                    }
                };

                match ctx.get_foreign_ident(mod_id, &symbol.name.value) {
                    Some(ident) => ident,
                    None => {
                        ctx.insert_err(err_undef_foreign_symbol(
                            &symbol.name.value,
                            &mod_name.value,
                            symbol.name.span,
                        ));
                        return placeholder;
                    }
                }
            }

            None => match ctx.get_local_ident(&symbol.name.value, Some(Usage::Read)) {
                Some(ident) => ident,
                None => {
                    ctx.insert_err(err_undef_local_symbol(&symbol.name.value, symbol.span));
                    return placeholder;
                }
            },
        };

        let (type_key, is_pub, kind, maybe_mod_id) = match ident.kind.clone() {
            IdentKind::Variable { type_key, .. } => (
                type_key,
                false,
                SymbolKind::Variable,
                Some(ctx.cur_mod_id()),
            ),

            IdentKind::Type {
                is_pub,
                type_key,
                mod_id,
            } => {
                if !allow_type {
                    let err = err_expected_expr_found_type(ctx, type_key, symbol.span);
                    ctx.insert_err(err);
                    return placeholder;
                }

                (type_key, is_pub, SymbolKind::Type, mod_id)
            }

            IdentKind::Fn {
                is_pub,
                type_key,
                mod_id,
            } => {
                let fn_sig = ctx.get_type(type_key).to_fn_sig();
                name = fn_sig.name.clone();
                (type_key, is_pub, SymbolKind::Fn, mod_id)
            }

            IdentKind::ExternFn {
                is_pub,
                type_key,
                mod_id,
            } => {
                let fn_sig = ctx.get_type(type_key).to_fn_sig();
                name = fn_sig.name.clone();
                (type_key, is_pub, SymbolKind::Fn, mod_id)
            }

            IdentKind::Const {
                is_pub,
                value,
                mod_id,
            } => (value.type_key, is_pub, SymbolKind::Const, mod_id),

            IdentKind::Static {
                is_pub,
                value,
                mod_id,
            } => (value.type_key, is_pub, SymbolKind::Static, mod_id),

            other => panic!("unexpected identifier kind: {:?}", other),
        };

        // Record an error if this symbol refers to a non-public foreign type.
        if maybe_mod_id.is_some_and(|id| id != ctx.cur_mod_id()) && !is_pub {
            ctx.insert_err(err_not_pub(&symbol.name.value, symbol.span));
        }

        // Analyze any generic parameters on this symbol and use them to monomorphize
        // the generic value, if it is generic. We don't do this if it's a type
        // because it would have already been done during type resolution.
        let (mono_type_key, maybe_param_tks) = match symbol.params.is_empty() {
            false => {
                if kind == SymbolKind::Const {
                    let mono_tk = ctx.resolve_type(&Type::Unresolved(UnresolvedType::from_symbol(
                        symbol.clone(),
                    )));
                    (mono_tk, None)
                } else {
                    // We're only including parameter type keys here so the symbol
                    // resolver in the code generator can figure out which concrete
                    // type this symbol maps to.
                    let mono_tk =
                        ctx.monomorphize_parameterized_type(type_key, &symbol.params, symbol);
                    let param_tks = symbol.params.iter().map(|t| ctx.resolve_type(t)).collect();
                    (mono_tk, Some(param_tks))
                }
            }

            true => {
                // No parameters were provided, so the type had better not be
                // parameterized unless the symbol type is the current `impl` type.
                let poly_type = ctx.get_type(type_key);
                if !ctx.get_cur_self_type_key().is_some_and(|tk| tk == type_key) {
                    match poly_type.params() {
                        Some(params) if !allow_polymorph => {
                            let param_names = params.params.iter().map(|p| &p.name).collect();
                            let err = err_unresolved_params(ctx, symbol, type_key, param_names);
                            ctx.insert_err(err);
                        }

                        _ => {}
                    }
                }

                (type_key, None)
            }
        };

        ASymbol {
            name,
            type_key: mono_type_key,
            maybe_param_tks,
            kind,
            maybe_mod_id,
            span: symbol.span,
        }
    }

    /// Returns true if this symbol represents the `null` intrinsic value.
    pub fn is_null_intrinsic(&self) -> bool {
        self.name == "null" && self.kind == SymbolKind::Const
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
            None => ctx.resolve_type(&Type::Pointer(Box::new(
                PointerType::new_with_default_span(Type::new_unresolved("u8"), true),
            ))),
        };

        ASymbol {
            name: "null".to_string(),
            type_key,
            maybe_param_tks: None,
            kind: SymbolKind::Const,
            maybe_mod_id: None,
            span,
        }
    }
}

/// Tries to locate an intrinsic that matches the given symbol and returns it
/// if one exists.
fn maybe_get_intrinsic(ctx: &mut ProgramContext, symbol: &Symbol) -> Option<ASymbol> {
    // Check for the `null` intrinsic.
    if symbol.maybe_mod_name.is_none() && symbol.name.value == "null" {
        return Some(ASymbol::new_null(ctx, None, symbol.span));
    }

    None
}
