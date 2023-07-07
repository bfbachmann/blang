use crate::analyzer::closure::analyze_closure;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::expr::analyze_expr;
use crate::analyzer::prog_context::{ProgramContext, ScopeKind};
use crate::analyzer::AnalyzeResult;
use crate::parser::expr::Expression;
use crate::parser::func::Function;
use crate::parser::func_call::FunctionCall;
use crate::parser::func_sig::FunctionSignature;
use crate::parser::r#type::Type;
use crate::parser::var_dec::VariableDeclaration;

pub fn analyze_fn_sig(ctx: &mut ProgramContext, sig: &FunctionSignature) -> AnalyzeResult<()> {
    // Add the function to the program context with an empty body, making sure it doesn't already
    // exist. We'll replace the function body when we analyze it later.
    if let Some(_) = ctx.add_extern_fn(sig.clone()) {
        return Err(AnalyzeError::new(
            ErrorKind::FunctionAlreadyDefined,
            format!("Function {} was already defined in this scope", sig.name).as_str(),
        ));
    }

    Ok(())
}

pub fn analyze_fn_decl(ctx: &mut ProgramContext, func: &Function) -> AnalyzeResult<()> {
    // Make sure the function is not already defined.
    if let Some(_) = ctx.get_fn(func.signature.name.as_str()) {
        return Err(AnalyzeError::new(
            ErrorKind::FunctionAlreadyDefined,
            format!(
                "Function {} was already defined in this scope",
                func.signature.name
            )
            .as_str(),
        ));
    }

    // Analyze the function body.
    analyze_closure(
        ctx,
        &func.body,
        ScopeKind::FnBody,
        func.signature.args.clone(),
        func.signature.return_type.clone(),
    )?;

    // Add the function to the program context so we can reference it later.
    ctx.add_fn(func.clone());

    Ok(())
}

pub fn analyze_fn_call(
    ctx: &mut ProgramContext,
    fn_call: &FunctionCall,
) -> AnalyzeResult<Option<Type>> {
    // Collect up argument types.
    let mut found_arg_types = vec![];
    for arg in &fn_call.args {
        let arg_type = analyze_expr(ctx, arg)?;
        found_arg_types.push(arg_type);
    }

    // Make sure the function exists, either as a fully analyzed function, an external function
    // signature, or a variable.
    let fn_sig = match ctx.get_extern_fn(fn_call.fn_name.as_str()) {
        Some(sig) => sig,
        None => match ctx.get_fn(fn_call.fn_name.as_str()) {
            Some(decl) => &decl.signature,
            None => match ctx.get_var(fn_call.fn_name.as_str()) {
                Some(&VariableDeclaration {
                    typ: Type::Function(ref func),
                    ..
                }) => func,
                _ => {
                    return Err(AnalyzeError::new(
                        ErrorKind::FunctionNotDefined,
                        format!("Function {} does not exist", fn_call.fn_name).as_str(),
                    ));
                }
            },
        },
    };

    // Make sure the right number of arguments were passed.
    if fn_call.args.len() != fn_sig.args.len() {
        return Err(AnalyzeError::new(
            ErrorKind::WrongNumberOfArgs,
            format!(
                "Function {} takes {} args, but {} were provided",
                fn_sig.name,
                fn_sig.args.len(),
                fn_call.args.len()
            )
            .as_str(),
        ));
    }

    // Make sure the arguments are of the right types.
    for (passed_type, defined) in found_arg_types.iter().zip(&fn_sig.args) {
        if passed_type != &defined.typ {
            return Err(AnalyzeError::new(
                ErrorKind::IncompatibleTypes,
                format!(
                    r#"Argument {} of function {} has type {}, but a value of type {} was \
                    provided"#,
                    &defined.name, &fn_sig.name, &defined.typ, &passed_type
                )
                .as_str(),
            ));
        }
    }

    Ok(fn_sig.return_type.clone())
}

pub fn analyze_return(
    ctx: &mut ProgramContext,
    expr: &Option<Expression>,
) -> AnalyzeResult<Option<Type>> {
    // Make sure we are inside a function body.
    if !ctx.is_in_fn() {
        return Err(AnalyzeError::new(
            ErrorKind::UnexpectedReturn,
            "Cannot return from outside function body",
        ));
    }

    match expr {
        Some(expr) => {
            // We're returning a value. Make sure the value is of the expected type.
            let expr_type = analyze_expr(ctx, expr)?;
            match ctx.return_type() {
                Some(expected) => {
                    if expected != &expr_type {
                        Err(AnalyzeError::new(
                            ErrorKind::IncompatibleTypes,
                            format!(
                                "Cannot return value of type {} from function with return type {}",
                                &expr_type, &expected
                            )
                            .as_str(),
                        ))
                    } else {
                        Ok(Some(expr_type))
                    }
                }
                None => Err(AnalyzeError::new(
                    ErrorKind::IncompatibleTypes,
                    format!(
                        "Cannot return value of type {} from function with no return type",
                        expr_type
                    )
                    .as_str(),
                )),
            }
        }
        None => {
            // This is an empty return. Make sure we're not expecting a return type.
            match ctx.return_type() {
                Some(expected) => Err(AnalyzeError::new(
                    ErrorKind::IncompatibleTypes,
                    format!(
                        "Expected return value of type {}, but found empty return",
                        expected
                    )
                    .as_str(),
                )),
                None => Ok(None),
            }
        }
    }
}
