use crate::analyzer::closure::analyze_closure;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::expr::analyze_expr;
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::AnalyzeResult;
use crate::parser::closure::Closure;
use crate::parser::func::Function;
use crate::parser::func_call::FunctionCall;
use crate::parser::func_sig::FunctionSignature;
use crate::parser::r#type::Type;

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
    analyze_closure(ctx, &func.body)?;

    // Add the function to the program context so we can reference it later.
    ctx.add_fn(func.clone());

    Ok(())
}

pub fn analyze_fn_call(
    ctx: &ProgramContext,
    fn_call: &FunctionCall,
) -> AnalyzeResult<Option<Type>> {
    // Make sure the function exists, either as a fully analyzed function or an external function
    // signature.
    let fn_sig = match ctx.get_extern_fn(fn_call.fn_name.as_str()) {
        Some(sig) => sig,
        None => match ctx.get_fn(fn_call.fn_name.as_str()) {
            Some(decl) => &decl.signature,
            None => {
                return Err(AnalyzeError::new(
                    ErrorKind::FunctionNotDefined,
                    format!("Function {} does not exist", fn_call.fn_name).as_str(),
                ));
            }
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
    for (passed, defined) in fn_call.args.iter().zip(&fn_sig.args) {
        let passed_type = analyze_expr(ctx, passed)?;
        if passed_type != defined.typ {
            return Err(AnalyzeError::new(
                ErrorKind::IncompatibleTypes,
                format!(
                    r#"Argument {} of function {} has type {}, but a value of type {} was \
                    provided"#,
                    defined.name, fn_sig.name, defined.typ, passed_type
                )
                .as_str(),
            ));
        }
    }

    Ok(fn_sig.return_type.clone())
}
