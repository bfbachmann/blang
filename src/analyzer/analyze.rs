use std::collections::HashMap;

use colored::Colorize;

use crate::analyzer::ast::func::{analyze_fn_sig, AFnSig};
use crate::analyzer::ast::source::ASource;
use crate::analyzer::ast::spec::ASpec;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::move_check::MoveChecker;
use crate::analyzer::prog_context::ProgramContext;

use crate::analyzer::type_containment::{check_enum_containment, check_struct_containment};
use crate::analyzer::type_store::TypeStore;
use crate::analyzer::warn::AnalyzeWarning;
use crate::lexer::pos::Position;

use crate::parser::ast::ext::Extern;
use crate::parser::ast::func::Function;
use crate::parser::ast::r#impl::Impl;
use crate::parser::ast::spec::Spec;
use crate::parser::ast::statement::Statement;
use crate::parser::source::Source;

/// An analyzed source file along with any errors or warnings that occurred during its analysis.
#[derive(Debug)]
pub struct AnalyzedSource {
    pub source: ASource,
    pub errors: Vec<AnalyzeError>,
    pub warnings: Vec<AnalyzeWarning>,
}

impl AnalyzedSource {
    /// Creates a new analyzed source.
    pub fn new(
        source: ASource,
        errors: HashMap<Position, AnalyzeError>,
        warns: HashMap<Position, AnalyzeWarning>,
    ) -> AnalyzedSource {
        // Extract and sort errors and warnings by their location in the source file.
        let mut errors: Vec<(Position, AnalyzeError)> =
            errors.into_iter().map(|(p, e)| (p, e)).collect();
        errors.sort_by(|(pos1, _), (pos2, _)| pos1.cmp(pos2));

        let mut warnings: Vec<(Position, AnalyzeWarning)> =
            warns.into_iter().map(|(p, e)| (p, e)).collect();
        warnings.sort_by(|(pos1, _), (pos2, _)| pos1.cmp(&pos2));

        AnalyzedSource {
            source,
            errors: errors.into_iter().map(|(_, e)| e).collect(),
            warnings: warnings.into_iter().map(|(_, w)| w.clone()).collect(),
        }
    }
}

/// The result of analysis on a set of source files.
#[derive(Debug)]
pub struct ProgramAnalysis {
    pub type_store: TypeStore,
    pub analyzed_sources: Vec<AnalyzedSource>,
}

/// Performs semantic analysis on all the given source files and returns the result of analysis.
pub fn analyze_sources(sources: Vec<Source>) -> ProgramAnalysis {
    let mut ctx = ProgramContext::new();
    let mut source_errors: Vec<HashMap<Position, AnalyzeError>> = vec![];
    let mut source_warns: Vec<HashMap<Position, AnalyzeWarning>> = vec![];

    // First pass: define types and functions in the program without analyzing them yet.
    for source in &sources {
        define_types(&mut ctx, source);
        define_fns(&mut ctx, source);
        define_consts(&mut ctx, source);

        // Take all warnings and errors from the program context, replacing them with empty maps.
        source_errors.push(std::mem::take(&mut ctx.errors));
        source_warns.push(std::mem::take(&mut ctx.warnings));
    }

    // Second pass: fully analyze all program statements.
    let mut analyzed_sources = vec![];
    for (i, source) in sources.iter().enumerate() {
        let analyzed_source = ASource::from(&mut ctx, source);

        // Perform move checks and add any errors to our list of errors only if semantic analysis
        // passed.
        if ctx.errors().is_empty() {
            let errors = MoveChecker::check_prog(&analyzed_source, ctx.type_store());
            for err in errors {
                ctx.insert_err(err);
            }
        }

        analyzed_sources.push(analyzed_source);

        // Take all warnings and errors from the program context, replacing them with empty maps.
        source_errors[i].extend(std::mem::take(&mut ctx.errors));
        source_warns[i].extend(std::mem::take(&mut ctx.warnings));
    }

    let mut results: Vec<AnalyzedSource> = vec![];
    for source in analyzed_sources {
        let errors = source_errors.remove(0);
        let warns = source_warns.remove(0);

        results.push(AnalyzedSource::new(source, errors, warns));
    }

    ProgramAnalysis {
        type_store: ctx.type_store,
        analyzed_sources: results,
    }
}

/// Defines top-level types and specs in the program context without deeply analyzing their fields,
/// so they can be referenced later. This will simply check for type name collisions and
/// containment cycles. We do this before fully analyzing types to prevent infinite recursion.
fn define_types(ctx: &mut ProgramContext, source: &Source) {
    // First pass: Define all types without analyzing their fields. In this pass, we will only
    // check that there are no type name collisions.
    for statement in &source.statements {
        match statement {
            Statement::StructDeclaration(struct_type) => {
                ctx.try_insert_unchecked_struct_type(struct_type.clone());
            }

            Statement::EnumDeclaration(enum_type) => {
                ctx.try_insert_unchecked_enum_type(enum_type.clone());
            }

            Statement::SpecDeclaration(spec) => ctx.try_insert_unchecked_spec(spec.clone()),

            _ => {}
        }
    }

    // Second pass: Check for type containment cycles.
    let mut results = vec![];
    {
        let extern_structs = ctx.unchecked_struct_types();
        for struct_type in extern_structs {
            let result = check_struct_containment(ctx, struct_type, &mut vec![]);
            results.push((result, struct_type.name.clone()));
        }

        let extern_enums = ctx.unchecked_enum_types();
        for enum_type in extern_enums {
            let result = check_enum_containment(ctx, enum_type, &mut vec![]);
            results.push((result, enum_type.name.clone()));
        }
    }

    // Remove types that have illegal containment cycles from the program context and add them as
    // invalid types instead. We do this so we can safely continue with semantic analysis without
    // having to worry about stack overflows during recursive type resolution.
    for (result, type_name) in results {
        if ctx.consume_error(result).is_none() {
            ctx.remove_unchecked_struct_type(type_name.as_str());
            ctx.remove_unchecked_enum_type(type_name.as_str());
            ctx.insert_invalid_type_name(type_name.as_str());
        }
    }
}

/// Stores un-analyzed constant declarations in the program context
/// so they can be fetched and analyzed later when they're used.
fn define_consts(ctx: &mut ProgramContext, source: &Source) {
    for statement in &source.statements {
        if let Statement::Consts(const_block) = statement {
            for const_decl in &const_block.consts {
                ctx.try_insert_unchecked_const(const_decl.clone());
            }
        }
    }
}

/// Analyzes all top-level function signatures (this includes those inside specs) and defines them
/// in the program context so they can be referenced later. This will not perform any analysis of
/// function bodies.
fn define_fns(ctx: &mut ProgramContext, source: &Source) {
    for statement in &source.statements {
        match statement {
            Statement::FunctionDeclaration(func) => {
                define_fn(ctx, func);
            }

            Statement::ExternFns(ext) => {
                define_extern_fns(ctx, ext);
            }

            Statement::Impl(impl_) => {
                define_impl(ctx, impl_);
            }

            Statement::SpecDeclaration(spec) => {
                define_spec(ctx, spec);
            }

            _ => {}
        };
    }
}

fn define_fn(ctx: &mut ProgramContext, func: &Function) {
    analyze_fn_sig(ctx, &func.signature);

    if func.signature.name == "main" {
        // Make sure main has no args or return.
        if func.signature.args.len() != 0 {
            ctx.insert_err(AnalyzeError::new(
                ErrorKind::InvalidMain,
                format_code!("function {} cannot have arguments", "main").as_str(),
                &func.signature,
            ));
        }

        if func.signature.maybe_ret_type.is_some() {
            ctx.insert_err(AnalyzeError::new(
                ErrorKind::InvalidMain,
                format_code!("function {} cannot have a return type", "main").as_str(),
                &func.signature,
            ));
        }
    }
}

fn define_extern_fns(ctx: &mut ProgramContext, ext: &Extern) {
    for sig in &ext.fn_sigs {
        if sig.tmpl_params.is_some() {
            ctx.insert_err(AnalyzeError::new(
                ErrorKind::InvalidExtern,
                "external functions cannot be templated",
                sig,
            ));
            continue;
        }

        analyze_fn_sig(ctx, sig);
    }
}

fn define_impl(ctx: &mut ProgramContext, impl_: &Impl) {
    // Set the current impl type key on the program context so we can access it when
    // resolving type `This`.
    let impl_type_key = ctx.resolve_type(&impl_.typ);
    ctx.set_cur_self_type_key(Some(impl_type_key));

    // Analyze each member function signature and record it as a member of this type
    // in the program context.
    for member_fn in &impl_.member_fns {
        let fn_sig = AFnSig::from(ctx, &member_fn.signature);

        // Make sure this isn't a duplicate member function.
        if ctx
            .get_member_fn(impl_type_key, fn_sig.name.as_str())
            .is_some()
        {
            ctx.insert_err(AnalyzeError::new(
                ErrorKind::DuplicateFunction,
                format_code!(
                    "function {} was already defined for type {}",
                    member_fn.signature.name,
                    ctx.display_type_for_key(impl_type_key),
                )
                .as_str(),
                &member_fn.signature,
            ));
        } else {
            ctx.insert_member_fn(impl_type_key, fn_sig);
        }
    }

    ctx.set_cur_self_type_key(None);
}

fn define_spec(ctx: &mut ProgramContext, spec: &Spec) {
    // Make sure this spec name is not a duplicate.
    if ctx.get_spec(spec.name.as_str()).is_some() {
        // Record the error and return a placeholder value.
        ctx.insert_err(AnalyzeError::new(
            ErrorKind::DuplicateSpec,
            format_code!("another spec named {} already exists", spec.name).as_str(),
            spec,
        ));

        return;
    }

    // Analyze the spec and add it to the program context so we can retrieve and render
    // it later.
    let a_spec = ASpec::from(ctx, spec);
    ctx.insert_spec(a_spec);
}
