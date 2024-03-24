use std::fmt;
use std::fmt::Formatter;

use crate::analyzer::ast::closure::{analyze_break, analyze_continue, AClosure};
use crate::analyzer::ast::cond::ACond;
use crate::analyzer::ast::fn_call::AFnCall;
use crate::analyzer::ast::func::{AFn, AFnSig};
use crate::analyzer::ast::r#const::AConst;
use crate::analyzer::ast::r#enum::AEnumType;
use crate::analyzer::ast::r#impl::AImpl;
use crate::analyzer::ast::r#loop::ALoop;
use crate::analyzer::ast::r#struct::AStructType;
use crate::analyzer::ast::ret::ARet;
use crate::analyzer::ast::var_assign::AVarAssign;
use crate::analyzer::ast::var_dec::AVarDecl;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::scope::ScopeKind;
use crate::parser::ast::statement::Statement;

/// Represents a semantically valid and type-rich statement.
#[derive(PartialEq, Debug, Clone)]
pub enum AStatement {
    VariableDeclaration(AVarDecl),
    VariableAssignment(AVarAssign),
    FunctionDeclaration(AFn),
    Closure(AClosure),
    FunctionCall(AFnCall),
    Conditional(ACond),
    Loop(Box<ALoop>),
    Break,
    Continue,
    Return(ARet),
    StructTypeDeclaration(AStructType),
    EnumTypeDeclaration(AEnumType),
    /// A set of external function declarations.
    ExternFns(Vec<AFnSig>),
    Consts(Vec<AConst>),
    Impl(AImpl),
}

impl fmt::Display for AStatement {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            AStatement::VariableDeclaration(v) => write!(f, "{}", v),
            AStatement::VariableAssignment(v) => write!(f, "{}", v),
            AStatement::FunctionDeclaration(v) => write!(f, "{}", v),
            AStatement::Closure(v) => write!(f, "{}", v),
            AStatement::FunctionCall(v) => write!(f, "{}", v),
            AStatement::Conditional(v) => write!(f, "{}", v),
            AStatement::Loop(v) => write!(f, "{}", v),
            AStatement::Break => write!(f, "break"),
            AStatement::Continue => write!(f, "continue"),
            AStatement::Return(v) => write!(f, "{}", v),
            AStatement::StructTypeDeclaration(s) => write!(f, "{}", s),
            AStatement::EnumTypeDeclaration(e) => write!(f, "{}", e),
            AStatement::ExternFns(e) => {
                if e.len() == 1 {
                    write!(f, "extern {}", e.first().unwrap())
                } else {
                    write!(f, "extern {{ <{} function signatures> }}", e.len())
                }
            }
            AStatement::Consts(consts) => {
                if consts.len() == 1 {
                    write!(f, "const {}", consts.first().unwrap())
                } else {
                    write!(f, "const {{ <{} constant declarations> }}", consts.len())
                }
            }
            AStatement::Impl(impl_) => {
                write!(
                    f,
                    "impl {} {{ <{} member functions> }}",
                    impl_.type_key,
                    impl_.member_fns.len()
                )
            }
        }
    }
}

impl AStatement {
    /// Performs semantic analysis on the given statement and returns a type-rich version of it.
    pub fn from(ctx: &mut ProgramContext, statement: &Statement) -> Self {
        match statement {
            Statement::VariableDeclaration(var_decl) => {
                AStatement::VariableDeclaration(AVarDecl::from(ctx, var_decl))
            }

            Statement::VariableAssignment(var_assign) => {
                AStatement::VariableAssignment(AVarAssign::from(ctx, var_assign))
            }

            Statement::FunctionDeclaration(fn_decl) => {
                // Analyze the function and add it to the program context so we can reference it
                // later.
                let a_fn = AFn::from(ctx, fn_decl);
                ctx.insert_fn(a_fn.clone());
                AStatement::FunctionDeclaration(a_fn)
            }

            Statement::Closure(closure) => AStatement::Closure(AClosure::from(
                ctx,
                closure,
                ScopeKind::InlineClosure,
                vec![],
                None,
            )),

            Statement::FunctionCall(call) => AStatement::FunctionCall(AFnCall::from(ctx, call)),

            Statement::Conditional(cond) => AStatement::Conditional(ACond::from(ctx, cond)),

            Statement::Loop(loop_) => AStatement::Loop(Box::new(ALoop::from(ctx, &loop_))),

            Statement::Break(br) => {
                analyze_break(ctx, &br);
                AStatement::Break
            }

            Statement::Continue(cont) => {
                analyze_continue(ctx, &cont);
                AStatement::Continue
            }

            Statement::Return(ret) => {
                let a_ret = ARet::from(ctx, ret);
                AStatement::Return(a_ret)
            }

            Statement::StructDeclaration(s) => {
                AStatement::StructTypeDeclaration(AStructType::from(ctx, &s, false))
            }

            Statement::EnumDeclaration(e) => {
                AStatement::EnumTypeDeclaration(AEnumType::from(ctx, &e))
            }

            Statement::Impl(impl_) => AStatement::Impl(AImpl::from(ctx, &impl_)),

            Statement::ExternFns(ext) => {
                // Make sure we are not already inside a function. Extern functions cannot be
                // defined within other functions.
                if ctx.is_in_fn() {
                    ctx.insert_err(AnalyzeError::new(
                        ErrorKind::InvalidStatement,
                        "cannot declare external functions inside other functions",
                        ext,
                    ));
                }

                // Analyze all the function signatures in the `extern` block.
                let mut a_fn_sigs = vec![];
                for ext_fn_sig in &ext.fn_sigs {
                    a_fn_sigs.push(AFnSig::from(ctx, ext_fn_sig));
                }

                AStatement::ExternFns(a_fn_sigs)
            }

            Statement::Consts(const_block) => {
                // Analyze all the constant declarations.
                let mut consts = vec![];
                for const_decl in &const_block.consts {
                    consts.push(AConst::from(ctx, const_decl));
                }

                AStatement::Consts(consts)
            }

            Statement::Use(_) => {
                // This should never happen because `use` statements are handled by the parser.
                unreachable!()
            }

            Statement::SpecDeclaration(_) => {
                // This should never happen as specs should be skipped – they're analyzed before
                // we start analyzing other program statements.
                unreachable!()
            }
        }
    }

    /// Returns true if this statement is a templated statement (and therefore should not actually
    /// be included in the AST that results from semantic analysis).
    pub fn is_templated(&self) -> bool {
        match self {
            AStatement::FunctionDeclaration(func) => func.signature.is_templated(),
            _ => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::analyzer::ast::r#struct::{AField, AStructType};
    use crate::analyzer::ast::statement::AStatement;
    use crate::analyzer::error::{AnalyzeError, ErrorKind};
    use crate::analyzer::prog_context::ProgramContext;
    use crate::analyzer::warn::AnalyzeWarning;
    use crate::lexer::lex::lex;
    use crate::lexer::stream::Stream;
    use crate::parser::ast::statement::Statement;

    fn analyze_statement(raw: &str, ctx: &mut ProgramContext) -> AStatement {
        let tokens = lex(raw).expect("should not error");
        let statement = Statement::from(&mut Stream::from(tokens)).expect("should not error");
        AStatement::from(ctx, &statement)
    }

    #[test]
    fn simple_return() {
        let raw = r#"
            fn thing(): bool {
                let b = true
                return b
            }
        "#;
        let mut ctx = ProgramContext::new_with_host_ptr_width();
        analyze_statement(raw, &mut ctx);
        assert!(ctx.errors().is_empty());
    }

    #[test]
    fn return_in_conditional() {
        let raw = r#"
            fn thing(a: i64): bool {
                let mut a = a * 2
                if a > 10 {
                    return true
                } elsif a > 5 {
                    return false
                } else {
                    return true
                }
            }
        "#;
        let mut ctx = ProgramContext::new_with_host_ptr_width();
        analyze_statement(raw, &mut ctx);
        assert!(ctx.errors().is_empty());
    }

    #[test]
    fn missing_return_in_conditional() {
        let raw = r#"
            fn thing(a: i64): bool {
                let mut mut_a = a * 2
                if mut_a > 10 {
                    return true
                } elsif mut_a > 5 {
                    return false
                } else {
                    mut_a = 2
                } 
            }
        "#;
        let mut ctx = ProgramContext::new_with_host_ptr_width();
        analyze_statement(raw, &mut ctx);
        assert!(matches!(
            ctx.errors()
                .values()
                .collect::<Vec<&AnalyzeError>>()
                .get(0)
                .unwrap(),
            AnalyzeError {
                kind: ErrorKind::MissingReturn,
                ..
            }
        ));
    }

    #[test]
    fn non_exhaustive_conditional() {
        let raw = r#"
            fn thing(a: i64): bool {
                let mut mut_a = a * 2
                if mut_a > 10 {
                    return true
                } elsif mut_a > 5 {
                    return false
                }
            }
        "#;
        let mut ctx = ProgramContext::new_with_host_ptr_width();
        analyze_statement(raw, &mut ctx);
        assert!(matches!(
            ctx.errors()
                .values()
                .collect::<Vec<&AnalyzeError>>()
                .get(0)
                .unwrap(),
            AnalyzeError {
                kind: ErrorKind::MissingReturn,
                ..
            }
        ))
    }

    #[test]
    fn conditional_with_loop() {
        let raw = r#"
            fn thing(a: i64): bool {
                let mut mut_a = a * 2
                if mut_a > 10 {
                    return true
                } elsif mut_a > 5 {
                    return false
                } else {
                    loop {
                        mut_a = mut_a * 2
                        if mut_a > 50 {
                            return true
                        }
                    }
                }
            }
        "#;
        let mut ctx = ProgramContext::new_with_host_ptr_width();
        analyze_statement(raw, &mut ctx);
        assert!(ctx.errors().is_empty());
    }

    #[test]
    fn conditional_with_closure() {
        let raw = r#"
            fn thing(a: i64): bool {
                let mut mut_a = a * 2
                if a > 10 {
                    return true
                } else {
                    {
                        if mut_a > 50 {
                            return true
                        }
                    }
                }
            }
        "#;
        let mut ctx = ProgramContext::new_with_host_ptr_width();
        analyze_statement(raw, &mut ctx);
        assert!(matches!(
            ctx.errors()
                .values()
                .collect::<Vec<&AnalyzeError>>()
                .get(0)
                .unwrap(),
            AnalyzeError {
                kind: ErrorKind::MissingReturn,
                ..
            }
        ));
    }

    #[test]
    fn loop_with_return() {
        let raw = r#"
            fn thing(a: i64): bool {
                loop {
                    return true
                }
            }
        "#;
        let mut ctx = ProgramContext::new_with_host_ptr_width();
        analyze_statement(raw, &mut ctx);
        assert!(ctx.errors().is_empty());
    }

    #[test]
    fn loop_with_return_in_cond() {
        let raw = r#"
            fn thing(a: i64): bool {
                loop {
                    if a == 1 {
                        return true
                    }
                }
            }
        "#;
        let mut ctx = ProgramContext::new_with_host_ptr_width();
        analyze_statement(raw, &mut ctx);
        assert!(ctx.errors().is_empty());
    }

    #[test]
    fn loop_with_return_in_closure() {
        let raw = r#"
            fn thing(a: i64): bool {
                loop {
                    loop {
                        if a == 1 {
                            return true
                        }
                    }
                }
            }
        "#;
        let mut ctx = ProgramContext::new_with_host_ptr_width();
        analyze_statement(raw, &mut ctx);
        assert!(ctx.errors().is_empty());
    }

    #[test]
    fn loop_with_continue() {
        let raw = r#"
            fn thing(a: i64): bool {
                let mut mut_a = a
                loop {
                    mut_a = mut_a - 1
                    if mut_a == 1 {
                        continue
                    }
                    return true
                }
            }
        "#;
        let mut ctx = ProgramContext::new_with_host_ptr_width();
        analyze_statement(raw, &mut ctx);
        assert!(ctx.errors().is_empty());
    }

    #[test]
    fn statements_following_return() {
        let raw = r#"
            fn thing(a: i64): bool {
                return true
                a = 2
                return false
            }
        "#;
        let mut ctx = ProgramContext::new_with_host_ptr_width();
        analyze_statement(raw, &mut ctx);
        assert!(ctx.errors().is_empty());
        assert!(matches!(
            ctx.warnings()
                .values()
                .collect::<Vec<&AnalyzeWarning>>()
                .remove(0),
            AnalyzeWarning { .. }
        ));
    }

    #[test]
    fn return_outside_fn() {
        let raw = "return 1";
        let mut ctx = ProgramContext::new_with_host_ptr_width();
        analyze_statement(raw, &mut ctx);
        assert!(matches!(
            ctx.errors()
                .values()
                .collect::<Vec<&AnalyzeError>>()
                .get(0)
                .unwrap(),
            AnalyzeError {
                kind: ErrorKind::UnexpectedReturn,
                ..
            }
        ));
    }

    #[test]
    fn loop_with_return_and_break() {
        let raw = r#"
            fn thing(a: i64): bool {
                loop {
                    loop {
                        if a == 1 {
                            return true
                        }
                    }
                    break
                }
            }
        "#;
        let mut ctx = ProgramContext::new_with_host_ptr_width();
        analyze_statement(raw, &mut ctx);
        assert!(matches!(
            ctx.errors()
                .values()
                .collect::<Vec<&AnalyzeError>>()
                .get(0)
                .unwrap(),
            AnalyzeError {
                kind: ErrorKind::MissingReturn,
                ..
            }
        ));
    }

    #[test]
    fn struct_decl() {
        let raw = r#"
            struct MyStruct {
                counter: i64,
                is_even: bool,
                message: str,
            }
        "#;
        let mut ctx = ProgramContext::new_with_host_ptr_width();
        let result = analyze_statement(raw, &mut ctx);
        assert!(ctx.errors().is_empty());

        // Make sure the struct fields are all present and in the right order (from largest field
        // to smallest with ties broken by lexicographical order).
        assert_eq!(
            result,
            AStatement::StructTypeDeclaration(AStructType {
                name: "MyStruct".to_string(),
                fields: vec![
                    AField {
                        name: "message".to_string(),
                        type_key: ctx.str_type_key(),
                    },
                    AField {
                        name: "counter".to_string(),
                        type_key: ctx.i64_type_key(),
                    },
                    AField {
                        name: "is_even".to_string(),
                        type_key: ctx.bool_type_key(),
                    },
                ],
            })
        )
    }
}
