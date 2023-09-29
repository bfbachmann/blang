use core::fmt;
use std::fmt::Formatter;

use crate::analyzer::closure::{analyze_break, analyze_continue, RichClosure};
use crate::analyzer::cond::RichCond;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::func::{RichFn, RichFnCall, RichFnSig, RichRet};
use crate::analyzer::prog_context::{ProgramContext, ScopeKind};
use crate::analyzer::r#const::RichConst;
use crate::analyzer::r#struct::RichStructType;
use crate::analyzer::var_assign::RichVarAssign;
use crate::analyzer::var_dec::RichVarDecl;
use crate::parser::statement::Statement;

/// Represents a semantically valid and type-rich statement.
#[derive(PartialEq, Debug, Clone)]
pub enum RichStatement {
    VariableDeclaration(RichVarDecl),
    VariableAssignment(RichVarAssign),
    FunctionDeclaration(RichFn),
    Closure(RichClosure),
    FunctionCall(RichFnCall),
    Conditional(RichCond),
    Loop(RichClosure),
    Break,
    Continue,
    Return(RichRet),
    StructTypeDeclaration(RichStructType),
    /// A set of external function declarations.
    ExternFns(Vec<RichFnSig>),
    Consts(Vec<RichConst>),
}

impl fmt::Display for RichStatement {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            RichStatement::VariableDeclaration(v) => write!(f, "{}", v),
            RichStatement::VariableAssignment(v) => write!(f, "{}", v),
            RichStatement::FunctionDeclaration(v) => write!(f, "{}", v),
            RichStatement::Closure(v) => write!(f, "{}", v),
            RichStatement::FunctionCall(v) => write!(f, "{}", v),
            RichStatement::Conditional(v) => write!(f, "{}", v),
            RichStatement::Loop(v) => write!(f, "{}", v),
            RichStatement::Break => write!(f, "break"),
            RichStatement::Continue => write!(f, "continue"),
            RichStatement::Return(v) => write!(f, "{}", v),
            RichStatement::StructTypeDeclaration(s) => write!(f, "{}", s),
            RichStatement::ExternFns(e) => {
                if e.len() == 1 {
                    write!(f, "ext {}", e.first().unwrap())
                } else {
                    write!(f, "ext {{ <{} function signatures> }}", e.len())
                }
            }
            RichStatement::Consts(consts) => {
                if consts.len() == 1 {
                    write!(f, "const {}", consts.first().unwrap())
                } else {
                    write!(f, "const {{ <{} constant declarations> }}", consts.len())
                }
            }
        }
    }
}

impl RichStatement {
    /// Performs semantic analysis on the given statement and returns a type-rich version of it.
    pub fn from(ctx: &mut ProgramContext, statement: Statement) -> Self {
        match statement {
            Statement::VariableDeclaration(var_decl) => {
                RichStatement::VariableDeclaration(RichVarDecl::from(ctx, var_decl))
            }

            Statement::VariableAssignment(var_assign) => {
                RichStatement::VariableAssignment(RichVarAssign::from(ctx, var_assign))
            }

            Statement::FunctionDeclaration(fn_decl) => {
                RichStatement::FunctionDeclaration(RichFn::from(ctx, fn_decl))
            }

            Statement::Closure(closure) => RichStatement::Closure(RichClosure::from(
                ctx,
                closure,
                ScopeKind::Inline,
                vec![],
                None,
            )),

            Statement::FunctionCall(call) => {
                RichStatement::FunctionCall(RichFnCall::from(ctx, call))
            }

            Statement::Conditional(cond) => RichStatement::Conditional(RichCond::from(ctx, cond)),

            Statement::Loop(loop_) => RichStatement::Loop(RichClosure::from(
                ctx,
                loop_.closure,
                ScopeKind::Loop,
                vec![],
                None,
            )),

            Statement::Break(br) => {
                analyze_break(ctx, &br);
                RichStatement::Break
            }

            Statement::Continue(cont) => {
                analyze_continue(ctx, &cont);
                RichStatement::Continue
            }

            Statement::Return(ret) => {
                let rich_ret = RichRet::from(ctx, ret);
                RichStatement::Return(rich_ret)
            }

            Statement::StructDeclaration(s) => {
                RichStatement::StructTypeDeclaration(RichStructType::from(ctx, &s, false))
            }

            Statement::ExternFns(ext) => {
                // Make sure we are not already inside a function. Extern functions cannot be
                // defined within other functions.
                if ctx.is_in_fn() {
                    ctx.add_err(AnalyzeError::new(
                        ErrorKind::InvalidStatement,
                        "cannot declare external functions inside other functions",
                        &ext,
                    ));
                }

                // Analyze all the function signatures in the `ext` block.
                let mut rich_fn_sigs = vec![];
                for ext_fn_sig in &ext.fn_sigs {
                    rich_fn_sigs.push(RichFnSig::from(ctx, ext_fn_sig));
                }

                RichStatement::ExternFns(rich_fn_sigs)
            }

            Statement::Consts(const_block) => {
                // Make sure this const is not being declared inside a function.
                if ctx.is_in_fn() {
                    ctx.add_err(AnalyzeError::new(
                        ErrorKind::InvalidStatement,
                        "cannot declare constant inside function",
                        &const_block,
                    ));
                }

                // Analyze all the constant declarations.
                let mut consts = vec![];
                for const_decl in &const_block.consts {
                    consts.push(RichConst::from(ctx, const_decl));
                }

                RichStatement::Consts(consts)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::io::{BufRead, Cursor};

    use crate::analyzer::error::AnalyzeError;
    use crate::analyzer::error::ErrorKind;
    use crate::analyzer::prog_context::ProgramContext;
    use crate::analyzer::r#struct::{RichField, RichStructType};
    use crate::analyzer::r#type::TypeId;
    use crate::analyzer::statement::RichStatement;
    use crate::analyzer::warn::AnalyzeWarning;
    use crate::lexer::token::Token;
    use crate::parser::statement::Statement;
    use crate::parser::stream::Stream;

    fn analyze_statement(raw: &str, ctx: &mut ProgramContext) -> RichStatement {
        let tokens = Token::tokenize(Cursor::new(raw).lines()).expect("should not error");
        let statement = Statement::from(&mut Stream::from(tokens)).expect("should not error");
        RichStatement::from(ctx, statement)
    }

    #[test]
    fn simple_return() {
        let raw = r#"
            fn thing() ~ bool {
                let b = true
                return b
            }
        "#;
        let mut ctx = ProgramContext::new();
        analyze_statement(raw, &mut ctx);
        assert!(ctx.errors().is_empty());
    }

    #[test]
    fn return_in_conditional() {
        let raw = r#"
            fn thing(a: i64) ~ bool {
                let mut a = a * 2
                if a > 10 {
                    return true
                } elsif a > 5 {
                    return false
                } else  {
                    return true
                }
            }
        "#;
        let mut ctx = ProgramContext::new();
        analyze_statement(raw, &mut ctx);
        assert!(ctx.errors().is_empty());
    }

    #[test]
    fn missing_return_in_conditional() {
        let raw = r#"
            fn thing(a: i64) ~ bool {
                let mut mut_a = a * 2
                if mut_a > 10 {
                    return true
                } elsif mut_a > 5 {
                    return false
                } else  {
                    mut_a = 2
                }
            }
        "#;
        let mut ctx = ProgramContext::new();
        analyze_statement(raw, &mut ctx);
        assert!(matches!(
            ctx.errors().remove(0),
            AnalyzeError {
                kind: ErrorKind::MissingReturn,
                ..
            }
        ));
    }

    #[test]
    fn non_exhaustive_conditional() {
        let raw = r#"
            fn thing(a: i64) ~ bool {
                let mut mut_a = a * 2
                if mut_a > 10 {
                    return true
                } elsif mut_a > 5 {
                    return false
                }
            }
        "#;
        let mut ctx = ProgramContext::new();
        analyze_statement(raw, &mut ctx);
        assert!(matches!(
            ctx.errors().remove(0),
            AnalyzeError {
                kind: ErrorKind::MissingReturn,
                ..
            }
        ))
    }

    #[test]
    fn conditional_with_loop() {
        let raw = r#"
            fn thing(a: i64) ~ bool {
                let mut mut_a = a * 2
                if mut_a > 10 {
                    return true
                } elsif mut_a > 5 {
                    return false
                } else  {
                    loop {
                        mut_a = mut_a * 2
                        if mut_a > 50 {
                            return true
                        }
                    }
                }
            }
        "#;
        let mut ctx = ProgramContext::new();
        analyze_statement(raw, &mut ctx);
        assert!(ctx.errors().is_empty());
    }

    #[test]
    fn conditional_with_closure() {
        let raw = r#"
            fn thing(a: i64) ~ bool {
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
        let mut ctx = ProgramContext::new();
        analyze_statement(raw, &mut ctx);
        assert!(matches!(
            ctx.errors().remove(0),
            AnalyzeError {
                kind: ErrorKind::MissingReturn,
                ..
            }
        ));
    }

    #[test]
    fn loop_with_return() {
        let raw = r#"
            fn thing(a: i64) ~ bool {
                loop {
                    return true
                }
            }
        "#;
        let mut ctx = ProgramContext::new();
        analyze_statement(raw, &mut ctx);
        assert!(ctx.errors().is_empty());
    }

    #[test]
    fn loop_with_return_in_cond() {
        let raw = r#"
            fn thing(a: i64) ~ bool {
                loop {
                    if a == 1 {
                        return true
                    }
                }
            }
        "#;
        let mut ctx = ProgramContext::new();
        analyze_statement(raw, &mut ctx);
        assert!(ctx.errors().is_empty());
    }

    #[test]
    fn loop_with_return_in_closure() {
        let raw = r#"
            fn thing(a: i64) ~ bool {
                loop {
                    loop {
                        if a == 1 {
                            return true
                        }
                    }
                }
            }
        "#;
        let mut ctx = ProgramContext::new();
        analyze_statement(raw, &mut ctx);
        assert!(ctx.errors().is_empty());
    }

    #[test]
    fn loop_with_continue() {
        let raw = r#"
            fn thing(a: i64) ~ bool {
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
        let mut ctx = ProgramContext::new();
        analyze_statement(raw, &mut ctx);
        assert!(ctx.errors().is_empty());
    }

    #[test]
    fn statements_following_return() {
        let raw = r#"
            fn thing(a: i64) ~ bool {
                return true
                a = 2
                return false
            }
        "#;
        let mut ctx = ProgramContext::new();
        analyze_statement(raw, &mut ctx);
        assert!(ctx.errors().is_empty());
        assert!(matches!(ctx.warnings().remove(0), AnalyzeWarning { .. }));
    }

    #[test]
    fn return_outside_fn() {
        let raw = "return 1";
        let mut ctx = ProgramContext::new();
        analyze_statement(raw, &mut ctx);
        assert!(matches!(
            ctx.errors().remove(0),
            AnalyzeError {
                kind: ErrorKind::UnexpectedReturn,
                ..
            }
        ));
    }

    #[test]
    fn loop_with_return_and_break() {
        let raw = r#"
            fn thing(a: i64) ~ bool {
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
        let mut ctx = ProgramContext::new();
        analyze_statement(raw, &mut ctx);
        assert!(matches!(
            ctx.errors().remove(0),
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
        let mut ctx = ProgramContext::new();
        let result = analyze_statement(raw, &mut ctx);
        assert!(ctx.errors().is_empty());
        assert_eq!(
            result,
            RichStatement::StructTypeDeclaration(RichStructType {
                name: "MyStruct".to_string(),
                fields: vec![
                    RichField {
                        name: "counter".to_string(),
                        type_id: TypeId::i64(),
                    },
                    RichField {
                        name: "is_even".to_string(),
                        type_id: TypeId::bool(),
                    },
                    RichField {
                        name: "message".to_string(),
                        type_id: TypeId::str(),
                    },
                ],
            })
        )
    }
}
