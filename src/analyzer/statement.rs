use core::fmt;
use std::fmt::Formatter;

use crate::analyzer::closure::{analyze_break, analyze_continue, RichClosure};
use crate::analyzer::cond::RichCond;
use crate::analyzer::func::{RichFn, RichFnCall, RichRet};
use crate::analyzer::prog_context::{ProgramContext, ScopeKind};
use crate::analyzer::r#struct::RichStruct;
use crate::analyzer::var_assign::RichVarAssign;
use crate::analyzer::var_dec::RichVarDecl;
use crate::analyzer::AnalyzeResult;
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
    StructTypeDeclaration(RichStruct),
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
        }
    }
}

impl RichStatement {
    /// Performs semantic analysis on the given statement and returns a type-rich version of it,
    /// or an error if the statement is semantically invalid.
    pub fn from(ctx: &mut ProgramContext, statement: Statement) -> AnalyzeResult<Self> {
        match statement {
            Statement::VariableDeclaration(var_decl) => match RichVarDecl::from(ctx, var_decl) {
                Ok(rvd) => Ok(RichStatement::VariableDeclaration(rvd)),
                Err(e) => Err(e),
            },
            Statement::VariableAssignment(var_assign) => match RichVarAssign::from(ctx, var_assign)
            {
                Ok(va) => Ok(RichStatement::VariableAssignment(va)),
                Err(e) => Err(e),
            },
            Statement::FunctionDeclaration(fn_decl) => match RichFn::from(ctx, fn_decl) {
                Ok(fd) => Ok(RichStatement::FunctionDeclaration(fd)),
                Err(e) => Err(e),
            },
            Statement::Closure(closure) => {
                match RichClosure::from(ctx, closure, ScopeKind::Inline, vec![], None) {
                    Ok(rc) => Ok(RichStatement::Closure(rc)),
                    Err(e) => Err(e),
                }
            }
            Statement::FunctionCall(call) => match RichFnCall::from(ctx, call) {
                Ok(rfc) => Ok(RichStatement::FunctionCall(rfc)),
                Err(e) => Err(e),
            },
            Statement::Conditional(cond) => match RichCond::from(ctx, cond) {
                Ok(rc) => Ok(RichStatement::Conditional(rc)),
                Err(e) => Err(e),
            },
            Statement::Loop(loop_) => {
                match RichClosure::from(ctx, loop_.closure, ScopeKind::Loop, vec![], None) {
                    Ok(rc) => Ok(RichStatement::Loop(rc)),
                    Err(e) => Err(e),
                }
            }
            Statement::Break(br) => match analyze_break(ctx, br) {
                Ok(_) => Ok(RichStatement::Break),
                Err(e) => Err(e),
            },
            Statement::Continue(cont) => match analyze_continue(ctx, cont) {
                Ok(_) => Ok(RichStatement::Continue),
                Err(e) => Err(e),
            },
            Statement::Return(ret) => match RichRet::from(ctx, ret) {
                Ok(rr) => Ok(RichStatement::Return(rr)),
                Err(e) => Err(e),
            },
            Statement::StructDeclaration(s) => {
                let rich_struct = RichStruct::from(ctx, &s, false)?;
                Ok(RichStatement::StructTypeDeclaration(rich_struct))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::io::{BufRead, Cursor};

    use crate::analyzer::error::ErrorKind;
    use crate::analyzer::prog_context::ProgramContext;
    use crate::analyzer::r#struct::{RichField, RichStruct};
    use crate::analyzer::r#type::RichType;
    use crate::analyzer::statement::RichStatement;
    use crate::analyzer::AnalyzeError;
    use crate::analyzer::AnalyzeResult;
    use crate::lexer::token::Token;
    use crate::parser::statement::Statement;

    fn analyze_statement(raw: &str) -> AnalyzeResult<RichStatement> {
        let mut tokens = Token::tokenize(Cursor::new(raw).lines()).expect("should not error");
        let statement = Statement::from(&mut tokens).expect("should not error");
        let mut ctx = ProgramContext::new();
        RichStatement::from(&mut ctx, statement)
    }

    #[test]
    fn simple_return() {
        let raw = r#"
            fn thing(): bool {
                let b = true
                return b
            }
        "#;
        let result = analyze_statement(raw);
        assert!(result.is_ok());
    }

    #[test]
    fn return_in_conditional() {
        let raw = r#"
            fn thing(a: i64): bool {
                a = a * 2
                if a > 10 {
                    return true
                } else if a > 5 {
                    return false
                } else  {
                    return true
                }
            }
        "#;
        let result = analyze_statement(raw);
        assert!(result.is_ok());
    }

    #[test]
    fn missing_return_in_conditional() {
        let raw = r#"
            fn thing(a: i64): bool {
                a = a * 2
                if a > 10 {
                    return true
                } else if a > 5 {
                    return false
                } else  {
                    a = 2
                }
            }
        "#;
        let result = analyze_statement(raw);
        assert!(result.is_err());
    }

    #[test]
    fn non_exhaustive_conditional() {
        let raw = r#"
            fn thing(a: i64): bool {
                a = a * 2
                if a > 10 {
                    return true
                } else if a > 5 {
                    return false
                }
            }
        "#;
        let result = analyze_statement(raw);
        assert!(result.is_err());
    }

    #[test]
    fn conditional_with_loop() {
        let raw = r#"
            fn thing(a: i64): bool {
                a = a * 2
                if a > 10 {
                    return true
                } else if a > 5 {
                    return false
                } else  {
                    loop {
                        a = a * 2
                        if a > 50 {
                            return true
                        }
                    }
                }
            }
        "#;
        let result = analyze_statement(raw);
        assert!(result.is_ok());
    }

    #[test]
    fn conditional_with_closure() {
        let raw = r#"
            fn thing(a: i64): bool {
                a = a * 2
                if a > 10 {
                    return true
                } else {
                    {
                        if a > 50 {
                            return true
                        }
                    }
                }
            }
        "#;
        let result = analyze_statement(raw);
        assert!(matches!(
            result,
            Err(AnalyzeError {
                kind: ErrorKind::MissingReturn,
                ..
            })
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
        let result = analyze_statement(raw);
        assert!(result.is_ok());
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
        let result = analyze_statement(raw);
        assert!(result.is_ok());
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
        let result = analyze_statement(raw);
        assert!(result.is_ok());
    }

    #[test]
    fn loop_with_continue() {
        let raw = r#"
            fn thing(a: i64): bool {
                loop {
                    a = a - 1
                    if a == 1 {
                        continue
                    }
                    
                    return true
                }
            }
        "#;
        let result = analyze_statement(raw);
        assert!(result.is_ok());
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
        let result = analyze_statement(raw);
        assert!(matches!(
            result,
            Err(AnalyzeError {
                kind: ErrorKind::UnexpectedReturn,
                ..
            })
        ));
    }

    #[test]
    fn return_outside_fn() {
        let raw = "return 1";
        let result = analyze_statement(raw);
        assert!(matches!(
            result,
            Err(AnalyzeError {
                kind: ErrorKind::UnexpectedReturn,
                ..
            })
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
        let result = analyze_statement(raw);
        assert!(matches!(
            result,
            Err(AnalyzeError {
                kind: ErrorKind::MissingReturn,
                ..
            })
        ));
    }

    #[test]
    fn struct_decl() {
        let raw = r#"
            struct MyStruct {
                counter: i64,
                is_even: bool,
                message: string,
            }
        "#;
        let result = analyze_statement(raw);
        assert_eq!(
            result,
            Ok(RichStatement::StructTypeDeclaration(RichStruct {
                name: "MyStruct".to_string(),
                fields: vec![
                    RichField {
                        name: "counter".to_string(),
                        typ: RichType::I64
                    },
                    RichField {
                        name: "is_even".to_string(),
                        typ: RichType::Bool
                    },
                    RichField {
                        name: "message".to_string(),
                        typ: RichType::String
                    },
                ],
            }))
        )
    }
}
