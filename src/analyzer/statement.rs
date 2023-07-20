use core::fmt;
use std::fmt::Formatter;

use crate::analyzer::closure::{analyze_break, RichClosure};
use crate::analyzer::cond::RichCond;
use crate::analyzer::func::{RichFn, RichFnCall, RichRet};
use crate::analyzer::prog_context::{ProgramContext, ScopeKind};
use crate::analyzer::var_assign::RichVarAssign;
use crate::analyzer::var_dec::RichVarDecl;
use crate::analyzer::AnalyzeResult;
use crate::parser::statement::Statement;

/// Represents a semantically valid and type-rich statement.
#[derive(PartialEq, Debug)]
pub enum RichStatement {
    VariableDeclaration(RichVarDecl),
    VariableAssignment(RichVarAssign),
    FunctionDeclaration(RichFn),
    Closure(RichClosure),
    FunctionCall(RichFnCall),
    Conditional(RichCond),
    Loop(RichClosure),
    Break,
    Return(RichRet),
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
            RichStatement::Return(v) => write!(f, "{}", v),
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
            Statement::Break => match analyze_break(ctx) {
                Ok(_) => Ok(RichStatement::Break),
                Err(e) => Err(e),
            },
            Statement::Return(expr) => match RichRet::from(ctx, expr) {
                Ok(rr) => Ok(RichStatement::Return(rr)),
                Err(e) => Err(e),
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use std::io::{BufRead, Cursor};

    use crate::analyzer::error::ErrorKind;
    use crate::analyzer::prog_context::ProgramContext;
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
                bool b = true
                return b
            }
        "#;
        let result = analyze_statement(raw);
        assert!(result.is_ok());
    }

    #[test]
    fn return_in_conditional() {
        let raw = r#"
            fn thing(i64 a): bool {
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
            fn thing(i64 a): bool {
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
            fn thing(i64 a): bool {
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
            fn thing(i64 a): bool {
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
            fn thing(i64 a): bool {
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
            fn thing(i64 a): bool {
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
            fn thing(i64 a): bool {
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
            fn thing(i64 a): bool {
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
    fn statements_following_return() {
        let raw = r#"
            fn thing(i64 a): bool {
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
            fn thing(i64 a): bool {
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
}
