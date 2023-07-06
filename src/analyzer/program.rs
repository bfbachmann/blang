use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::func::{analyze_fn_decl, analyze_fn_sig};
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::statement::analyze_statement;
use crate::analyzer::var_dec::analyze_var_decl;
use crate::analyzer::AnalyzeResult;
use crate::parser::program::Program;
use crate::parser::statement::Statement;

fn analyze_program(program: &Program) -> AnalyzeResult<()> {
    let mut ctx = ProgramContext::new();

    // Analyze all function signatures defined at the top level of the program so we can reference
    // them when we analyze statements.
    for statement in &program.statements {
        match statement {
            Statement::FunctionDeclaration(func) => {
                analyze_fn_sig(&mut ctx, &func.signature)?;
            }
            _ => {}
        }
    }

    // Analyze each statement in the program.
    for statement in &program.statements {
        analyze_statement(&mut ctx, statement)?;
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use std::io::{BufRead, Cursor};

    use crate::analyzer::error::{AnalyzeError, ErrorKind};
    use crate::analyzer::program::analyze_program;
    use crate::lexer::token::Token;
    use crate::parser::program::Program;

    #[test]
    fn variable_assignment() {
        let raw = r#"
        int i = 10
        i = 11
        "#;
        let mut tokens = Token::tokenize(Cursor::new(raw).lines()).expect("should not error");
        let prog = Program::from(&mut tokens).expect("should not error");
        let result = analyze_program(&prog);
        assert!(matches!(result, Ok(())));
    }

    #[test]
    fn fn_decl() {
        let raw = r#"
        fn test(int a, string b) { 
            string s = "hello world!" 
        }"#;
        let mut tokens = Token::tokenize(Cursor::new(raw).lines()).expect("should not error");
        let prog = Program::from(&mut tokens).expect("should not error");
        let result = analyze_program(&prog);
        assert!(matches!(result, Ok(())));
    }

    #[test]
    fn fn_already_defined() {
        let raw = r#"
        fn test() {}
        fn test(string thing) {}
        "#;
        let mut tokens = Token::tokenize(Cursor::new(raw).lines()).expect("should not error");
        let prog = Program::from(&mut tokens).expect("should not error");
        let result = analyze_program(&prog);
        assert!(matches!(
            result,
            Err(AnalyzeError {
                kind: ErrorKind::FunctionAlreadyDefined,
                ..
            })
        ));
    }

    #[test]
    fn multiple_functions() {
        let raw = r#"
        string s = "Hello world!"
        
        fn main() {
            do_thing()
        }
        
        fn do_thing() {
            string v = s
        }
        "#;

        let mut tokens = Token::tokenize(Cursor::new(raw).lines()).expect("should not error");
        let prog = Program::from(&mut tokens).expect("should not error");
        let result = analyze_program(&prog);
        assert!(matches!(result, Ok(())));
    }
}
