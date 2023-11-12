#[cfg(test)]
mod tests {
    use crate::lexer::error::{LexError, LexResult};
    use crate::lexer::lex::lex;
    use crate::lexer::stream::Stream;
    use crate::lexer::token::Token;
    use crate::lexer::token_kind::TokenKind;

    fn tokenize(code: &str) -> LexResult<Vec<Token>> {
        lex(&mut Stream::from(code.chars().collect()))
    }

    #[test]
    fn lex_add() {
        let result = TokenKind::from(" + ");
        assert_eq!(result, Some(TokenKind::Add));

        let result = TokenKind::from(" aos83;2/ ");
        assert_eq!(result, None);
    }

    #[test]
    fn lex_subtract() {
        let result = TokenKind::from(" - ");
        assert_eq!(result, Some(TokenKind::Subtract));

        let result = TokenKind::from(" ao9u5424lm/ ");
        assert_eq!(result, None);
    }

    #[test]
    fn lex_equal() {
        let result = TokenKind::from(" = ");
        assert_eq!(result, Some(TokenKind::Equal));

        let result = TokenKind::from(" ?#li4kU#@(U* ");
        assert_eq!(result, None);
    }

    #[test]
    fn lex_i64_literal() {
        let result = TokenKind::from(" 123 ");
        assert_eq!(result, Some(TokenKind::I64Literal(123, false)));

        let result = TokenKind::from(" 9923423 ");
        assert_eq!(result, Some(TokenKind::I64Literal(9923423, false)));

        let result = TokenKind::from(" ..23423;lj1 ");
        assert_eq!(result, None);
    }

    #[test]
    fn lex_identifier() {
        let result = TokenKind::from(" _a_2_32sdfkeFDSwre980 ");
        assert_eq!(
            result,
            Some(TokenKind::Identifier(String::from("_a_2_32sdfkeFDSwre980")))
        );

        let result = TokenKind::from(" asr32/23 ");
        assert_eq!(result, None);
    }

    #[test]
    fn lex_str_literal() {
        let result = TokenKind::from(" \"asdf\" ");
        assert_eq!(result, Some(TokenKind::StrLiteral(String::from("asdf"))));

        let result = TokenKind::from(r#" "say \"something\"!!" "#);
        assert_eq!(
            result,
            Some(TokenKind::StrLiteral(String::from(r#"say "something"!!"#)))
        );

        let result = TokenKind::from(r#" "" "#);
        assert_eq!(result, Some(TokenKind::StrLiteral(String::from(""))));

        let result = TokenKind::from(r#" "\\\\" "#);
        assert_eq!(result, Some(TokenKind::StrLiteral(String::from(r#"\\"#))));

        let result = TokenKind::from(r#""\n\t\r""#);
        assert_eq!(result, Some(TokenKind::StrLiteral("\n\t\r".to_string())));

        let result = TokenKind::from(r#" "23424?? "#);
        assert_eq!(result, None);
    }

    #[test]
    fn tokenize_line() {
        let result = tokenize(r#"thing = 234 "onetwo" "three"four"" "\\\\\\""#);
        assert_eq!(
            result,
            Ok(vec![
                Token::new(TokenKind::Identifier(String::from("thing")), 1, 1, 6),
                Token::new(TokenKind::Equal, 1, 7, 8),
                Token::new(TokenKind::I64Literal(234, false), 1, 9, 12),
                Token::new(TokenKind::StrLiteral(String::from("onetwo")), 1, 13, 21),
                Token::new(TokenKind::StrLiteral(String::from("three")), 1, 22, 29),
                Token::new(TokenKind::Identifier(String::from("four")), 1, 29, 33),
                Token::new(TokenKind::StrLiteral(String::from("")), 1, 33, 35),
                Token::new(TokenKind::StrLiteral(String::from(r#"\\\"#)), 1, 36, 44),
            ]),
        );

        let result = tokenize(r#"if {} elsif {} else {} elser iff"#);
        assert_eq!(
            result,
            Ok(vec![
                Token::new(TokenKind::If, 1, 1, 3),
                Token::new(TokenKind::LeftBrace, 1, 4, 5),
                Token::new(TokenKind::RightBrace, 1, 5, 6),
                Token::new(TokenKind::Elsif, 1, 7, 12),
                Token::new(TokenKind::LeftBrace, 1, 13, 14),
                Token::new(TokenKind::RightBrace, 1, 14, 15),
                Token::new(TokenKind::Else, 1, 16, 20),
                Token::new(TokenKind::LeftBrace, 1, 21, 22),
                Token::new(TokenKind::RightBrace, 1, 22, 23),
                Token::new(TokenKind::Identifier(String::from("elser")), 1, 24, 29),
                Token::new(TokenKind::Identifier(String::from("iff")), 1, 30, 33),
            ]),
        );

        let result = tokenize(r#"<?>"#);
        assert!(matches!(
            result,
            Err(LexError {
                message: _,
                line: _,
                col: 2,
            })
        ));
    }

    #[test]
    fn block_comments() {
        let result = tokenize(
            r#"
            fn main(){
                /* this is a block comment */
                
                /*
                    This is
                        /* a nested block comment */
                */
            }
        "#,
        );
        assert!(result.is_ok());
    }
}
