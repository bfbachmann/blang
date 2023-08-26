pub mod error;
pub mod kind;
pub mod pos;
pub mod token;

#[cfg(test)]
mod tests {
    use std::collections::VecDeque;

    use crate::lexer::error::LexError;
    use crate::lexer::kind::TokenKind;
    use crate::lexer::token::Token;

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
        assert_eq!(result, Some(TokenKind::I64Literal(123)));

        let result = TokenKind::from(" 9923423 ");
        assert_eq!(result, Some(TokenKind::I64Literal(9923423)));

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
    fn lex_string_literal() {
        let result = TokenKind::from(" \"asdf\" ");
        assert_eq!(result, Some(TokenKind::StringLiteral(String::from("asdf"))));

        let result = TokenKind::from(r#" "say \"something\"!!" "#);
        assert_eq!(
            result,
            Some(TokenKind::StringLiteral(String::from(
                r#"say "something"!!"#
            )))
        );

        let result = TokenKind::from(r#" "" "#);
        assert_eq!(result, Some(TokenKind::StringLiteral(String::from(""))));

        let result = TokenKind::from(r#" "\\\\" "#);
        assert_eq!(
            result,
            Some(TokenKind::StringLiteral(String::from(r#"\\"#)))
        );

        let result = TokenKind::from(r#""\n\t\r""#);
        assert_eq!(result, Some(TokenKind::StringLiteral("\n\t\r".to_string())));

        let result = TokenKind::from(r#" "23424?? "#);
        assert_eq!(result, None);
    }

    #[test]
    fn lex_first() {
        let result = TokenKind::first_from("letter ");
        assert_eq!(
            result,
            Some((TokenKind::Identifier(String::from("letter")), 7)),
        );

        let result = TokenKind::first_from("thing 234 ");
        assert_eq!(
            result,
            Some((TokenKind::Identifier(String::from("thing")), 6))
        );

        let result = TokenKind::first_from("    3784751 --");
        assert_eq!(result, Some((TokenKind::I64Literal(3784751), 12)),);

        let result = TokenKind::first_from("  =letting 435");
        assert_eq!(result, Some((TokenKind::Equal, 3)),);

        let result = TokenKind::first_from("  =letting ");
        assert_eq!(result, Some((TokenKind::Equal, 3)),);

        let result = TokenKind::first_from("  +++++ ");
        assert_eq!(result, Some((TokenKind::Add, 3)),);

        let result = TokenKind::first_from("  -3480 ");
        assert_eq!(result, Some((TokenKind::Subtract, 3)),);

        let result = TokenKind::first_from(r#"  "some \"BIG\" string" "#);
        assert_eq!(
            result,
            Some((
                TokenKind::StringLiteral(String::from(r#"some "BIG" string"#)),
                24,
            )),
        );

        let result = TokenKind::first_from(" #$J@#?@ ");
        assert_eq!(result, None);
    }

    #[test]
    fn tokenize_line() {
        let result = Token::tokenize_line(r#"thing = 234 "onetwo" "three"four"" "\\\\\\""#, 1);
        assert_eq!(
            result,
            Ok(VecDeque::from(vec![
                Token::new(TokenKind::Identifier(String::from("thing")), 1, 1, 6),
                Token::new(TokenKind::Equal, 1, 7, 8),
                Token::new(TokenKind::I64Literal(234), 1, 9, 12),
                Token::new(TokenKind::StringLiteral(String::from("onetwo")), 1, 13, 21),
                Token::new(TokenKind::StringLiteral(String::from("three")), 1, 22, 29),
                Token::new(TokenKind::Identifier(String::from("four")), 1, 29, 33),
                Token::new(TokenKind::StringLiteral(String::from("")), 1, 33, 35),
                Token::new(TokenKind::StringLiteral(String::from(r#"\\\"#)), 1, 36, 44),
            ])),
        );

        let result = Token::tokenize_line(r#"if {} else if {} else {} elser iff"#, 100);
        assert_eq!(
            result,
            Ok(VecDeque::from(vec![
                Token::new(TokenKind::If, 100, 1, 3),
                Token::new(TokenKind::LeftBrace, 100, 4, 5),
                Token::new(TokenKind::RightBrace, 100, 5, 6),
                Token::new(TokenKind::ElseIf, 100, 7, 14),
                Token::new(TokenKind::LeftBrace, 100, 15, 16),
                Token::new(TokenKind::RightBrace, 100, 16, 17),
                Token::new(TokenKind::Else, 100, 18, 22),
                Token::new(TokenKind::LeftBrace, 100, 23, 24),
                Token::new(TokenKind::RightBrace, 100, 24, 25),
                Token::new(TokenKind::Identifier(String::from("elser")), 100, 26, 31),
                Token::new(TokenKind::Identifier(String::from("iff")), 100, 32, 35),
            ])),
        );

        let result = Token::tokenize_line(r#"<?>"#, 1);
        assert!(matches!(
            result,
            Err(LexError {
                message: _,
                line: _,
                col: 2,
            })
        ));
    }
}
