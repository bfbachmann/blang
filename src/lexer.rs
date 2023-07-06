use std::result::Result;

use error::LexError;

pub mod error;
pub mod kind;
pub mod pos;
pub mod token;

type LexResult<T> = Result<T, LexError>;

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
        let result = Token::tokenize_line(r#"thing = 234 "onetwo" "three"four"" "\\\\\\""#, 0);
        assert_eq!(
            result,
            Ok(VecDeque::from(vec![
                Token::new(TokenKind::Identifier(String::from("thing")), 0, 0, 5),
                Token::new(TokenKind::Equal, 0, 6, 7),
                Token::new(TokenKind::I64Literal(234), 0, 8, 11),
                Token::new(TokenKind::StringLiteral(String::from("onetwo")), 0, 12, 20),
                Token::new(TokenKind::StringLiteral(String::from("three")), 0, 21, 28),
                Token::new(TokenKind::Identifier(String::from("four")), 0, 28, 32),
                Token::new(TokenKind::StringLiteral(String::from("")), 0, 32, 34),
                Token::new(TokenKind::StringLiteral(String::from(r#"\\\"#)), 0, 35, 43),
            ])),
        );

        let result = Token::tokenize_line(r#"if {} else if {} else {} elser iff"#, 100);
        assert_eq!(
            result,
            Ok(VecDeque::from(vec![
                Token::new(TokenKind::If, 100, 0, 2),
                Token::new(TokenKind::BeginClosure, 100, 3, 4),
                Token::new(TokenKind::EndClosure, 100, 4, 5),
                Token::new(TokenKind::ElseIf, 100, 6, 13),
                Token::new(TokenKind::BeginClosure, 100, 14, 15),
                Token::new(TokenKind::EndClosure, 100, 15, 16),
                Token::new(TokenKind::Else, 100, 17, 21),
                Token::new(TokenKind::BeginClosure, 100, 22, 23),
                Token::new(TokenKind::EndClosure, 100, 23, 24),
                Token::new(TokenKind::Identifier(String::from("elser")), 100, 25, 30),
                Token::new(TokenKind::Identifier(String::from("iff")), 100, 31, 34),
            ])),
        );

        let result = Token::tokenize_line(r#"<?>"#, 0);
        if let Err(LexError {
            message: _,
            line: _,
            col,
        }) = result
        {
            assert_eq!(col, 1);
        } else {
            panic!("Expected TokenizeError");
        }
    }
}
