#[test]
fn test_tokenize_number() {
    assert_eq!(tokenize_number("10"), Some(Token::Number(10)));
    assert_eq!(tokenize_number(""), None);
    assert_eq!(tokenize_number("a"), None);
    assert_eq!(tokenize_number("123456789"), Some(Token::Number(123456789)));
    assert_eq!(
        tokenize_number("+"),
        Some(Token::Identifier("+".to_owned()))
    );
    assert_eq!(
        tokenize_number("-"),
        Some(Token::Identifier("-".to_owned()))
    );
}
