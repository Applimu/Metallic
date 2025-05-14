use std::rc::Rc;

use crate::{Binding, Expr, Keyword, Token, parse, tokenize, tokenize_number};

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

#[test]
fn test_tokenize1() {
    let tokenized: Vec<Token> = tokenize(
        "
        def a : u8 := 0
        ",
    )
    .collect();
    println!("Tokenizing: {:?}", tokenized);
    assert_eq!(
        tokenized,
        vec![
            Token::Keyword(Keyword::Def),
            Token::Identifier("a".to_owned()),
            Token::Keyword(Keyword::Colon),
            Token::Identifier("u8".to_owned()),
            Token::Keyword(Keyword::Eq),
            Token::Number(0)
        ]
    );
}

#[test]
fn test_tokenize2() {
    let tokenized: Vec<Token> = tokenize("a_w_a_Wa").collect();
    assert_eq!(tokenized, vec![Token::Identifier("a_w_a_Wa".to_owned())])
}

#[test]
pub fn test_parse1() {
    let tokens = vec![
        Token::Keyword(Keyword::Def),
        Token::Identifier("u8".to_owned()),
        Token::Keyword(Keyword::Colon),
        Token::Identifier("five".to_owned()),
        Token::Keyword(Keyword::Eq),
        Token::Number(5),
    ];
    assert_eq!(
        parse(tokens.into_iter()).next().expect("Failed to parse"),
        Binding {
            type_sig: Expr::Variable("u8".to_owned()),
            var_name: "five".to_owned(),
            value: Expr::IntLit(5),
        }
    )
}

#[test]
pub fn test_parse2() {
    let tokens = vec![
        Token::Identifier("add".to_owned()),
        Token::Number(5),
        Token::Number(7),
    ];
    assert_eq!(
        parse(tokens.into_iter())
            .parse_expr()
            .expect("Failed parse"),
        Expr::Apply(
            Box::new(Expr::Apply(
                Box::new(Expr::Variable("add".to_owned())),
                Box::new(Expr::IntLit(5))
            )),
            Box::new(Expr::IntLit(7))
        )
    )
}

#[test]
pub fn test_parse3() {
    let tokens = vec![
        Token::ParenL,
        Token::Identifier("add".to_owned()),
        Token::Number(5),
        Token::Number(7),
        Token::ParenR,
    ];
    assert_eq!(
        parse(tokens.into_iter())
            .parse_expr()
            .expect("Failed parse"),
        Expr::Apply(
            Box::new(Expr::Apply(
                Box::new(Expr::Variable("add".to_owned())),
                Box::new(Expr::IntLit(5))
            )),
            Box::new(Expr::IntLit(7))
        )
    )
}

#[test]
pub fn test_parse4() {
    // (add (5 7))
    let tokens = vec![
        Token::ParenL,
        Token::Identifier("add".to_owned()),
        Token::ParenL,
        Token::Number(5),
        Token::Number(7),
        Token::ParenR,
        Token::ParenR,
    ];
    assert_eq!(
        parse(tokens.into_iter())
            .parse_expr()
            .expect("Failed parse"),
        Expr::Apply(
            Box::new(Expr::Variable("add".to_owned())),
            Box::new(Expr::Apply(
                Box::new(Expr::IntLit(5)),
                Box::new(Expr::IntLit(7))
            ))
        )
    )
}

#[test]
pub fn test_parse5() {
    // ((add 5) 7 )
    let tokens = vec![
        Token::ParenL,
        Token::ParenL,
        Token::Identifier("add".to_owned()),
        Token::Number(5),
        Token::ParenR,
        Token::Number(7),
        Token::ParenR,
    ];
    assert_eq!(
        parse(tokens.into_iter())
            .parse_expr()
            .expect("Failed parse"),
        Expr::Apply(
            Box::new(Expr::Apply(
                Box::new(Expr::Variable("add".to_owned())),
                Box::new(Expr::IntLit(5))
            )),
            Box::new(Expr::IntLit(7))
        )
    )
}

#[test]
fn test_parse6() {
    let tokens = vec![Token::ParenL, Token::ParenR];
    assert_eq!(
        parse(tokens.into_iter())
            .parse_expr()
            .expect("Failed Parsing `()`"),
        Expr::Unit
    );
}

#[test]
fn test_parse7() {
    let tokens = vec![Token::Number(5), Token::ParenL, Token::ParenR];
    assert_eq!(
        parse(tokens.into_iter())
            .parse_expr()
            .expect("Failed Parsing `5 ()`"),
        Expr::Apply(Box::new(Expr::IntLit(5)), Box::new(Expr::Unit)),
    );
}

#[test]
fn test_parse8() {
    let tokens = vec![
        Token::Number(5),
        Token::ParenL,
        Token::ParenL,
        Token::ParenR,
        Token::ParenR,
    ];
    assert_eq!(
        parse(tokens.into_iter())
            .parse_expr()
            .expect("Failed Parsing `5 ()`"),
        Expr::Apply(Box::new(Expr::IntLit(5)), Box::new(Expr::Unit)),
    );
}
