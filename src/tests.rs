use crate::{
    Expr, Type, get_internal_val, interpret, make_program,
    parsing::{
        Binding, Command, Keyword, ParseError, Token, UnresolvedExpr, parse, tokenize,
        tokenize_number,
    },
    runtime::Val,
};

#[test]
fn test_tokenize_number() {
    assert_eq!(tokenize_number("0"), (Ok(Token::Number(0)), ""));
    assert_eq!(tokenize_number("10"), (Ok(Token::Number(10)), ""));
    assert_eq!(tokenize_number("5"), (Ok(Token::Number(5)), ""));
    assert_eq!(tokenize_number("6"), (Ok(Token::Number(6)), ""));
    assert_eq!(tokenize_number("-4"), (Ok(Token::Number(-4)), ""));
    assert_eq!(tokenize_number("-300"), (Ok(Token::Number(-300)), ""));
    assert_eq!(tokenize_number(""), (Err(ParseError::NotANumber("")), ""));
    assert_eq!(
        tokenize_number("a"),
        (Err(ParseError::NotANumber("a")), "a")
    );
    assert_eq!(
        tokenize_number("ababa"),
        (Err(ParseError::NotANumber("ababa")), "ababa")
    );
    assert_eq!(
        tokenize_number("123456789"),
        (Ok(Token::Number(123456789)), "")
    );
    assert_eq!(
        tokenize_number("+"),
        (Ok(Token::Identifier("+".to_owned())), "")
    );
    assert_eq!(
        tokenize_number("-"),
        (Ok(Token::Identifier("-".to_owned())), "")
    );
}

#[test]
fn test_tokenize1() {
    let mut tokens = tokenize("def a : u8 := 0");
    println!("test1");

    assert_eq!(tokens.next().unwrap(), Ok(Token::Keyword(Keyword::Def)));
    assert_eq!(
        tokens.next().unwrap(),
        Ok(Token::Identifier("a".to_owned()))
    );
    assert_eq!(tokens.next().unwrap(), Ok(Token::Keyword(Keyword::Colon)));
    assert_eq!(
        tokens.next().unwrap(),
        Ok(Token::Identifier("u8".to_owned()))
    );
    assert_eq!(tokens.next().unwrap(), Ok(Token::Keyword(Keyword::Eq)));
    assert_eq!(tokens.next().unwrap(), Ok(Token::Number(0)));
    assert_eq!(tokens.next(), None);
}

#[test]
fn test_tokenize2() {
    let mut tokens = tokenize("a_w_a_Wa");
    assert_eq!(
        tokens.next(),
        Some(Ok(Token::Identifier("a_w_a_Wa".to_owned())))
    )
}

#[test]
fn test_tokenize3() {
    // tests parsing number + parenthesis
    let mut tokens = tokenize("compose (add 5)");
    assert_eq!(
        tokens.next().unwrap(),
        Ok(Token::Identifier("compose".to_owned()))
    );
    assert_eq!(tokens.next().unwrap(), Ok(Token::ParenL));
    assert_eq!(
        tokens.next().unwrap(),
        Ok(Token::Identifier("add".to_owned()))
    );
    assert_eq!(tokens.next().unwrap(), Ok(Token::Number(5)));
    assert_eq!(tokens.next().unwrap(), Ok(Token::ParenR));
    assert_eq!(tokens.next(), None);
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
        parse(tokens.into_iter().map(Ok)).next().expect("what"),
        Ok(Command::Definition(Binding {
            type_sig: UnresolvedExpr::Variable("u8".to_owned()),
            var_name: "five".to_owned(),
            value: UnresolvedExpr::IntLit(5),
        }))
    );
}

#[test]
pub fn test_parse2() {
    let tokens = vec![
        Token::Identifier("add".to_owned()),
        Token::Number(5),
        Token::Number(7),
    ];
    assert_eq!(
        parse(tokens.into_iter().map(Ok)).parse_expr(),
        Ok(UnresolvedExpr::Apply(
            Box::new(UnresolvedExpr::Apply(
                Box::new(UnresolvedExpr::Variable("add".to_owned())),
                Box::new(UnresolvedExpr::IntLit(5))
            )),
            Box::new(UnresolvedExpr::IntLit(7))
        ))
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
        parse(tokens.into_iter().map(Ok)).parse_expr(),
        Ok(UnresolvedExpr::Apply(
            Box::new(UnresolvedExpr::Apply(
                Box::new(UnresolvedExpr::Variable("add".to_owned())),
                Box::new(UnresolvedExpr::IntLit(5))
            )),
            Box::new(UnresolvedExpr::IntLit(7))
        ))
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
        parse(tokens.into_iter().map(Ok)).parse_expr(),
        Ok(UnresolvedExpr::Apply(
            Box::new(UnresolvedExpr::Variable("add".to_owned())),
            Box::new(UnresolvedExpr::Apply(
                Box::new(UnresolvedExpr::IntLit(5)),
                Box::new(UnresolvedExpr::IntLit(7))
            ))
        ))
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
        parse(tokens.into_iter().map(Ok)).parse_expr(),
        Ok(UnresolvedExpr::Apply(
            Box::new(UnresolvedExpr::Apply(
                Box::new(UnresolvedExpr::Variable("add".to_owned())),
                Box::new(UnresolvedExpr::IntLit(5))
            )),
            Box::new(UnresolvedExpr::IntLit(7))
        ))
    )
}

#[test]
fn test_parse6() {
    let tokens = vec![Token::ParenL, Token::ParenR];
    assert_eq!(
        parse(tokens.into_iter().map(Ok)).parse_expr(),
        Ok(UnresolvedExpr::Unit)
    );
}

#[test]
fn test_parse7() {
    let tokens = vec![Token::Number(5), Token::ParenL, Token::ParenR];
    assert_eq!(
        parse(tokens.into_iter().map(Ok)).parse_expr(),
        Ok(UnresolvedExpr::Apply(
            Box::new(UnresolvedExpr::IntLit(5)),
            Box::new(UnresolvedExpr::Unit)
        )),
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
        parse(tokens.into_iter().map(Ok)).parse_expr(),
        Ok(UnresolvedExpr::Apply(
            Box::new(UnresolvedExpr::IntLit(5)),
            Box::new(UnresolvedExpr::Unit)
        )),
    );
}

#[test]
fn test_parse9() {
    let tokens = vec![
        // hi () 6
        Token::Identifier("hi".to_string()),
        Token::ParenL,
        Token::ParenR,
        Token::Number(6),
    ];
    assert_eq!(
        parse(tokens.into_iter().map(Ok)).parse_expr(),
        Ok(UnresolvedExpr::Apply(
            Box::new(UnresolvedExpr::Apply(
                Box::new(UnresolvedExpr::Variable("hi".to_string())),
                Box::new(UnresolvedExpr::Unit)
            )),
            Box::new(UnresolvedExpr::IntLit(6))
        )),
    );
}

#[test]
fn test_interpret1() {
    // functions can get variables and stuff correctly
    let val: Expr = Expr::Apply(
        Box::new(Expr::Apply(
            Box::new(Expr::Function {
                input_type: Box::new(Expr::Value(Box::new(Val::Type(Type::Type)))),
                output: Box::new(Expr::Function {
                    input_type: Box::new(Expr::Value(Box::new(Val::Type(Type::Type)))),
                    output: Box::new(Expr::Local(1)),
                }),
            }),
            Box::new(Expr::Value(Box::new(Val::Type(Type::Int)))),
        )),
        Box::new(Expr::Value(Box::new(Val::Type(Type::Unit)))),
    );

    match interpret(&Vec::new(), val) {
        Ok(res) => assert_eq!(res, Val::Type(Type::Int)),
        Err(e) => panic!("Interpretting reached error: {:?}", e),
    };
}

#[test]
fn test_interpret2() {
    let (names, global, evals) = make_program(
        "def fun Int (fun Type (fun Type Type)): f := fn Int: x do
          fn Type: T do
          fn Type: Y do
        	fun T Y
        eval f -2 Int Type",
    )
    .expect("Failed to parse program");
    assert!(global.len() == 1);
    dbg!(&global[0]);
    assert!(names == vec!["f".to_string()]);
    assert!(&evals.len() == &1);

    let val = evals[0].clone();

    let expected = Val::Type(crate::Type::FunctionType(
        Box::new(crate::Type::Int),
        Box::new(crate::Type::Type),
    ));
    match interpret(&global, val) {
        Ok(v) => assert_eq!(v, expected),
        Err(e) => panic!("Interpretting reached error: {:?}", e),
    }
}

#[test]
fn test_interpret3() {
    let (names, global, evals) =
        make_program("eval mk_pair Int (PairType Unit Int) 6 (mk_pair Unit Int () -1700)")
            .expect("Failed to parse program");
    assert!(names.len() == 0);
    assert!(global.len() == 0);
    assert!(&evals.len() == &1);

    let expected: Val = Val::Pair(
        Box::new(Val::IntLit(6)),
        Box::new(Val::Pair(Box::new(Val::Unit), Box::new(Val::IntLit(-1700)))),
    );
    match interpret(&global, evals[0].clone()) {
        Ok(v) => assert_eq!(v, expected),
        Err(e) => panic!("Interpretting reached error: {:?}", e),
    }
}
