use std::{collections::HashMap, rc::Rc};

use crate::{
    Expr, Type, interpret, make_program,
    parsing::{
        Binding, Command, Keyword, Matching, ParseError, Token, UnresolvedExpr, parse, tokenize,
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
fn test_tokenize4() {
    // tests parsing number + parenthesis
    let mut tokens = tokenize(
        "add 7 -2 // this is a comment
        13",
    );
    assert_eq!(
        tokens.next().unwrap(),
        Ok(Token::Identifier("add".to_owned()))
    );
    assert_eq!(tokens.next().unwrap(), Ok(Token::Number(7)));
    assert_eq!(tokens.next().unwrap(), Ok(Token::Number(-2)));
    assert_eq!(tokens.next().unwrap(), Ok(Token::Number(13)));
    assert_eq!(tokens.next(), None);
}

#[test]
fn test_tokenize5() {
    // tests parsing number + parenthesis
    let mut tokens = tokenize(
        "add 7 -2//this is a comment
        13",
    );
    assert_eq!(
        tokens.next().unwrap(),
        Ok(Token::Identifier("add".to_owned()))
    );
    assert_eq!(tokens.next().unwrap(), Ok(Token::Number(7)));
    assert_eq!(tokens.next().unwrap(), Ok(Token::Number(-2)));
    assert_eq!(tokens.next().unwrap(), Ok(Token::Number(13)));
    assert_eq!(tokens.next(), None);
}

#[test]
pub fn test_parse01() {
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
pub fn test_parse02() {
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
pub fn test_parse03() {
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
pub fn test_parse04() {
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
pub fn test_parse05() {
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
fn test_parse06() {
    let tokens = vec![Token::ParenL, Token::ParenR];
    assert_eq!(
        parse(tokens.into_iter().map(Ok)).parse_expr(),
        Ok(UnresolvedExpr::Unit)
    );
}

#[test]
fn test_parse07() {
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
fn test_parse08() {
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
fn test_parse09() {
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
fn test_parse10() {
    // tests empty match statement
    let tokens = vec![
        Token::Keyword(Keyword::Match),
        Token::Identifier("hi".to_string()),
        Token::Keyword(Keyword::End),
        Token::Number(6),
    ];
    assert_eq!(
        parse(tokens.into_iter().map(Ok)).parse_expr(),
        Ok(UnresolvedExpr::Apply(
            Box::new(UnresolvedExpr::Match(Matching {
                matchend: "hi".to_owned(),
                branches: HashMap::new(),
            })),
            Box::new(UnresolvedExpr::IntLit(6))
        )),
    );
}

#[test]
fn test_parse11() {
    // test match with one case
    let tokens = vec![
        Token::Keyword(Keyword::Match),
        Token::Identifier("hi".to_string()),
        Token::Keyword(Keyword::Case),
        Token::Identifier("case1".to_string()),
        Token::Keyword(Keyword::Do),
        Token::Identifier("add".to_string()),
        Token::Number(0),
        Token::Number(1),
        Token::Keyword(Keyword::End),
        Token::Number(6),
    ];
    let mut case_map = HashMap::new();
    case_map.insert(
        "case1".to_string(),
        UnresolvedExpr::Apply(
            Box::new(UnresolvedExpr::Apply(
                Box::new(UnresolvedExpr::Variable("add".to_string())),
                Box::new(UnresolvedExpr::IntLit(0)),
            )),
            Box::new(UnresolvedExpr::IntLit(1)),
        ),
    );
    assert_eq!(
        parse(tokens.into_iter().map(Ok)).parse_expr(),
        Ok(UnresolvedExpr::Apply(
            Box::new(UnresolvedExpr::Match(Matching {
                matchend: "hi".to_owned(),
                branches: case_map,
            })),
            Box::new(UnresolvedExpr::IntLit(6))
        )),
    );
}

#[test]
fn test_parse12() {
    // function that returns a match statement all applied to another expression
    let tokens = vec![
        Token::ParenL,
        Token::Keyword(Keyword::Fn),
        Token::Identifier("Bool".to_owned()),
        Token::Keyword(Keyword::Colon),
        Token::Identifier("input".to_owned()),
        Token::Keyword(Keyword::Do),
        Token::Keyword(Keyword::Match),
        Token::Identifier("hi".to_string()),
        Token::Keyword(Keyword::End),
        Token::ParenR,
        Token::ParenL,
        Token::Identifier("x".to_owned()),
        Token::Number(5),
        Token::ParenR,
    ];
    let inner_match = Box::new(UnresolvedExpr::Match(Matching {
        matchend: "hi".to_owned(),
        branches: HashMap::new(),
    }));
    let func = UnresolvedExpr::Function {
        name: "input".to_owned(),
        input_type: Box::new(UnresolvedExpr::Variable("Bool".to_owned())),
        output: inner_match,
    };
    assert_eq!(
        parse(tokens.into_iter().map(Ok)).parse_expr(),
        Ok(UnresolvedExpr::Apply(
            Box::new(func),
            Box::new(UnresolvedExpr::Apply(
                Box::new(UnresolvedExpr::Variable("x".to_owned())),
                Box::new(UnresolvedExpr::IntLit(5))
            ))
        )),
    );
}

#[test]
fn test_parse13() {
    // same as 12 but with no matchs statement
    let tokens = vec![
        Token::ParenL,
        Token::Keyword(Keyword::Fn),
        Token::Identifier("Bool".to_owned()),
        Token::Keyword(Keyword::Colon),
        Token::Identifier("input".to_owned()),
        Token::Keyword(Keyword::Do),
        Token::Identifier("input".to_owned()),
        Token::ParenR,
        Token::ParenL,
        Token::Identifier("x".to_owned()),
        Token::Number(5),
        Token::ParenR,
    ];
    let func = UnresolvedExpr::Function {
        name: "input".to_owned(),
        input_type: Box::new(UnresolvedExpr::Variable("Bool".to_owned())),
        output: Box::new(UnresolvedExpr::Variable("input".to_owned())),
    };
    assert_eq!(
        parse(tokens.into_iter().map(Ok)).parse_expr(),
        Ok(UnresolvedExpr::Apply(
            Box::new(func),
            Box::new(UnresolvedExpr::Apply(
                Box::new(UnresolvedExpr::Variable("x".to_owned())),
                Box::new(UnresolvedExpr::IntLit(5))
            ))
        )),
    );
}

#[test]
fn test_parse14() {
    let tokens = vec![
        Token::Keyword(Keyword::Let),
        Token::Identifier("Bool".to_owned()),
        Token::Keyword(Keyword::Colon),
        Token::Identifier("x".to_owned()),
        Token::Keyword(Keyword::Eq),
        Token::Identifier("true".to_owned()),
        Token::Keyword(Keyword::In),
        Token::Number(5),
    ];
    assert_eq!(
        parse(tokens.into_iter().map(Ok)).parse_expr(),
        Ok(UnresolvedExpr::Let(
            Box::new(Binding {
                var_name: "x".to_owned(),
                type_sig: UnresolvedExpr::Variable("Bool".to_owned()),
                value: UnresolvedExpr::Variable("true".to_owned())
            }),
            Box::new(UnresolvedExpr::IntLit(5))
        ))
    );
}

#[test]
fn test_parse15() {
    let tokens = vec![
        Token::Number(7),
        Token::Keyword(Keyword::Let),
        Token::Identifier("Bool".to_owned()),
        Token::Keyword(Keyword::Colon),
        Token::Identifier("x".to_owned()),
        Token::Keyword(Keyword::Eq),
        Token::Identifier("true".to_owned()),
        Token::Keyword(Keyword::In),
        Token::Number(5),
    ];
    assert_eq!(
        parse(tokens.into_iter().map(Ok)).parse_expr(),
        Ok(UnresolvedExpr::Apply(
            Box::new(UnresolvedExpr::IntLit(7)),
            Box::new(UnresolvedExpr::Let(
                Box::new(Binding {
                    var_name: "x".to_owned(),
                    type_sig: UnresolvedExpr::Variable("Bool".to_owned()),
                    value: UnresolvedExpr::Variable("true".to_owned())
                }),
                Box::new(UnresolvedExpr::IntLit(5))
            ))
        ))
    );
}

#[test]
fn test_interpret1() {
    // functions can get variables and stuff correctly
    let val: Expr = Expr::Apply(
        Rc::new(Expr::Apply(
            Rc::new(Expr::Function {
                input_type: Rc::new(Expr::Value(Rc::new(Val::Type(Rc::new(Type::Type))))),
                output: Rc::new(Expr::Function {
                    input_type: Rc::new(Expr::Value(Rc::new(Val::Type(Rc::new(Type::Type))))),
                    output: Rc::new(Expr::Local(1)),
                }),
            }),
            Rc::new(Expr::Value(Rc::new(Val::Type(Rc::new(Type::Int))))),
        )),
        Rc::new(Expr::Value(Rc::new(Val::Type(Rc::new(Type::Unit))))),
    );

    match interpret(Vec::new(), &val) {
        Ok(res) => assert_eq!(*res, Val::Type(Rc::new(Type::Int))),
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

    let expected = Val::Type(Rc::new(Type::FunctionType(
        Rc::new(Type::Int),
        Rc::new(Type::Type),
    )));
    match interpret(global, &val) {
        Ok(v) => assert_eq!(*v, expected),
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
    assert!(evals.len() == 1);

    let expected: Val = Val::Pair(
        Rc::new(Val::IntLit(6)),
        Rc::new(Val::Pair(Rc::new(Val::Unit), Rc::new(Val::IntLit(-1700)))),
    );
    match interpret(global, &evals[0]) {
        Ok(v) => assert_eq!(*v, expected),
        Err(e) => panic!("Interpretting reached error: {:?}", e),
    }
}

#[test]
fn test_interpret4() {
    let (names, global, evals) = make_program(
        "def fun Bool Int : f := fn Bool : b do match b case true do -10 case false do 31 end
            eval f true
            eval f false",
    )
    .expect("Failed to parse program");
    assert!(names.len() == 1);
    assert!(global.len() == 1);
    assert!(evals.len() == 2);

    let expected_0: Rc<Val> = Rc::new(Val::IntLit(-10));
    let expected_1: Rc<Val> = Rc::new(Val::IntLit(31));
    dbg!(&evals);
    match interpret(global.clone(), &evals[0]) {
        Ok(v) => assert_eq!(v, expected_0),
        Err(e) => panic!("Interpretting reached error: {:?}", e),
    }
    match interpret(global, &evals[1]) {
        Ok(v) => assert_eq!(v, expected_1),
        Err(e) => panic!("Interpretting reached error: {:?}", e),
    }
}

#[test]
fn test_interpret5() {
    let (names, global, evals) = make_program(
        "eval
            let Int: a := 7 in
            let Int : b := 19 in
            add a b",
    )
    .expect("Failed to parse program");
    assert!(names.len() == 0);
    assert!(global.len() == 0);
    assert!(evals.len() == 1);

    let expected: Val = Val::IntLit(26);
    match interpret(global, &evals[0]) {
        Ok(v) => assert_eq!(*v, expected),
        Err(e) => panic!("Interpretting reached error: {:?}", e),
    }
}
