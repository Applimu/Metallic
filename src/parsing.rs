use std::{collections::HashMap, iter::Peekable};

use crate::{
    resolve::UnresolvedExpr,
    tokenize::{Operator, Token, tokenize},
};

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Keyword {
    Def,
    Enum,
    Fn,
    Eval,
    Let,
    In,
    Match,
    Case,
    End,
    Do,
    Eq,
    Colon,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParseError<'a> {
    NotANumber(&'a str),
    UnexpectedToken(Token),
    UnexpectedEOF,
    BadParenL,
    BadParenR,
    EmptyExpression,
    UnrecognizedToken(&'a str),
    // honestly this probably falls more under a resolve error
    // than a parse error
    CaseNameCollision(String),
    NoRHS(Operator),
    MultipleOperators(Operator, Operator),
}

// code which is of the form <Expr>: <name> := <Expr>
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Binding {
    pub var_name: String,
    // TODO: make type_sig optional
    pub type_sig: UnresolvedExpr,
    pub value: UnresolvedExpr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Matching {
    pub matchend: Box<UnresolvedExpr>,
    pub branches: HashMap<String, UnresolvedExpr>,
}

// A command to the compiler to do something
#[derive(Debug, PartialEq, Eq)]
pub enum Command {
    // Define a new global variable
    Definition(Binding),
    // Interpret an expression
    Eval(UnresolvedExpr),
    // Define a new enum type
    Enum(String, Vec<String>),
}

pub struct Parser<'a, T>
where
    T: Iterator<Item = Result<Token, ParseError<'a>>>,
{
    tokens: Peekable<T>,
}

impl<'a, T> Iterator for Parser<'a, T>
where
    T: Iterator<Item = Result<Token, ParseError<'a>>>,
{
    type Item = Result<Command, ParseError<'a>>;

    fn next(&mut self) -> Option<Result<Command, ParseError<'a>>> {
        self.parse_command()
    }
}

// helper function for Parser::parse_expr and Parser::parse_inside_parens.
fn push_as_arg(paren_stack: &mut Vec<(UnresolvedExpr, Option<Operator>)>, arg: UnresolvedExpr) {
    match paren_stack.pop() {
        Some((e, None)) => {
            paren_stack.push((UnresolvedExpr::Apply(Box::new(e), Box::new(arg)), None))
        }
        Some((e, Some(o))) => paren_stack.push((
            UnresolvedExpr::Operator(Box::new(e), o, Box::new(arg)),
            None,
        )),
        None => paren_stack.push((arg, None)),
    }
}

impl<'a, T> Parser<'a, T>
where
    T: Iterator<Item = Result<Token, ParseError<'a>>>,
{
    fn get_next_token(&mut self) -> Result<Token, ParseError<'a>> {
        self.tokens.next().ok_or(ParseError::UnexpectedEOF)?
    }
    fn peek_next_token(&mut self) -> Result<Option<&Token>, ParseError<'a>> {
        match self.tokens.peek() {
            Some(Ok(t)) => Ok(Some(t)),
            Some(Err(e)) => Err(e.clone()),
            None => Ok(None),
        }
    }
    /// Expect an identifier, and eat it, returning the identifier as a `String`. Returns `UnexpectedToken` otherwise
    fn expect_identifier(&mut self) -> Result<String, ParseError<'a>> {
        let next_token = self.get_next_token()?;
        if let Token::Identifier(str) = next_token {
            Ok(str)
        } else {
            Err(ParseError::UnexpectedToken(next_token))
        }
    }

    /// Expect the provided keyword, and eat it. Returns `UnexpectedToken` otherwise
    fn expect_keyword(&mut self, kwd: Keyword) -> Result<(), ParseError<'a>> {
        let next_token = self.get_next_token()?;
        if next_token != Token::Keyword(kwd) {
            Err(ParseError::UnexpectedToken(next_token))
        } else {
            Ok(())
        }
    }

    /// Parses an expression. Returns the expression when it reaches an unexpected keyword
    /// or when it parses all remaining tokens.
    pub fn parse_expr(&mut self) -> Result<UnresolvedExpr, ParseError<'a>> {
        let mut paren_stack: Vec<(UnresolvedExpr, Option<Operator>)> = Vec::new();
        let mut depth: u32 = 0;
        while let Some(tok) = self.peek_next_token()? {
            match tok {
                Token::Keyword(Keyword::Def) => break,
                Token::Keyword(Keyword::Enum) => break,
                Token::Keyword(Keyword::Eval) => break,
                Token::Keyword(Keyword::Eq) => break,
                Token::Keyword(Keyword::Case) => break,
                Token::Keyword(Keyword::End) => break,
                Token::Keyword(Keyword::Colon) => break,
                Token::Keyword(Keyword::In) => break,
                Token::Keyword(Keyword::Do) => {
                    return Err(ParseError::UnexpectedToken(Token::Keyword(Keyword::Do)));
                }
                Token::Identifier(s) => {
                    push_as_arg(&mut paren_stack, UnresolvedExpr::Variable(s.clone()));
                    self.tokens.next(); // eat token
                }
                Token::Number(n) => {
                    push_as_arg(&mut paren_stack, UnresolvedExpr::IntLit(*n));
                    self.tokens.next(); // eat token
                }
                Token::Stringlit(s) => {
                    push_as_arg(&mut paren_stack, UnresolvedExpr::StringLit(s.clone()));
                    self.tokens.next(); // eat token
                }
                Token::Operator(op) => {
                    let (_, mb_op) = paren_stack
                        .last_mut()
                        .expect("Found prefix operator unexpectedly");
                    match mb_op {
                        None => {
                            *mb_op = Some(op.clone());
                        }
                        Some(op2) => {
                            return Err(ParseError::MultipleOperators(op.clone(), op2.clone()));
                        }
                    }
                    self.tokens.next(); // eat token
                }
                Token::ParenL => {
                    depth += 1;
                    self.tokens.next(); // eat token
                    self.parse_inside_parens(&mut paren_stack, &mut depth)?;
                }
                Token::ParenR => {
                    if depth == 0 {
                        break;
                    };
                    depth -= 1;
                    self.tokens.next(); // eat this token
                    let (arg, _) = paren_stack.pop().ok_or(ParseError::BadParenR)?;
                    push_as_arg(&mut paren_stack, arg);
                }
                Token::Keyword(Keyword::Fn) => {
                    self.tokens.next(); // eat token
                    let input_type = self.parse_expr()?;
                    self.expect_keyword(Keyword::Colon)?;
                    let name = self.expect_identifier()?;

                    self.expect_keyword(Keyword::Do)?;

                    let output = self.parse_expr()?;

                    push_as_arg(
                        &mut paren_stack,
                        UnresolvedExpr::Function {
                            name,
                            input_type: Box::new(input_type),
                            output: Box::new(output),
                        },
                    )
                }
                Token::Keyword(Keyword::Match) => {
                    let match_statement = UnresolvedExpr::Match(self.parse_match()?);
                    push_as_arg(&mut paren_stack, match_statement)
                }
                Token::Keyword(Keyword::Let) => {
                    self.tokens.next(); // eat let token
                    let binding = self.parse_binding()?;

                    self.expect_keyword(Keyword::In)?;
                    let expr = self.parse_expr()?;
                    push_as_arg(
                        &mut paren_stack,
                        UnresolvedExpr::Let(Box::new(binding), Box::new(expr)),
                    );
                }
            }
        }

        // I think this technically allows for expressions like `f (2 (5 4`
        // which I think is okay because you know what is meant by this and
        // closing parentheses is often a nightmare
        let (mut final_expr, op) = paren_stack.pop().ok_or(ParseError::EmptyExpression)?;
        match op {
            Some(op) => return Err(ParseError::NoRHS(op)),
            None => (),
        }

        while let Some((expr, mb_op)) = paren_stack.pop() {
            match mb_op {
                Some(_) => panic!("Dont know how to resolve operators like this :/"),
                None => {
                    final_expr = UnresolvedExpr::Apply(Box::new(expr), Box::new(final_expr));
                }
            }
        }

        return Ok(final_expr);
    }

    /// Parses parentheses until it is able to push something onto the paren_stack, and
    /// then returns with a depth equal to one greater. Also handles things like `()` and
    /// Expects the caller to raise the depth by 1 before calling
    fn parse_inside_parens(
        &mut self,
        paren_stack: &mut Vec<(UnresolvedExpr, Option<Operator>)>,
        depth: &mut u32,
    ) -> Result<(), ParseError<'a>> {
        assert!(*depth != 0);
        loop {
            match self.get_next_token()? {
                Token::Identifier(s) => {
                    paren_stack.push((UnresolvedExpr::Variable(s), None));
                    break;
                }
                Token::Number(n) => {
                    paren_stack.push((UnresolvedExpr::IntLit(n), None));
                    break;
                }
                Token::ParenL => {
                    *depth += 1;
                    continue;
                }
                Token::ParenR => {
                    *depth -= 1;
                    push_as_arg(paren_stack, UnresolvedExpr::Unit);
                    break;
                }
                Token::Keyword(Keyword::Fn) => {
                    // just parse the function here. not the best solution
                    let input_type = self.parse_expr()?;
                    self.expect_keyword(Keyword::Colon)?;
                    let name = self.expect_identifier()?;

                    self.expect_keyword(Keyword::Do)?;

                    let output = self.parse_expr()?;
                    paren_stack.push((
                        UnresolvedExpr::Function {
                            name,
                            input_type: Box::new(input_type),
                            output: Box::new(output),
                        },
                        None,
                    ));
                    break;
                }
                bad_token => return Err(ParseError::UnexpectedToken(bad_token)),
            }
        }
        Ok(())
    }

    fn parse_binding(&mut self) -> Result<Binding, ParseError<'a>> {
        let type_sig: UnresolvedExpr = self.parse_expr()?;

        self.expect_keyword(Keyword::Colon)?;
        let name = self.expect_identifier()?;
        self.expect_keyword(Keyword::Eq)?;

        let value: UnresolvedExpr = self.parse_expr()?;

        return Ok(Binding {
            var_name: name,
            type_sig,
            value,
        });
    }

    fn parse_match(&mut self) -> Result<Matching, ParseError<'a>> {
        self.expect_keyword(Keyword::Match)?;

        let matchend = Box::new(self.parse_expr()?);

        let mut branches: HashMap<String, UnresolvedExpr> = HashMap::new();
        while !matches!(self.peek_next_token()?, Some(Token::Keyword(Keyword::End))) {
            self.expect_keyword(Keyword::Case)?;

            let case_name: String = self.expect_identifier()?;
            if branches.contains_key(&case_name) {
                return Err(ParseError::CaseNameCollision(case_name));
            }

            self.expect_keyword(Keyword::Do)?;

            let expr = self.parse_expr()?;
            branches.insert(case_name, expr);
        }
        // eat final `end` token
        self.get_next_token()?;

        Ok(Matching { matchend, branches })
    }

    fn parse_enum(&mut self) -> Result<(String, Vec<String>), ParseError<'a>> {
        let name = match self.get_next_token()? {
            Token::Identifier(s) => s,
            t => return Err(ParseError::UnexpectedToken(t)),
        };
        let mut variants = Vec::new();
        while let Some(Token::Identifier(_)) = self.peek_next_token()? {
            variants.push(self.expect_identifier()?);
        }
        Ok((name, variants))
    }

    /// Attempts to parse a command. If there are no more tokens to parse
    /// it instead returns `None`
    fn parse_command(&mut self) -> Option<Result<Command, ParseError<'a>>> {
        // the first word always says what kind of command it is
        let Some(next_token_res) = self.tokens.next() else {
            return None;
        };
        let token = match next_token_res {
            Ok(t) => t,
            Err(e) => return Some(Err(e)),
        };
        Some(match token {
            Token::Keyword(Keyword::Def) => self.parse_binding().map(Command::Definition),
            Token::Keyword(Keyword::Eval) => self.parse_expr().map(Command::Eval),
            Token::Keyword(Keyword::Enum) => self
                .parse_enum()
                .map(|(name, variants)| Command::Enum(name, variants)),
            t => Err(ParseError::UnexpectedToken(t)),
        })
    }
}

pub fn parse<'a, T>(tokens: T) -> Parser<'a, T>
where
    T: Iterator<Item = Result<Token, ParseError<'a>>>,
{
    Parser {
        tokens: tokens.peekable(),
    }
}

pub fn parse_src<'a>(src: &'a str) -> Result<Vec<Command>, ParseError<'a>> {
    let mut tokens = tokenize(&src);

    let res: Result<Vec<_>, _> = parse(&mut tokens).collect();
    // At this point we have either eaten all the source code or we have arrived at an error
    assert!(
        tokens.src.len() == 0 || res.is_err(),
        "TOKENS SOURCE (length {}): \n{}\n\nAST CREATED:\n{:?}",
        tokens.src.len(),
        tokens.src,
        res
    );
    return res;
}
