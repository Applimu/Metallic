use std::{collections::HashMap, iter::Peekable, str::Chars};

use crate::resolve::UnresolvedExpr;

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

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Token {
    ParenL,
    ParenR,
    Identifier(String),
    Stringlit(String),
    Number(i64),
    Keyword(Keyword),
}

// TODO: add parsing strings
// TODO: add a way to obtain line numbers for error messages
#[derive(Debug, Clone)]
pub struct Tokens<'a> {
    src: &'a str,
    next_to_read: &'a str,
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
}

// turns a sequence of numeric characters into an integer
// first character must be a number, '-' or '+'
pub fn tokenize_number<'a>(numbers: &'a str) -> (Result<Token, ParseError<'a>>, &'a str) {
    // essentially /[+-]?[0-9]*/
    let mut chars: Peekable<Chars<'a>> = numbers.chars().peekable();
    let first: char = match chars.peek() {
        Some(c) => *c,
        None => return (Err(ParseError::NotANumber(&numbers)), numbers),
    };
    if first == '-' || first == '+' {
        chars.next();
        if numbers.len() == 1 {
            // If this is only a '+' or '-', parse it as an operator
            return (Ok(Token::Identifier(numbers.to_string())), "");
        }
    } else if !first.is_numeric() && first != '-' && first != '+' {
        return (Err(ParseError::NotANumber(numbers)), numbers);
    }

    let mut number: i64 = 0;
    let mut chars_eaten = if first == '-' || first == '+' { 1 } else { 0 };
    for digit in chars {
        match digit.to_digit(10) {
            Some(d) => {
                chars_eaten += 1;
                number = (number * 10) + (d as i64);
            }
            None => {
                break;
            }
        }
    }

    (
        Ok(Token::Number(if first == '-' { -number } else { number })),
        &numbers[chars_eaten..],
    )
}

fn try_as_keyword<'a>(kwd: &'a str) -> Option<Keyword> {
    match kwd {
        "def" => Some(Keyword::Def),
        "eval" => Some(Keyword::Eval),
        "enum" => Some(Keyword::Enum),
        "fn" => Some(Keyword::Fn),
        "let" => Some(Keyword::Let),
        "in" => Some(Keyword::In),
        "match" => Some(Keyword::Match),
        "case" => Some(Keyword::Case),
        "end" => Some(Keyword::End),
        "do" => Some(Keyword::Do),
        ":=" => Some(Keyword::Eq),
        ":" => Some(Keyword::Colon),
        _ => None,
    }
}

impl<'a> Iterator for Tokens<'a> {
    type Item = Result<Token, ParseError<'a>>;

    // in this function as we parse, we usually need to set self.next_to_read = ""
    // to show that we have eaten the input and actually parsed it
    fn next(&mut self) -> Option<Result<Token, ParseError<'a>>> {
        while self.next_to_read.len() == 0 {
            self.next_to_read = self.next_nowhitespace_substr()?;
        }

        if &self.next_to_read[0..1] == "\"" {
            println!("FOUND STRING: {}", self.next_to_read);
            let last_idx = self.next_to_read.len() - 1;
            assert_eq!("\"", &self.next_to_read[last_idx..last_idx + 1]);
            if last_idx == 0 {
                panic!("String has no closing parentheses");
            }
            let new_str = if last_idx == 1 {
                String::new()
            } else {
                self.next_to_read[1..last_idx].to_string()
            };
            self.next_to_read = "";
            return Some(Ok(Token::Stringlit(new_str)));
        }

        // self.next_to_read is a non-empty string with no whitespace characters
        if let Some(kwd) = try_as_keyword(&self.next_to_read) {
            self.next_to_read = "";
            return Some(Ok(Token::Keyword(kwd)));
        }

        let first_char: char = self.next_to_read.chars().next().unwrap();

        if first_char.is_numeric() || first_char == '-' || first_char == '+' {
            let result = tokenize_number(&self.next_to_read);
            self.next_to_read = result.1;
            return Some(result.0);
        }

        if first_char.is_alphabetic() || first_char == '_' {
            // this is a variable; find the end of the variable
            let mut idx: usize = self.next_to_read.len();
            for (i, char) in self.next_to_read.char_indices() {
                if !char.is_alphanumeric() && char != '_' {
                    idx = i;
                    break;
                }
            }
            let (var, rest) = self.next_to_read.split_at(idx);
            self.next_to_read = rest;
            return Some(Ok(Token::Identifier(var.to_owned())));
        } else if first_char == ')' {
            self.next_to_read = &self.next_to_read[1..];
            return Some(Ok(Token::ParenR));
        } else if first_char == '(' {
            self.next_to_read = &self.next_to_read[1..];
            return Some(Ok(Token::ParenL));
        } else {
            return Some(Err(ParseError::UnrecognizedToken(self.next_to_read)));
        }
    }
}

impl<'a> Tokens<'a> {
    // returns the next chunk of code without any whitespace
    // skips over comments and whitespace, and returns strings separately.
    fn next_nowhitespace_substr(&mut self) -> Option<&'a str> {
        if self.src.len() == 0 {
            return None;
        };
        let mut iterator = self.src.char_indices();
        // first find next character which is not whitespace and not commented out
        let begin_idx: usize = loop {
            let (idx, chr) = iterator.next()?;
            if !chr.is_whitespace() {
                if self.src.get(idx..idx + 2) == Some("//") {
                    while iterator.next()?.1 != '\n' {
                        continue;
                    }
                    continue;
                }
                break idx;
            }
        };
        println!("HI");

        // If the first valid non-whitespace character is a ", then this
        // is a string.
        if &self.src[begin_idx..begin_idx + 1] == "\"" {
            loop {
                // TODO: make this cause an error rather than just a None
                let (idx, chr) = iterator.next()?;
                if chr == '"' {
                    let new_chunk = &self.src[begin_idx..idx + 1];
                    self.src = &self.src[idx + 1..];
                    return Some(new_chunk);
                }
            }
        }

        // Otherwise we just keep going until we find whitespace or the beginning of a comment
        let end_idx: usize = loop {
            if let Some((idx, chr)) = iterator.next() {
                if chr.is_whitespace() || chr == '"' || self.src.get(idx..idx + 2) == Some("//") {
                    break idx;
                };
            } else {
                // if we've found the end of the program we just return
                // the final chunk
                let new_chunk = &self.src[begin_idx..];
                self.src = "";
                return Some(new_chunk);
            }
        };

        let new_chunk: &'a str = &self.src[begin_idx..end_idx];
        self.src = &self.src[end_idx..];
        Some(new_chunk)
    }
}

pub fn tokenize<'a>(raw_src: &'a str) -> Tokens<'a> {
    Tokens {
        src: raw_src,
        next_to_read: "",
    }
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
    pub matchend: String,
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
        match self.parse_command() {
            Err(ParseError::UnexpectedEOF) => None,
            otherwise => Some(otherwise),
        }
    }
}

// helper function for Parser::parse_expr and Parser::parse_inside_parens.
fn push_as_arg(paren_stack: &mut Vec<UnresolvedExpr>, arg: UnresolvedExpr) {
    match paren_stack.pop() {
        Some(e) => paren_stack.push(UnresolvedExpr::Apply(Box::new(e), Box::new(arg))),
        None => paren_stack.push(arg),
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
    fn expect_identifier(&mut self) -> Result<String, ParseError<'a>> {
        let next_token = self.get_next_token()?;
        if let Token::Identifier(str) = next_token {
            Ok(str)
        } else {
            Err(ParseError::UnexpectedToken(next_token))
        }
    }

    fn expect_keyword(&mut self, kwd: Keyword) -> Result<(), ParseError<'a>> {
        let next_token = self.get_next_token()?;
        if next_token != Token::Keyword(kwd) {
            Err(ParseError::UnexpectedToken(next_token))
        } else {
            Ok(())
        }
    }

    pub fn parse_expr(&mut self) -> Result<UnresolvedExpr, ParseError<'a>> {
        let mut paren_stack: Vec<UnresolvedExpr> = Vec::new();
        let mut depth: u32 = 0;
        loop {
            // println!(
            //     "Now accepting token: {:?}\nparen_stack = {:?}",
            //     self.tokens.peek(),
            //     paren_stack
            // );
            match self.peek_next_token()? {
                None => break,
                Some(Token::Keyword(Keyword::Def)) => break,
                Some(Token::Keyword(Keyword::Enum)) => break,
                Some(Token::Keyword(Keyword::Eval)) => break,
                Some(Token::Keyword(Keyword::Eq)) => break,
                Some(Token::Keyword(Keyword::Case)) => break,
                Some(Token::Keyword(Keyword::End)) => break,
                Some(Token::Keyword(Keyword::Colon)) => break,
                Some(Token::Keyword(Keyword::In)) => break,
                Some(Token::Keyword(Keyword::Do)) => {
                    return Err(ParseError::UnexpectedToken(Token::Keyword(Keyword::Do)));
                }
                Some(Token::Identifier(s)) => {
                    push_as_arg(&mut paren_stack, UnresolvedExpr::Variable(s.clone()));
                    self.tokens.next(); // eat token
                }
                Some(Token::Number(n)) => {
                    push_as_arg(&mut paren_stack, UnresolvedExpr::IntLit(*n));
                    self.tokens.next(); // eat token
                }
                Some(Token::Stringlit(s)) => {
                    push_as_arg(&mut paren_stack, UnresolvedExpr::StringLit(s.clone()));
                    self.tokens.next(); // eat token
                }
                Some(Token::ParenL) => {
                    depth += 1;
                    self.tokens.next(); // eat token
                    self.parse_inside_parens(&mut paren_stack, &mut depth)?;
                }
                Some(Token::ParenR) => {
                    if depth == 0 {
                        break;
                    };
                    depth -= 1;
                    self.tokens.next(); // eat this token
                    let arg = paren_stack.pop().ok_or(ParseError::BadParenR)?;
                    push_as_arg(&mut paren_stack, arg);
                }
                Some(Token::Keyword(Keyword::Fn)) => {
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
                Some(Token::Keyword(Keyword::Match)) => {
                    let match_statement = UnresolvedExpr::Match(self.parse_match()?);
                    push_as_arg(&mut paren_stack, match_statement)
                }
                Some(Token::Keyword(Keyword::Let)) => {
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
        let mut final_expr = paren_stack.pop().ok_or(ParseError::EmptyExpression)?;
        while let Some(expr) = paren_stack.pop() {
            final_expr = UnresolvedExpr::Apply(Box::new(expr), Box::new(final_expr));
        }

        return Ok(final_expr);
    }

    // parses parentheses until it is able to push something onto the paren_stack
    fn parse_inside_parens(
        &mut self,
        paren_stack: &mut Vec<UnresolvedExpr>,
        depth: &mut u32,
    ) -> Result<(), ParseError<'a>> {
        assert!(*depth != 0);
        loop {
            match self.get_next_token()? {
                Token::Identifier(s) => {
                    paren_stack.push(UnresolvedExpr::Variable(s));
                    break;
                }
                Token::Number(n) => {
                    paren_stack.push(UnresolvedExpr::IntLit(n));
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
                    paren_stack.push(UnresolvedExpr::Function {
                        name,
                        input_type: Box::new(input_type),
                        output: Box::new(output),
                    });
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
        // println!("PARSING MATCH STATEMENT!");
        self.expect_keyword(Keyword::Match)?;

        // println!("MATCH TOKEN ACCEPTED -- READING IDENTIFIER");
        let matchend: String = self.expect_identifier()?;
        // println!("MATCHEND: {} ACCEPTED -- READING CASES", matchend);

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

    fn parse_command(&mut self) -> Result<Command, ParseError<'a>> {
        // the first word always says what kind of command it is
        let Some(next_token_res) = self.tokens.next() else {
            return Err(ParseError::UnexpectedEOF);
        };
        match next_token_res? {
            Token::Keyword(Keyword::Def) => self.parse_binding().map(Command::Definition),
            Token::Keyword(Keyword::Eval) => self.parse_expr().map(Command::Eval),
            Token::Keyword(Keyword::Enum) => match self.parse_enum() {
                Ok((name, variants)) => Ok(Command::Enum(name, variants)),
                Err(e) => Err(e),
            },
            t => Err(ParseError::UnexpectedToken(t)),
        }
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

    let mut commands = Vec::new();
    for command in parse(&mut tokens) {
        commands.push(command?)
    }
    Ok(commands)
}
