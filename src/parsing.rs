// hi

use std::{
    iter::{Peekable, once},
    str::SplitWhitespace,
};

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Keyword {
    Def,
    // Enum,
    Fn,
    // Let,
    // In,
    // Match,
    // Case,
    // End,
    Do,
    Eq,
    Colon,
}

// turns a sequence of numeric characters into an integer
// first character assumed to be a number, - or +
pub fn tokenize_number(numbers: &str) -> Option<Token> {
    // essentially /[+-]?[0-9]+/
    let mut chars: Box<dyn Iterator<Item = char>> = Box::new(numbers.chars());
    let first: char = chars.next()?;
    if first != '-' && first != '+' {
        // if the first character is not a sign, then append it to the beginning
        chars = Box::new(once(first).chain(chars));
    } else if numbers.len() == 1 {
        // If this is only a '+' or '-', parse it as an operator
        return Some(Token::Identifier(numbers.to_string()));
    }

    let mut number: i64 = 0;
    for digit in chars {
        let d = digit.to_digit(10)? as i64;
        number = (number * 10) + d;
    }

    Some(Token::Number(if first == '-' { -number } else { number }))
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Token {
    ParenL,
    ParenR,
    Identifier(String),
    Number(i64),
    Keyword(Keyword),
}

// TODO: allow for parsing strings
// TODO: swap SplitWhitespace with different system
// TODO: add comments
// TODO: allow for stuff like line numbers for error messages
pub struct Tokens<'a> {
    src: SplitWhitespace<'a>,
    is_bad: bool,
    next_to_read: &'a str,
}

impl<'a> Iterator for Tokens<'a> {
    // TODO: make this a Result for error messages
    type Item = Token;

    // in this function as we parse, we usually need to set self.next_to_read = ""
    // to show that we have eaten the input and actually parsed it
    fn next(&mut self) -> Option<Token> {
        // this doesnt account for things that are put *right* next to eachother

        while self.next_to_read.len() == 0 {
            self.next_to_read = self.src.next()?
        }
        // find next string which isnt empty

        match self.next_to_read {
            "def" => {
                self.next_to_read = "";
                return Some(Token::Keyword(Keyword::Def));
            }
            // "enum" => {
            //     self.next_to_read = "";
            //     return Some(Token::Keyword(Keyword::Let));
            // }
            // "let" => {
            //     self.next_to_read = "";
            //     return Some(Token::Keyword(Keyword::Let));
            // }
            // "match" => {
            //     self.next_to_read = "";
            //     return Some(Token::Keyword(Keyword::Match));
            // }
            // "case" => {
            //     self.next_to_read = "";
            //     return Some(Token::Keyword(Keyword::Case));
            // }
            "fn" => {
                self.next_to_read = "";
                return Some(Token::Keyword(Keyword::Fn));
            }
            "do" => {
                self.next_to_read = "";
                return Some(Token::Keyword(Keyword::Do));
            }
            ":=" => {
                self.next_to_read = "";
                return Some(Token::Keyword(Keyword::Eq));
            }
            ":" => {
                self.next_to_read = "";
                return Some(Token::Keyword(Keyword::Colon));
            }
            _ => (),
        }
        // self.next_to_read is guarenteed to have non-zero length here
        // because we check for that earlier
        let first_char: char = self.next_to_read.chars().next().unwrap();

        if first_char.is_numeric() || first_char == '-' || first_char == '+' {
            let parsed_str: Option<Token> = tokenize_number(self.next_to_read);
            self.next_to_read = "";
            return parsed_str;
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
            return Some(Token::Identifier(var.to_owned()));
        } else if first_char == ')' {
            self.next_to_read = &self.next_to_read[1..];
            return Some(Token::ParenR);
        } else if first_char == '(' {
            self.next_to_read = &self.next_to_read[1..];
            return Some(Token::ParenL);
        } else {
            self.is_bad = true;
            return None;
        }
    }
}

pub fn tokenize<'a>(raw_src: &'a str) -> Tokens<'a> {
    let mut src = raw_src.split_whitespace();
    let next_to_read = src.next().unwrap();
    Tokens {
        src,
        is_bad: false,
        next_to_read,
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Apply(Box<Expr>, Box<Expr>),
    Function {
        name: String,
        input_type: Box<Expr>,
        output: Box<Expr>,
    },
    Variable(String),
    IntLit(i64),
    Unit,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Binding {
    pub(crate) var_name: String,
    // TODO: make type_sig optional
    pub(crate) type_sig: Expr,
    pub(crate) value: Expr,
}

pub enum Command {
    Binding(Binding),
}

pub struct Parser<T>
where
    T: Iterator<Item = Token>,
{
    tokens: Peekable<T>,
}

impl<T> Iterator for Parser<T>
where
    T: Iterator<Item = Token>,
{
    // TODO: make this a result for better errors
    type Item = Command;

    fn next(&mut self) -> Option<Command> {
        // assert that the first word was def
        match self.tokens.next()? {
            Token::Keyword(Keyword::Def) => self.parse_binding().map(Command::Binding),
            _ => None,
        }
    }
}

impl<T> Parser<T>
where
    T: Iterator<Item = Token>,
{
    // TODO: make this a result type
    fn parse_expr(&mut self) -> Option<Expr> {
        // helper function for thing
        fn push_as_arg(paren_stack: &mut Vec<Expr>, arg: Expr) {
            match paren_stack.pop() {
                Some(e) => paren_stack.push(Expr::Apply(Box::new(e), Box::new(arg))),
                None => paren_stack.push(arg),
            }
        }

        let mut paren_stack: Vec<Expr> = Vec::new();
        let mut depth: u32 = 0;
        loop {
            // println!(
            //     "Now accepting token: {:?}\nparen_stack = {:?}",
            //     self.tokens.peek(),
            //     paren_stack
            // );
            match self.tokens.peek() {
                None => break,
                Some(Token::Keyword(Keyword::Def)) => break,
                Some(Token::Keyword(Keyword::Eq)) => break,
                Some(Token::Keyword(Keyword::Colon)) => break,
                Some(Token::Identifier(s)) => {
                    push_as_arg(&mut paren_stack, Expr::Variable(s.clone()));
                    self.tokens.next(); // eat token
                }
                Some(Token::Number(n)) => {
                    push_as_arg(&mut paren_stack, Expr::IntLit(*n));
                    self.tokens.next(); // eat token
                }
                Some(Token::ParenL) => {
                    depth += 1;
                    self.tokens.next(); // eat token
                    let next_atom: Expr = loop {
                        match self.tokens.next()? {
                            Token::Identifier(s) => break Expr::Variable(s),
                            Token::Number(n) => break Expr::IntLit(n),
                            Token::ParenL => {
                                depth += 1;
                                continue;
                            }
                            Token::ParenR => break Expr::Unit,
                            _ => return None,
                        }
                    };
                    paren_stack.push(next_atom);
                }
                Some(Token::ParenR) => {
                    if depth == 0 {
                        break;
                    };
                    depth -= 1;
                    self.tokens.next(); // eat this token
                    let arg = paren_stack.pop()?;
                    push_as_arg(&mut paren_stack, arg);
                }
                Some(Token::Keyword(Keyword::Fn)) => {
                    self.tokens.next(); // eat token
                    let input_type = self.parse_expr()?;
                    match self.tokens.next() {
                        Some(Token::Keyword(Keyword::Colon)) => (),
                        _ => return None,
                    };
                    let name = match self.tokens.next() {
                        Some(Token::Identifier(s)) => s,
                        _ => return None,
                    };

                    match self.tokens.next() {
                        Some(Token::Keyword(Keyword::Do)) => (),
                        _ => return None,
                    };

                    let output = self.parse_expr()?;

                    push_as_arg(
                        &mut paren_stack,
                        Expr::Function {
                            name,
                            input_type: Box::new(input_type),
                            output: Box::new(output),
                        },
                    )
                }
                _ => return None,
            }
        }

        // I think this technically allows for expressions like `f (2 (5 4`
        // which I think is okay because you know what is meant by this and closing parentheses is often a nightmare
        let mut final_expr = paren_stack.pop()?;
        while let Some(expr) = paren_stack.pop() {
            final_expr = Expr::Apply(Box::new(expr), Box::new(final_expr));
        }

        return Some(final_expr);
    }

    // TODO: make this a result
    fn parse_binding(&mut self) -> Option<Binding> {
        let type_sig: Expr = self.parse_expr()?;

        match self.tokens.next()? {
            Token::Keyword(Keyword::Colon) => (),
            _ => return None,
        }

        // assert that the next word was an identifier. This is where we would parse a pattern
        // when we add those
        let Token::Identifier(name) = self.tokens.next()? else {
            return None;
        };
        match self.tokens.next()? {
            Token::Keyword(Keyword::Eq) => (),
            _ => return None,
        }

        let value: Expr = self.parse_expr()?;

        return Some(Binding {
            var_name: name,
            type_sig,
            value,
        });
    }
}

pub fn parse<T>(tokens: T) -> Parser<T>
where
    T: Iterator<Item = Token>,
{
    Parser {
        tokens: tokens.peekable(),
    }
}

pub fn parse_src(src: &str) -> Vec<Command> {
    let tokens = tokenize(&src);
    return parse(tokens).collect();
}
