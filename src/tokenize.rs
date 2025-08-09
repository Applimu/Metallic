use std::{iter::Peekable, str::Chars};

use crate::parsing::{Keyword, ParseError};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Token {
    ParenL,
    ParenR,
    Identifier(String),
    Stringlit(String),
    Number(i64),
    Keyword(Keyword),
    Operator(Operator),
}

// TODO: add a way to obtain line numbers for error messages
#[derive(Debug, Clone)]
pub struct Tokens<'a> {
    pub src: &'a str,
    pub next_to_read: &'a str,
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Operator(pub String);

/// Returns `true` iff the character is to be interpretted as part of an operator
fn is_operator_char(c: char) -> bool {
    match c {
        '+' | '-' | '<' | '>' | '=' | '!' | '*' => true,
        _ => false,
    }
}
/// Returns the string as an `Operator` if the language considers it to be an operator
fn try_as_operator(op: &str) -> Option<Operator> {
    if op.len() == 0 {
        return None;
    };
    if op.chars().all(|c| is_operator_char(c)) {
        Some(Operator(String::from(op)))
    } else {
        None
    }
}

fn try_as_keyword<'a>(kwd: &'a str) -> Option<Keyword> {
    Some(match kwd {
        "def" => Keyword::Def,
        "eval" => Keyword::Eval,
        "enum" => Keyword::Enum,
        "fn" => Keyword::Fn,
        "let" => Keyword::Let,
        "in" => Keyword::In,
        "match" => Keyword::Match,
        "case" => Keyword::Case,
        "end" => Keyword::End,
        "do" => Keyword::Do,
        ":=" => Keyword::Eq,
        ":" => Keyword::Colon,
        _ => return None,
    })
}

impl<'a> Iterator for Tokens<'a> {
    type Item = Result<Token, ParseError<'a>>;

    // in this function as we parse, we usually need to set self.next_to_read = ""
    // to show that we have eaten the input and actually parsed it
    fn next(&mut self) -> Option<Result<Token, ParseError<'a>>> {
        while self.next_to_read.len() == 0 {
            self.next_to_read = match self.next_nowhitespace_substr() {
                None => {
                    self.src = "";
                    return None;
                }
                Some(s) => s,
            };
        }
        println!("PROCESSING: \"{}\"", self.next_to_read);

        if &self.next_to_read[0..1] == "\"" {
            let last_idx = self.next_to_read.len() - 1;
            assert_eq!("\"", &self.next_to_read[last_idx..last_idx + 1]);
            if last_idx == 0 {
                panic!("String has no closing quotation");
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

        if let Some(o) = try_as_operator(self.next_to_read) {
            self.next_to_read = "";
            return Some(Ok(Token::Operator(o)));
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
    /// Returns the next chunk of code without any whitespace
    /// skips over any comments and whitespace, and returns strings separately.
    /// There technically *can* be whitespace in the result, but this is only if the returned
    /// value is a string. Returns `None` if there is nothing more to return
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
