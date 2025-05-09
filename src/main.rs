use std::env;
use std::fs::{File, OpenOptions};
use std::io::Read;
use std::iter::once;
use std::rc::Rc;
use std::str::SplitWhitespace;

#[derive(Debug, Clone)]
struct Binding {
    var_name: &'static str,
    type_sig: Expr,
    value: Expr,
}

#[derive(Debug, Clone)]
enum Expr {
    Apply(Rc<Expr>, Rc<Expr>),
    Variable(&'static str),
    IntLit(u64),
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum Keyword {
    Def,
    Fn,
    // Let,
    // Match,
    // On,
    Do,
    Eq,
    Colon,
}

// turns a sequence of numeric characters into an integer
// first character assumed to be a number, - or +
fn tokenize_number(numbers: &str) -> Option<Token> {
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

#[derive(Clone, Debug, PartialEq, Eq)]
enum Token {
    ParenL,
    ParenR,
    Identifier(String),
    Number(i64),
    Keyword(Keyword),
}

struct Tokens<'a> {
    src: SplitWhitespace<'a>,
    is_bad: bool,
    next_to_read: &'a str,
}

impl<'a> Iterator for Tokens<'a> {
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

        if first_char.is_alphabetic() {
            // this is a variable; find the end of the variable
            let mut idx: usize = self.next_to_read.len();
            for (i, char) in self.next_to_read.char_indices() {
                if !char.is_alphanumeric() {
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

fn tokenize<'a>(raw_src: &'a str) -> Tokens<'a> {
    let mut src = raw_src.split_whitespace();
    let next_to_read = src.next().unwrap();
    Tokens {
        src,
        is_bad: false,
        next_to_read,
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();

    let mut src_file: File = match args.get(1) {
        Some(f) => File::open(f).expect("Failed to open file :/"),
        None => return,
    };
    let mut src: String = String::new();
    src_file
        .read_to_string(&mut src)
        .expect("Something went wrong when reading the file :/");

    let tokens: Vec<Token> = tokenize(src.as_str()).collect();
    dbg!(tokens);
    // test_tokenize_number();
    // println!("Tests pass!")
}
