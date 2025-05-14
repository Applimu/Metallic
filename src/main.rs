use std::env;
use std::fs::File;
use std::io::Read;
use std::iter::{Peekable, once};
use std::str::SplitWhitespace;

#[cfg(test)]
mod tests;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Keyword {
    Def,
    // Enum,
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
pub struct Binding {
    var_name: String,
    // TODO: make type_sig optional i.e. add type inferrence
    type_sig: Expr,
    value: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Apply(Box<Expr>, Box<Expr>),
    Variable(String),
    IntLit(i64),
    Unit,
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
    // TODO: Replace `Binding` here with `Command` to allow for more commands such as enum
    type Item = Binding;

    fn next(&mut self) -> Option<Binding> {
        // assert that the first word was def
        match self.tokens.next()? {
            Token::Keyword(Keyword::Def) => self.parse_binding(),
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
        let mut paren_stack: Vec<Expr> = Vec::new();

        // helper function for thing
        fn push_as_arg(paren_stack: &mut Vec<Expr>, arg: Expr) {
            match paren_stack.pop() {
                Some(e) => paren_stack.push(Expr::Apply(Box::new(e), Box::new(arg))),
                None => paren_stack.push(arg),
            }
        }

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
                    self.tokens.next(); // eat token
                    let next_atom: Expr = loop {
                        match self.tokens.next()? {
                            Token::Identifier(s) => break Expr::Variable(s),
                            Token::Number(n) => break Expr::IntLit(n),
                            Token::ParenL => continue,
                            Token::ParenR => break Expr::Unit,
                            _ => return None,
                        }
                    };
                    paren_stack.push(next_atom);
                }
                Some(Token::ParenR) => {
                    self.tokens.next(); // eat this token
                    let arg = paren_stack.pop()?;
                    push_as_arg(&mut paren_stack, arg);
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

// an expression where each name is known
#[derive(Debug, Clone, PartialEq, Eq)]
enum ResolvedExpr {
    Apply(Box<ResolvedExpr>, Box<ResolvedExpr>),
    // reference to another defined value as index in the grid
    Ref(usize),
    // reference to internally defined value
    Internal(usize),
    IntLit(i64),
    Unit,
}

// a type/value pair where each name is known
#[derive(Debug, Clone)]
pub struct ResolvedDefinition {
    type_sig: ResolvedExpr,
    value: ResolvedExpr,
}

pub struct InternalValue {
    name: &'static str,
    val: RuntimeVal,
}

// all the names that are resolved internally
pub const INTERNAL_VALUES: [InternalValue; 4] = [
    InternalValue {
        name: "Type",
        val: RuntimeVal::Type(Type::Type),
    },
    InternalValue {
        name: "Int",
        val: RuntimeVal::Type(Type::Int),
    },
    InternalValue {
        name: "add",
        val: RuntimeVal::Add,
    },
    InternalValue {
        name: "print_int",
        val: RuntimeVal::PrintInt,
    },
];

// TODO: make this a result
fn resolve_expr(names: &[String], expr: Expr) -> Option<ResolvedExpr> {
    match expr {
        Expr::Apply(func, arg) => {
            let rfunc = Box::new(resolve_expr(names, *func)?);
            let rarg = Box::new(resolve_expr(names, *arg)?);
            Some(ResolvedExpr::Apply(rfunc, rarg))
        }
        Expr::Variable(s) => {
            for (i, internal) in INTERNAL_VALUES.iter().enumerate() {
                println!("Testing {} against {} !!", &s, internal.name);
                if internal.name == &s {
                    return Some(ResolvedExpr::Internal(i));
                }
            }
            for (i, name) in names.iter().enumerate() {
                if *name == s {
                    return Some(ResolvedExpr::Ref(i));
                }
            }
            // if the variable name is not an internal value or another name, crash
            None
        }
        Expr::IntLit(n) => Some(ResolvedExpr::IntLit(n)),
        Expr::Unit => Some(ResolvedExpr::Unit),
    }
}

fn resolve_bindings(ast1: &Vec<Binding>) -> Option<Vec<ResolvedDefinition>> {
    let names: Vec<String> = (ast1).into_iter().map(|b| b.var_name.clone()).collect();
    dbg!(&names);
    let mut resolved_program: Vec<ResolvedDefinition> = Vec::new();
    for b in ast1 {
        dbg!(&b);
        let rtype_sig = resolve_expr(&names, b.type_sig.clone())?;
        dbg!(&rtype_sig);
        let rvalue = resolve_expr(&names, b.value.clone())?;
        dbg!(&rvalue);
        resolved_program.push(ResolvedDefinition {
            type_sig: rtype_sig,
            value: rvalue,
        });
    }
    Some(resolved_program)
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    Type,
    Int,
    Unit,
    Bool,
    FunctionType(Box<Type>, Box<Type>),
}

impl ResolvedExpr {
    // gets the type of an expression without type checking anything inside.
    // Basically when it gets to a function type it doesn't check if the inputs are correct,
    // while `get_type_checked` does check if the inputs are correct. Idk which is more useful
    // so I am keeping both right now.
    fn get_type_unchecked(self, globals: &Vec<ResolvedDefinition>) -> Option<Type> {
        match self {
            ResolvedExpr::Apply(func, _) => match func.get_type_unchecked(globals) {
                Some(Type::FunctionType(_, output_type)) => Some(*output_type),
                _ => None,
            },
            ResolvedExpr::Ref(i) => {
                let mbtype = interpret_unchecked(globals, globals[i].type_sig.clone())?;
                mbtype.get_as_type()
            }
            ResolvedExpr::Internal(i) => Some(INTERNAL_VALUES[i].val.clone().get_type()),
            ResolvedExpr::IntLit(_) => Some(Type::Int),
            ResolvedExpr::Unit => Some(Type::Unit),
        }
    }

    // gets the type of a value. While obtaining the value it also recursively checks
    // the type of everything inside the expression.
    fn get_type_checked(self, globals: &Vec<ResolvedDefinition>) -> Option<Type> {
        match self {
            ResolvedExpr::Apply(func, args) => match func.get_type_checked(globals) {
                Some(Type::FunctionType(input_type, output_type)) => {
                    if args.get_type_checked(globals)? == *input_type {
                        Some(*output_type)
                    } else {
                        None
                    }
                }
                _ => None,
            },
            ResolvedExpr::Ref(i) => {
                let mbtype = interpret_unchecked(globals, globals[i].type_sig.clone())?;
                mbtype.get_as_type()
            }
            ResolvedExpr::Internal(i) => Some(INTERNAL_VALUES[i].val.clone().get_type()),
            ResolvedExpr::IntLit(_) => Some(Type::Int),
            ResolvedExpr::Unit => Some(Type::Unit),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckedDefinition {
    get_type: Type,
    value: ResolvedExpr,
}

pub fn basic_type_check(globals: &Vec<ResolvedDefinition>) -> Option<Vec<CheckedDefinition>> {
    let mut out: Vec<CheckedDefinition> = Vec::new();
    for def in globals {
        out.push(CheckedDefinition {
            get_type: def.type_sig.clone().get_type_checked(globals)?,
            value: def.value.clone(),
        })
    }
    Some(out)
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RuntimeVal {
    Type(Type),
    IntLit(i64),
    Unit,
    Bool(bool),
    Add, // add function
    PartialAdd(i64),
    PrintInt,
}

impl RuntimeVal {
    fn get_as_int(self) -> Option<i64> {
        match self {
            RuntimeVal::IntLit(n) => Some(n),
            _ => None,
        }
    }

    fn apply_as_fn(self, arg: RuntimeVal) -> Option<RuntimeVal> {
        match self {
            RuntimeVal::Add => Some(RuntimeVal::PartialAdd(arg.get_as_int()?)),
            RuntimeVal::PartialAdd(n) => Some(RuntimeVal::IntLit(n + arg.get_as_int()?)),
            RuntimeVal::PrintInt => {
                let n: i64 = arg.get_as_int()?;
                println!("{}", n);
                Some(RuntimeVal::Unit)
            }
            _ => None,
        }
    }

    fn get_as_type(self) -> Option<Type> {
        match self {
            RuntimeVal::Type(t) => Some(t),
            _ => None,
        }
    }

    fn get_type(self) -> Type {
        match self {
            RuntimeVal::Type(_) => Type::Type,
            RuntimeVal::IntLit(_) => Type::Int,
            RuntimeVal::Unit => Type::Unit,
            RuntimeVal::Bool(_) => Type::Bool,
            RuntimeVal::Add => Type::FunctionType(
                Box::new(Type::Int),
                Box::new(Type::FunctionType(Box::new(Type::Int), Box::new(Type::Int))),
            ),
            RuntimeVal::PartialAdd(_) => {
                Type::FunctionType(Box::new(Type::Int), Box::new(Type::Int))
            }
            RuntimeVal::PrintInt => Type::FunctionType(Box::new(Type::Int), Box::new(Type::Unit)),
        }
    }
}

fn interpret_unchecked(
    globals: &Vec<ResolvedDefinition>,
    to_eval: ResolvedExpr,
) -> Option<RuntimeVal> {
    match to_eval {
        ResolvedExpr::Apply(func, arg) => {
            let f: RuntimeVal = interpret_unchecked(globals, *func)?;
            let x: RuntimeVal = interpret_unchecked(globals, *arg)?;
            f.apply_as_fn(x)
        }
        ResolvedExpr::Ref(i) => interpret_unchecked(globals, globals.get(i)?.clone().value),
        ResolvedExpr::Internal(i) => INTERNAL_VALUES.get(i).map(|v| v.val.clone()),
        ResolvedExpr::IntLit(n) => Some(RuntimeVal::IntLit(n.try_into().unwrap())),
        ResolvedExpr::Unit => Some(RuntimeVal::Unit),
    }
}

fn interpret(globals: &Vec<CheckedDefinition>, to_eval: ResolvedExpr) -> Option<RuntimeVal> {
    match to_eval {
        ResolvedExpr::Apply(func, arg) => {
            let f: RuntimeVal = interpret(globals, *func)?;
            let x: RuntimeVal = interpret(globals, *arg)?;
            f.apply_as_fn(x)
        }
        ResolvedExpr::Ref(i) => interpret(globals, globals.get(i)?.clone().value),
        ResolvedExpr::Internal(i) => INTERNAL_VALUES.get(i).map(|v| v.val.clone()),
        ResolvedExpr::IntLit(n) => Some(RuntimeVal::IntLit(n.try_into().unwrap())),
        ResolvedExpr::Unit => Some(RuntimeVal::Unit),
    }
}

pub fn main() {
    let args: Vec<String> = env::args().collect();

    let mut src_file: File = match args.get(1) {
        Some(f) => File::open(f).expect("Failed to open file :/"),
        None => {
            println!("No file argument supplied </3");
            return;
        }
    };
    let mut src: String = String::new();
    src_file
        .read_to_string(&mut src)
        .expect("Something went wrong when reading the file :/");

    let tokens: Vec<Token> = tokenize(src.as_str()).collect();
    dbg!(&tokens);
    let ast: Vec<Binding> = parse(tokens.into_iter()).collect();
    dbg!(&ast);
    let resolved = resolve_bindings(&ast).expect("Failed to resolve names");
    dbg!(&resolved);
    let checked = basic_type_check(&resolved).expect("Type checking failed");
    dbg!(&checked);
    for i in 0..resolved.len() {
        let result = interpret(&checked, resolved[i].value.clone());
        println!("{} := {:?}", ast[i].var_name.clone(), result);
    }
}
