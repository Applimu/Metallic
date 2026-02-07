use std::fs::File;
use std::io::Read;
use std::rc::Rc;
use std::{collections::HashMap, env};

use parsing::{Binding, Command, ParseError};
use resolve::{ResolveError, UnresolvedExpr, resolve_exprs};
use runtime::{FunctionConstant, RuntimeError, Val};
use type_checking::{CheckerError, type_check_program};

mod parsing;
mod resolve;
mod runtime;
#[cfg(test)]
mod tests;
mod tokenize;
mod type_checking;
mod defuncd;

/// An atomic value in an expression, a leaf of the AST
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Atomic {
    /// index reference to local variable
    Local(usize),
    /// reference to a value in the globals array
    Global(usize),
    /// literal value
    Internal(Internal),
    /// EnumVariant("Ex", 5) is the 5th variant of the Ex enum
    EnumVariant(String, usize),
    /// An enum type literal, just represented as a string
    EnumType(String),
    /// An integer literal
    IntLit(i64),
    /// A string literal
    StringLit(String),
}

/// an expression where each variable name has been resolved
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    /// Application of a function to a value
    Apply(Rc<Expr>, Rc<Expr>),
    /// A lambda expression
    Function {
        input_type: Rc<Expr>,
        output: Rc<Expr>,
    },
    /// An atomic value in our expression
    Atom(Atomic),
    /// A match statement which matches on an enum of a specific type
    Match {
        enum_name: String,
        matchend: Rc<Expr>,
        branches: Vec<Rc<Expr>>,
    },
    /// A let expression with
    Let {
        new_value_type: Rc<Expr>,
        new_value: Rc<Expr>,
        expr: Rc<Expr>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    /// The type of types, which doesn't have any universe levels or anything (yet?)
    Type,
    /// The type of integers
    Int,
    /// The type of string literals
    String,
    /// The type of ()
    Unit,
    /// A Product type
    Pair(Rc<Type>, Rc<Type>),
    /// An arrow type
    FunctionType(Rc<Type>, Rc<Type>),
    /// A dependent product over a closure function
    DepProdClosure {
        // this is an arrow function which should always return a type
        captured_vals: Vec<Rc<Val>>,
        code: Rc<Expr>
    },
    /// A dependent product over a `FunctionConstant`
    DepProdPartialApp {
        // this is an arrow function which should always return a type
        fn_const: FunctionConstant,
        args: Vec<Rc<Val>>,
    },
    /// An enum type, represented by it's name
    Enum(String),
    /// The IO type which represents a program that can be executed.
    IO,
}

impl Type {
    #[allow(non_snake_case)]
    fn Bool() -> Type {
        Type::Enum("Bool".to_owned())
    }
}

/// These are constant values that are defined internally by the compiler
/// It's made for pairing identifiers with their `runtime::Val`s
#[derive(Debug, Eq, PartialEq, Clone, Copy, Hash)]
pub enum Internal {
    IType,    // type of types
    Ifun,     // curried function-type function on types
    IDepProd, // the function that converts a A -> Type into a dependent product

    IInt, // type of integers
    Iadd, // curried add function on integers
    Imul,
    Isub,
    Ieq, // integer boolean equality
    Igt,
    Ilt,
    Ile,

    IUnit, // the type of the unit ()
    Iunit, // the unit value

    IPairType, // the type of pairs of elements
    ImkPair,   // the function that makes a pair of elements
    Ifirst,    // gets the first half of a pair
    Isecond,   // gets the second half of a pair

    IBool, // the type of the boolean domain
    IString,
    Itrue,  // true bool
    Ifalse, // false bool

    Igetln,   // IO action of getting a string
    Iprintln, // IO action of printing a string
    ISeq,     // Sequencs two IO actions
    IDone,    // "Empty IO action"
}

impl Internal {
    /// Constructs the `Type` of the provided `Internal`
    fn get_type(&self) -> Type {
        use crate::Type::{FunctionType, IO, Int, String};
        use Internal::*;
        match self {
            IType | IInt | IString | IUnit | IBool => Type::Type,
            Iadd | Imul | Isub => Type::FunctionType(
                Rc::new(Type::Int),
                Rc::new(Type::FunctionType(Rc::new(Type::Int), Rc::new(Type::Int))),
            ),
            Ifun => FunctionType(
                Rc::new(Type::Type),
                Rc::new(FunctionType(Rc::new(Type::Type), Rc::new(Type::Type))),
            ),
            Iunit => Type::Unit,
            IDepProd => Type::DepProdPartialApp { 
                fn_const: FunctionConstant::TypeOfDepProd,
                args: Vec::new(),
            },
            ImkPair => Type::DepProdPartialApp {
                fn_const: FunctionConstant::OutputTypeOfMkPair,
                args: Vec::new(),
            },
            IPairType => FunctionType(
                Rc::new(Type::Type),
                Rc::new(FunctionType(Rc::new(Type::Type), Rc::new(Type::Type))),
            ),
            Ifirst => todo!(),
            Isecond => todo!(),
            Itrue => Type::Bool(),
            Ifalse => Type::Bool(),
            Igetln => FunctionType(
                Rc::new(FunctionType(Rc::new(String), Rc::new(IO))),
                Rc::new(IO),
            ),
            Iprintln => FunctionType(Rc::new(String), Rc::new(IO)),
            ISeq => FunctionType(
                Rc::new(Type::IO),
                Rc::new(FunctionType(Rc::new(Type::IO), Rc::new(Type::IO))),
            ),
            IDone => Type::IO,
            Ieq | Igt | Ilt | Ile => FunctionType(
                Rc::new(Int),
                Rc::new(FunctionType(Rc::new(Int), Rc::new(Type::Bool()))),
            ),
        }
    }

    /// Constructs the `Val` of the provided `Internal`
    pub fn val(&self) -> Val {
        match self {
            Internal::IType => Val::Type(Rc::new(Type::Type)),
            Internal::IInt => Val::Type(Rc::new(Type::Int)),
            Internal::Iadd => Val::PartialApplication(
                FunctionConstant::Add,
                Vec::new(),
            ),
            Internal::Imul => Val::PartialApplication(
                FunctionConstant::Mul,
                Vec::new(),
            ),
            Internal::Isub => Val::PartialApplication(
                FunctionConstant::Sub,
                Vec::new(),
            ),
            Internal::Ifun => Val::PartialApplication(
                FunctionConstant::Fun,
                Vec::new(),
            ),
            Internal::Iunit => Val::Unit,
            Internal::IUnit => Val::Type(Rc::new(Type::Unit)),
            Internal::IDepProd => Val::PartialApplication(
                FunctionConstant::DepProd,
                Vec::new(),
            ),
            Internal::ImkPair => Val::PartialApplication(
                FunctionConstant::Pair,
                Vec::new(),
            ),
            Internal::IPairType => Val::PartialApplication(
                FunctionConstant::PairType,
                Vec::new(),
            ),
            Internal::Ifirst => todo!(),
            Internal::Isecond => todo!(),
            Internal::IBool => Val::Type(Rc::new(Type::Bool())),
            Internal::Itrue => Val::Enum("Bool".to_owned(), 1),
            Internal::Ifalse => Val::Enum("Bool".to_owned(), 0),
            Internal::Ieq => Val::PartialApplication(
                FunctionConstant::IntEq,
                Vec::new(),
            ),
            Internal::Igetln => Val::PartialApplication(
                FunctionConstant::GetLn,
                Vec::new(),
            ),
            Internal::Iprintln => Val::PartialApplication(
                FunctionConstant::PrintLn,
                Vec::new(),
            ),
            Internal::IString => Val::Type(Rc::new(Type::String)),
            Internal::Ilt => Val::PartialApplication(
                FunctionConstant::IntLt,
                Vec::new(),
            ),
            Internal::Igt => Val::PartialApplication(
                FunctionConstant::IntGt,
                Vec::new(),
            ),
            Internal::Ile => Val::PartialApplication(
                FunctionConstant::IntLe,
                Vec::new(),
            ),
            Internal::ISeq => Val::PartialApplication(
                FunctionConstant::Seq,
                Vec::new(),
            ),
            Internal::IDone => Val::IO(runtime::IOAction::Done),
        }
    }

    fn try_as_internal(name: &str) -> Option<Internal> {
        Some(match name {
            "Type" => Internal::IType,
            "Int" => Internal::IInt,
            "String" => Internal::IString,
            "Bool" => Internal::IBool,
            "add" => Internal::Iadd,
            "mul" => Internal::Imul,
            "sub" => Internal::Isub,
            "fun" => Internal::Ifun,
            "Unit" => Internal::IUnit,
            "DepProd" => Internal::IDepProd,
            "pair" => Internal::ImkPair,
            "PairType" => Internal::IPairType,
            "first" => Internal::Ifirst,
            "second" => Internal::Isecond,
            "true" => Internal::Itrue,
            "false" => Internal::Ifalse,
            "eq" => Internal::Ieq,
            "gt" => Internal::Igt,
            "lt" => Internal::Ilt,
            "le" => Internal::Ile,
            "getln" => Internal::Igetln,
            "println" => Internal::Iprintln,
            "seq" => Internal::ISeq,
            "done" => Internal::IDone,
            _ => return None,
        })
    }
}

/// A program where the names have not been resolved yet
/// the first three fields of this struct should always
/// have the same length.
pub struct UnresolvedProgram {
    def_names: Vec<String>,
    def_types: Vec<UnresolvedExpr>,
    def_values: Vec<UnresolvedExpr>,
    to_evaluate: Vec<UnresolvedExpr>,
    enums: HashMap<String, Vec<String>>,
}

/// Unpacks the list of commands into the different types of commands.
pub fn separate_commands(commands: Vec<Command>) -> UnresolvedProgram {
    let mut def_names = Vec::new();
    let mut def_types = Vec::new();
    let mut def_values = Vec::new();
    let mut to_eval = Vec::new();
    let mut enums: HashMap<String, Vec<String>> = HashMap::new();
    enums.insert(
        "Bool".to_owned(),
        vec!["false".to_owned(), "true".to_owned()],
    );
    for command in commands {
        match command {
            Command::Definition(Binding {
                var_name,
                type_sig,
                value,
            }) => {
                def_names.push(var_name);
                def_types.push(type_sig);
                def_values.push(value);
            }
            Command::Eval(expr) => to_eval.push(expr),
            Command::Enum(enum_name, variants) => match enums.insert(enum_name, variants) {
                Some(_) => panic!("Multiple enums have the same name"),
                None => (),
            },
        }
    }
    UnresolvedProgram {
        def_names,
        def_types,
        def_values,
        to_evaluate: to_eval,
        enums,
    }
}

#[derive(Debug)]
pub enum GenericError<'a> {
    ResolutionError(ResolveError),
    ParseError(ParseError<'a>),
    RuntimeError(RuntimeError),
    CheckerError(CheckerError),
}

/// A `Program` that can be interpreted by `runtime::interpret`
/// This is the object that is verified to be correct through type-checking.
#[derive(Debug)]
pub struct Program {
    names: Vec<String>,
    globals: Vec<Rc<Expr>>,
    // TODO: change this into &'a[Rc<Type>]
    global_types: Vec<Rc<Expr>>,
    evals: Vec<Rc<Expr>>,
}

impl Program {
    pub fn new(names: Vec<String>, globals: Vec<Rc<Expr>>, global_types: Vec<Rc<Expr>>, evals: Vec<Rc<Expr>>) -> Program {
        assert!(names.len() == globals.len());
        assert!(names.len() == global_types.len());
        Program {
            names,
            globals,
            global_types,
            evals
        }
    }

    pub fn len(&self) -> usize {
        self.names.len()
    }
}

/// Big function that goes all the way for source code to final `Program`
pub fn make_program<'a>(src: &'a str) -> Result<Program, GenericError<'a>> {
    // parsing
    let ast: Vec<Command> = parsing::parse_src(src).map_err(GenericError::ParseError)?;
    let prog = separate_commands(ast);
    println!("Program parsed and separated!");
    // Name resolution
    let globals = resolve_exprs(&prog.def_names, &prog.enums, prog.def_values)
        .map_err(GenericError::ResolutionError)?;
    println!("Global values resolved");
    let resolved_evals = resolve_exprs(&prog.def_names, &prog.enums, prog.to_evaluate)
        .map_err(GenericError::ResolutionError)?;
    println!("Values to evaluate resolved");
    let resolved_types = resolve_exprs(&prog.def_names, &prog.enums, prog.def_types)
        .map_err(GenericError::ResolutionError)?;
    println!("Global's types values resolved");
    // Type checking
    let prog = Program::new(prog.def_names, globals, resolved_types, resolved_evals);
    // let prog = Program {
    //     names: prog.def_names,
    //     globals,
    //     global_types: resolved_types,
    //     evals: resolved_evals,
    // };

    type_check_program(&prog).map_err(GenericError::CheckerError)?;
    println!("Program is type-checked!");

    Ok(prog)
}


// pub fn main() {defuncd::main()}

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

    let Program {
        names,
        globals,
        global_types,
        evals,
    } = make_program(src.as_str()).expect("failed to compile program");
    println!("Interpretting program!");
    for e in evals {
        match runtime::interpret(&globals, &global_types, &names, &e) {
            Ok(result) => println!("evaluation result: {:?}", result),
            Err(error) => println!("evaluation error: {:?}", error),
        }
    }
}
