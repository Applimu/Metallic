use std::fs::File;
use std::io::Read;
use std::rc::Rc;
use std::{collections::HashMap, env};

use parsing::{Binding, Command, ParseError};
use resolve::{ResolveError, UnresolvedExpr, resolve_exprs};
use runtime::{Function, FunctionConstant, RuntimeError, Val, interpret};
use type_checking::{CheckerError, type_check_program};

mod parsing;
mod resolve;
mod runtime;
#[cfg(test)]
mod tests;
mod type_checking;

// An atomic name in an expression
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Atomic {
    // index reference to local variable
    Local(usize),
    // reference to a value in the globals array
    Global(usize),
    // literal value
    Internal(Internal),
    // EnumVariant("Ex", 5) is the 5th variant of the Ex enum
    EnumVariant(String, usize),
    EnumType(String),
    IntLit(i64),
    StringLit(String),
}

// an expression where each variable name has been resolved
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Apply(Rc<Expr>, Rc<Expr>),
    Function {
        input_type: Rc<Expr>,
        output: Rc<Expr>,
    },
    Atom(Atomic),
    Match {
        enum_name: String,
        matchend: Rc<Expr>,
        branches: Vec<Rc<Expr>>,
    },
    Let {
        new_value_type: Rc<Expr>,
        new_value: Rc<Expr>,
        expr: Rc<Expr>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    Type,
    Int,
    String,
    Unit,
    Pair(Rc<Type>, Rc<Type>),
    FunctionType(Rc<Type>, Rc<Type>),
    DepProd {
        // this function should always return a Type
        family: Rc<Function>,
    },
    Enum(String),
    IO,
}

impl Type {
    #[allow(non_snake_case)]
    fn Bool() -> Type {
        Type::Enum("Bool".to_owned())
    }
}

// These are constant values that are defined internally
// It's basically made for pairing names with their `runtime::Val`s
#[derive(Debug, Eq, PartialEq, Clone, Copy)]
pub enum Internal {
    IType,
    IInt,
    Iadd,
    Ifun,
    IUnit,
    IDepProd,
    ImkPair,
    IPairType,
    IBool,
    Itrue,
    Ifalse,
    Ieq,
    Iunit,
    Igetln,
    Iprintln,
}

impl Internal {
    fn get_type(&self) -> Type {
        match self {
            Internal::IType => Type::Type,
            Internal::IInt => Type::Type,
            Internal::Iadd => Type::FunctionType(
                Rc::new(Type::Int),
                Rc::new(Type::FunctionType(Rc::new(Type::Int), Rc::new(Type::Int))),
            ),
            Internal::Ifun => Type::FunctionType(
                Rc::new(Type::Type),
                Rc::new(Type::FunctionType(Rc::new(Type::Type), Rc::new(Type::Type))),
            ),
            Internal::Iunit => Type::Unit,
            Internal::IUnit => Type::Type,
            Internal::IDepProd => todo!("Implement DepProd's type"),
            // should be (Type: T) -> (T -> Type) -> Type
            Internal::ImkPair => Type::DepProd {
                family: Rc::new(Function::PartialApplication(
                    FunctionConstant::OutputTypeOfMkPair,
                    Vec::new(),
                )),
            },
            Internal::IPairType => Type::FunctionType(
                Rc::new(Type::Type),
                Rc::new(Type::FunctionType(Rc::new(Type::Type), Rc::new(Type::Type))),
            ),
            Internal::IBool => Type::Type,
            Internal::Itrue => Type::Bool(),
            Internal::Ifalse => Type::Bool(),
            Internal::Ieq => Type::FunctionType(
                Rc::new(Type::Int),
                Rc::new(Type::FunctionType(
                    Rc::new(Type::Int),
                    Rc::new(Type::Bool()),
                )),
            ),
            Internal::Igetln => Type::FunctionType(
                Rc::new(Type::FunctionType(Rc::new(Type::String), Rc::new(Type::IO))),
                Rc::new(Type::IO),
            ),
            Internal::Iprintln => Type::FunctionType(Rc::new(Type::String), Rc::new(Type::IO)),
        }
    }

    pub fn val(&self) -> Val {
        match self {
            Internal::IType => Val::Type(Rc::new(Type::Type)),
            Internal::IInt => Val::Type(Rc::new(Type::Int)),
            Internal::Iadd => Val::Function(Function::PartialApplication(
                FunctionConstant::Add,
                Vec::new(),
            )),
            Internal::Ifun => Val::Function(Function::PartialApplication(
                FunctionConstant::Fun,
                Vec::new(),
            )),
            Internal::Iunit => Val::Unit,
            Internal::IUnit => Val::Type(Rc::new(Type::Unit)),
            Internal::IDepProd => Val::Function(Function::PartialApplication(
                FunctionConstant::DepProd,
                Vec::new(),
            )),
            Internal::ImkPair => Val::Function(Function::PartialApplication(
                FunctionConstant::Pair,
                Vec::new(),
            )),
            Internal::IPairType => Val::Function(Function::PartialApplication(
                FunctionConstant::PairType,
                Vec::new(),
            )),
            Internal::IBool => Val::Type(Rc::new(Type::Bool())),
            Internal::Itrue => Val::Enum("Bool".to_owned(), 1),
            Internal::Ifalse => Val::Enum("Bool".to_owned(), 0),
            Internal::Ieq => Val::Function(Function::PartialApplication(
                FunctionConstant::IntEq,
                Vec::new(),
            )),
            Internal::Igetln => Val::Function(Function::PartialApplication(
                FunctionConstant::GetLn,
                Vec::new(),
            )),
            Internal::Iprintln => Val::Function(Function::PartialApplication(
                FunctionConstant::PrintLn,
                Vec::new(),
            )),
        }
    }

    fn try_as_internal(name: &str) -> Option<Internal> {
        Some(match name {
            "Type" => Internal::IType,
            "Int" => Internal::IInt,
            "add" => Internal::Iadd,
            "fun" => Internal::Ifun,
            "Unit" => Internal::IUnit,
            "DepProd" => Internal::IDepProd,
            "pair" => Internal::ImkPair,
            "PairType" => Internal::IPairType,
            "Bool" => Internal::IBool,
            "true" => Internal::Itrue,
            "false" => Internal::Ifalse,
            "eq" => Internal::Ieq,
            "getln" => Internal::Igetln,
            "println" => Internal::Iprintln,
            _ => return None,
        })
    }
}

pub struct UnresolvedProgram {
    // the first three fields of this struct should always
    // have the same length.
    def_names: Vec<String>,
    def_types: Vec<UnresolvedExpr>,
    def_values: Vec<UnresolvedExpr>,
    to_evaluate: Vec<UnresolvedExpr>,
    enums: HashMap<String, Vec<String>>,
}

// Unpacks the list of commands into the different types of commands.
// first three arrays are always the same length
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

pub struct Program {
    names: Vec<String>,
    globals: Vec<Rc<Expr>>,
    // TODO: change this into &'a[Rc<Type>]
    global_types: Vec<Rc<Expr>>,
    evals: Vec<Rc<Expr>>,
}

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
    let prog = Program {
        names: prog.def_names,
        globals,
        global_types: resolved_types,
        evals: resolved_evals,
    };

    type_check_program(&prog).map_err(GenericError::CheckerError)?;
    println!("Program is type-checked!");

    Ok(prog)
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

    let Program {
        names: _,
        globals,
        global_types,
        evals,
    } = make_program(src.as_str()).expect("failed to compile program");
    println!("Interpretting program!");
    for e in evals {
        let result = interpret(&globals, &global_types, &e);
        println!("evaluation result := {:?}", result);
    }
}
