use std::env;
use std::fs::File;
use std::io::Read;

use parsing::{Binding, Command, ParseError, UnresolvedExpr};
use runtime::{ArrFunc, Function, RuntimeError, Val, interpret};

mod parsing;
mod runtime;
#[cfg(test)]
mod tests;

// an expression where each name is known
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Apply(Box<Expr>, Box<Expr>),
    Function {
        // variable_name: String,
        input_type: Box<Expr>,
        output: Box<Expr>,
    },
    // reference to local variable (debrujin style)
    Local(usize),
    // reference to another defined value as index in the grid
    Global(usize),
    // literal value
    Value(Box<runtime::Val>),
    IntLit(i64),
    Unit,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    Type,
    Int,
    Unit,
    Bool,
    Pair(Box<Type>, Box<Type>),
    FunctionType(Box<Type>, Box<Type>),
    DepProd {
        input_type: Box<Type>,
        function: Box<ArrFunc>,
    },
}

pub struct InternalValue {
    name: &'static str,
    val: Val,
}

// all the names that are resolved internally
pub const INTERNAL_VALUES: [InternalValue; 8] = [
    InternalValue {
        name: "Type",
        val: Val::Type(Type::Type),
    },
    InternalValue {
        name: "Int",
        val: Val::Type(Type::Int),
    },
    InternalValue {
        name: "add",
        val: Val::Function(Function::Arrow(ArrFunc::Add)),
    },
    InternalValue {
        name: "fun",
        val: Val::Function(Function::Arrow(ArrFunc::Fun)),
    },
    InternalValue {
        name: "Unit",
        val: Val::Type(Type::Unit),
    },
    InternalValue {
        name: "DepProd",
        val: Val::Function(Function::DepProd(runtime::DependentProduct::DepProd)),
    },
    InternalValue {
        name: "mk_pair",
        val: Val::Function(Function::DepProd(runtime::DependentProduct::Pair)),
    },
    InternalValue {
        name: "PairType",
        val: Val::Function(Function::Arrow(ArrFunc::TypeOfMakePair)),
    },
];

fn get_internal_idx(name: &str) -> Option<usize> {
    for (idx, internal) in INTERNAL_VALUES.iter().enumerate() {
        if internal.name == name {
            // println!(
            //     "Index: {} for internal value {} = {}",
            //     idx, internal.name, name
            // );
            return Some(idx);
        }
    }
    // panic!("name: '{}', does not exist as an internal value", name)
    None
}

fn get_internal_val(name: &str) -> Option<Val> {
    Some(INTERNAL_VALUES[get_internal_idx(name)?].val.clone())
}

//TODO: create a better error message
#[derive(Debug)]
pub enum ResolveError {
    UnknownName(String),
}

// Resolves all names inside an expression and converts them into an indices of the provided array
fn resolve_expr(
    globals: &Vec<String>,
    locals: &mut Vec<String>,
    expr: UnresolvedExpr,
) -> Result<Expr, ResolveError> {
    match expr {
        UnresolvedExpr::Apply(func, arg) => {
            let rfunc = Box::new(resolve_expr(globals, locals, *func)?);
            let rarg = Box::new(resolve_expr(globals, locals, *arg)?);
            Ok(Expr::Apply(rfunc, rarg))
        }
        UnresolvedExpr::Function {
            name,
            input_type,
            output,
        } => {
            let input_type = resolve_expr(globals, locals, *input_type)?;
            locals.push(name.clone());
            let output = resolve_expr(globals, locals, *output)?;
            assert_eq!(locals.pop().unwrap(), name);
            Ok(Expr::Function {
                // variable_name: name,
                input_type: Box::new(input_type),
                output: Box::new(output),
            })
        }
        UnresolvedExpr::Variable(s) => {
            // local variables shadow globals shadow internal
            for (i, name) in locals.iter().rev().enumerate() {
                // here `i` gives the debrujin indices
                if **name == s {
                    return Ok(Expr::Local(i));
                }
            }
            for (i, name) in globals.iter().enumerate() {
                if *name == s {
                    return Ok(Expr::Global(i));
                }
            }
            match get_internal_val(&s) {
                Some(v) => Ok(Expr::Value(Box::new(v))),
                None => Err(ResolveError::UnknownName(s)),
            }
        }
        UnresolvedExpr::IntLit(n) => Ok(Expr::IntLit(n)),
        UnresolvedExpr::Unit => Ok(Expr::Unit),
    }
}

// resolves references to local, global, and internally defined names. Multiple variables in the same
// thing gives undefined behavior currently.
// TODO: Allow for name overloading (make the types of variables matter)
fn resolve_exprs(
    global_names: &Vec<String>,
    exprs: Vec<UnresolvedExpr>,
) -> Result<Vec<Expr>, ResolveError> {
    let mut resolved_program: Vec<Expr> = Vec::new();
    for e in exprs {
        let resolved = resolve_expr(&global_names, &mut Vec::new(), e.clone())?;
        resolved_program.push(resolved);
    }
    Ok(resolved_program)
}

impl Expr {
    // gets the type of a value. While obtaining the value it also recursively checks that
    // the type of everything inside the expression has no type errors.
    fn get_type_checked_with_locals(
        self,
        globals: &Vec<Expr>,
        locals: &mut Vec<Type>,
    ) -> Result<Type, RuntimeError> {
        match self {
            Expr::Apply(func, args) => {
                let func_type = func.clone().get_type_checked_with_locals(globals, locals)?;
                let args_type = args.clone().get_type_checked_with_locals(globals, locals)?;
                match func_type {
                    Type::FunctionType(input_type, output_type) => {
                        if args_type == *input_type {
                            Ok(*output_type)
                        } else {
                            Err(RuntimeError::TypesMismatch {
                                expected: *input_type,
                                found: args_type,
                            })
                        }
                    }
                    _ => Err(RuntimeError::NotFunctionType {
                        func: *func,
                        args: *args,
                    }),
                }
            }
            Expr::Function {
                // variable_name: _,
                input_type,
                output,
            } => {
                let runtime_val = interpret(globals, *input_type)?;
                let input_type = runtime_val.clone().get_as_type()?;
                Ok(Type::FunctionType(
                    Box::new(input_type),
                    Box::new(output.get_type_checked_with_locals(globals, locals)?),
                ))
            }
            Expr::Local(i) => Ok(locals[locals.len() - 1 - i].clone()),
            Expr::Global(i) => {
                <Expr as Clone>::clone(&globals[i]).get_type_checked_with_locals(globals, locals)
            }
            Expr::IntLit(_) => Ok(Type::Int),
            Expr::Unit => Ok(Type::Unit),
            Expr::Value(val) => Ok(val.get_type(globals)),
        }
    }
}

pub fn is_wellformed_type(globals: &Vec<Expr>, maybe_type: Expr) -> Result<Type, RuntimeError> {
    let yeah = interpret(globals, maybe_type)?;
    yeah.get_as_type()
}

// checks the type of each type signature and makes sure that it is a type
fn check_wellformed_types(
    globals: &Vec<Expr>,
    globals_types: Vec<Expr>,
) -> Result<Vec<Type>, RuntimeError> {
    let mut types = Vec::new();
    for type_expr in globals_types {
        let type_sig = interpret(globals, type_expr)?;
        types.push(type_sig.get_as_type()?);
    }

    Ok(types)
}

// Unpacks the list of commands into the different types of commands.
// All three arrays are expected to have the same length, the first is the names of all bound
// values, the second is the type signatures and the third is the values
pub fn unpack(
    commands: Vec<Command>,
) -> (
    Vec<String>,
    Vec<UnresolvedExpr>,
    Vec<UnresolvedExpr>,
    Vec<UnresolvedExpr>,
) {
    let mut def_names = Vec::new();
    let mut types = Vec::new();
    let mut def_values = Vec::new();
    let mut to_eval = Vec::new();
    for command in commands {
        match command {
            Command::Definition(Binding {
                var_name,
                type_sig,
                value,
            }) => {
                def_names.push(var_name);
                types.push(type_sig);
                def_values.push(value);
            }
            Command::Eval(expr) => to_eval.push(expr),
        }
    }
    (def_names, types, def_values, to_eval)
}

#[derive(Debug)]
pub enum GenericError<'a> {
    ResolutionError(ResolveError),
    ParseError(ParseError<'a>),
    RuntimeError(RuntimeError),
}

pub fn make_program<'a>(
    src: &'a str,
) -> Result<(Vec<String>, Vec<Expr>, Vec<Expr>), GenericError<'a>> {
    // parsing
    let ast: Vec<Command> = parsing::parse_src(src).map_err(GenericError::ParseError)?;
    let (def_names, def_types, def_vals, to_eval) = unpack(ast);
    // Name resolution
    let globals = resolve_exprs(&def_names, def_vals).map_err(GenericError::ResolutionError)?;
    let resolved_evals =
        resolve_exprs(&def_names, to_eval).map_err(GenericError::ResolutionError)?;
    let resolved_types =
        resolve_exprs(&def_names, def_types).map_err(GenericError::ResolutionError)?;
    // Type checking
    let checked_types =
        check_wellformed_types(&globals, resolved_types).map_err(GenericError::RuntimeError);
    Ok((def_names, globals, resolved_evals))
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

    let (def_names, resolved_values, resolved_evals) =
        make_program(src.as_str()).expect("failed to compile program");
    for e in resolved_evals {
        let result = interpret(&resolved_values, e.clone());
        println!("evaluation result := {:?}", result);
    }
}
