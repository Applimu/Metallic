use std::env;
use std::fs::File;
use std::io::Read;

use parsing::{Binding, Command, ParseError, UnresolvedExpr};

mod parsing;
#[cfg(test)]
mod tests;

// an expression where each name is known
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Apply(Box<Expr>, Box<Expr>),
    Function {
        variable_name: String,
        input_type: Box<Expr>,
        output: Box<Expr>,
    },
    // reference to local variable (debrujin style)
    Local(usize),
    // reference to another defined value as index in the grid
    Global(usize),
    // reference to internally defined value
    Internal(usize),
    IntLit(i64),
    Unit,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    Type,
    Int,
    Unit,
    Bool,
    FunctionType(Box<Type>, Box<Type>),
}

pub struct InternalValue {
    name: &'static str,
    val: RuntimeVal,
}

// all the names that are resolved internally
pub const INTERNAL_VALUES: [InternalValue; 6] = [
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
    InternalValue {
        name: "fun",
        val: RuntimeVal::Fun,
    },
    InternalValue {
        name: "Unit",
        val: RuntimeVal::Type(Type::Unit),
    },
];

fn get_internal_idx(name: &str) -> Option<usize> {
    for (idx, internal) in INTERNAL_VALUES.iter().enumerate() {
        if internal.name == name {
            return Some(idx);
        }
    }
    // panic!("name: '{}', does not exist as an internal value", name)
    None
}

fn get_internal_expr(name: &str) -> Expr {
    Expr::Internal(get_internal_idx(name).unwrap())
}

fn get_internal_val(name: &str) -> RuntimeVal {
    INTERNAL_VALUES[get_internal_idx(name).unwrap()].val.clone()
}

//TODO: create a better error message
#[derive(Debug)]
enum ResolveError {
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
                variable_name: name,
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
            match get_internal_idx(&s) {
                Some(i) => Ok(Expr::Internal(i)),
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
                variable_name: _,
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
            Expr::Internal(i) => Ok(INTERNAL_VALUES[i].val.clone().get_type(globals)),
            Expr::IntLit(_) => Ok(Type::Int),
            Expr::Unit => Ok(Type::Unit),
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RuntimeVal {
    Type(Type),
    IntLit(i64),
    Unit,
    Closure {
        input_type: Type,
        captured_vars: Vec<RuntimeVal>,
        code: Expr,
    },
    Bool(bool),
    Add, // add function
    PartialAdd(i64),
    Fun, // function type operator
    PartialFun(Type),
    PrintInt,
}

// TODO: create better error messages
#[derive(Debug)]
pub enum RuntimeError {
    TypeError { expected: Type, found: RuntimeVal },
    TypesMismatch { expected: Type, found: Type },
    NotAFunction { value: RuntimeVal },
    NotFunctionType { func: Expr, args: Expr },
}

impl RuntimeVal {
    fn get_as_int(self) -> Option<i64> {
        match self {
            RuntimeVal::IntLit(n) => Some(n),
            _ => None,
        }
    }

    // Unwraps this runtime value as a function, and then applies that function to
    // the supplied argument
    fn apply_as_fn(
        self,
        globals: &Vec<Expr>,
        locals: &mut Vec<RuntimeVal>,
        arg: RuntimeVal,
    ) -> Result<RuntimeVal, RuntimeError> {
        match self {
            RuntimeVal::Closure {
                input_type: _,
                captured_vars: mut bound_locals,
                code: expr,
            } => {
                let num_new_locals = bound_locals.len() + 1;
                locals.append(&mut bound_locals);
                // important that we push the new argument last as that is
                // the 0th debrujin index
                locals.push(arg);
                let result = interpret_with_locals(globals, locals, expr);
                for _ in 0..num_new_locals {
                    locals.pop().expect("Number of locals changed????");
                }

                // dbg!(&result);
                result
            }
            RuntimeVal::Add => match arg.clone().get_as_int() {
                Some(n) => Ok(RuntimeVal::PartialAdd(n)),
                None => Err(RuntimeError::TypeError {
                    expected: Type::Int,
                    found: arg.clone(),
                }),
            },
            RuntimeVal::PartialAdd(n) => match arg.clone().get_as_int() {
                Some(m) => Ok(RuntimeVal::IntLit(n + m)),
                None => Err(RuntimeError::TypeError {
                    expected: Type::Int,
                    found: arg.clone(),
                }),
            },
            RuntimeVal::Fun => arg.clone().get_as_type().map(RuntimeVal::PartialFun),
            RuntimeVal::PartialFun(t1) => match arg.clone().get_as_type() {
                Ok(t2) => Ok(RuntimeVal::Type({
                    Type::FunctionType(Box::new(t1), Box::new(t2))
                })),
                Err(e) => Err(e),
            },
            RuntimeVal::PrintInt => match arg.clone().get_as_int() {
                Some(n) => {
                    // println!("{}", n);
                    Ok(RuntimeVal::Unit)
                }
                None => Err(RuntimeError::TypeError {
                    expected: Type::Int,
                    found: arg.clone(),
                }),
            },
            _ => Err(RuntimeError::NotAFunction { value: self }),
        }
    }

    fn get_as_type(self) -> Result<Type, RuntimeError> {
        match self {
            RuntimeVal::Type(t) => Ok(t),
            c => Err(RuntimeError::TypeError {
                expected: Type::Type,
                found: c,
            }),
        }
    }

    // Given a runtime value, obtains the type of the given value. This is different
    // from get_as_type which asserts that the given value is a type and returns that value
    fn get_type(self, globals: &Vec<Expr>) -> Type {
        match self {
            RuntimeVal::Type(_) => Type::Type,
            RuntimeVal::IntLit(_) => Type::Int,
            RuntimeVal::Closure {
                input_type: t,
                captured_vars: bound_locals,
                code: e,
            } => {
                let mut locals_types = bound_locals
                    .iter()
                    .map(|r| r.clone().get_type(globals))
                    .collect();

                Type::FunctionType(
                    Box::new(t),
                    Box::new(
                        e.get_type_checked_with_locals(globals, &mut locals_types)
                            .expect("Bad expression caused function to have ill-formed type"),
                    ),
                )
            }
            RuntimeVal::Unit => Type::Unit,
            RuntimeVal::Bool(_) => Type::Bool,

            RuntimeVal::Add => Type::FunctionType(
                Box::new(Type::Int),
                Box::new(Type::FunctionType(Box::new(Type::Int), Box::new(Type::Int))),
            ),
            RuntimeVal::PartialAdd(_) => {
                Type::FunctionType(Box::new(Type::Int), Box::new(Type::Int))
            }

            RuntimeVal::Fun => Type::FunctionType(
                Box::new(Type::Type),
                Box::new(Type::FunctionType(
                    Box::new(Type::Type),
                    Box::new(Type::Type),
                )),
            ),
            RuntimeVal::PartialFun(_) => {
                Type::FunctionType(Box::new(Type::Type), Box::new(Type::Type))
            }
            RuntimeVal::PrintInt => Type::FunctionType(Box::new(Type::Int), Box::new(Type::Unit)),
        }
    }
}

fn interpret_with_locals(
    globals: &Vec<Expr>,
    locals: &mut Vec<RuntimeVal>,
    to_eval: Expr,
) -> Result<RuntimeVal, RuntimeError> {
    //dbg!(&locals);
    match to_eval {
        Expr::Apply(func, arg) => {
            // println!("APPLY FUNCTION:");
            let f: RuntimeVal = interpret_with_locals(globals, locals, *func)?;
            // println!("APPLY ARG:");
            let x: RuntimeVal = interpret_with_locals(globals, locals, *arg)?;
            let res = f.apply_as_fn(globals, locals, x);
            // println!("END APPLY ({:?})", res);
            res
        }
        Expr::Function {
            variable_name: _,
            input_type,
            output,
        } => {
            // println!("FUNCTION");
            let input_type = interpret_with_locals(globals, locals, *input_type)?;
            let res = Ok(RuntimeVal::Closure {
                input_type: input_type.get_as_type()?,
                captured_vars: locals.clone(),
                code: *output,
            });
            // println!("END FUNCTION");
            res
        }
        // The check here fails because when we evaluate during type checking it doesnt
        // have values of every single local variable
        Expr::Local(i) => Ok(locals[locals.len() - 1 - i].clone()),
        Expr::Global(i) => interpret_with_locals(globals, locals, globals[i].clone()),
        Expr::Internal(i) => Ok(INTERNAL_VALUES[i].val.clone()),
        Expr::IntLit(n) => Ok(RuntimeVal::IntLit(n)),
        Expr::Unit => Ok(RuntimeVal::Unit),
    }
}

pub fn interpret(globals: &Vec<Expr>, to_eval: Expr) -> Result<RuntimeVal, RuntimeError> {
    let mut locals = Vec::new();
    let res = interpret_with_locals(globals, &mut locals, to_eval);
    assert!(locals.len() == 0);
    res
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

pub fn make_program<'a>(
    src: &'a str,
) -> Result<(Vec<String>, Vec<Expr>, Vec<Expr>), ParseError<'a>> {
    let ast: Vec<Command> = parsing::parse_src(src)?;
    let (def_names, def_types, def_vals, to_eval) = unpack(ast);
    let resolved_globals =
        resolve_exprs(&def_names, def_vals).expect("Failed to resolve value names");
    let resolved_evals = resolve_exprs(&def_names, to_eval).expect("failed lmao");
    Ok((def_names, resolved_globals, resolved_evals))
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
