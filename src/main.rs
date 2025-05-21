use std::collections::HashSet;
use std::fs::File;
use std::io::Read;
use std::rc::Rc;
use std::{collections::HashMap, env};

use parsing::{Binding, Command, Matching, ParseError, UnresolvedExpr};
use runtime::{ArrFunc, Function, RuntimeError, Val, interpret};

mod parsing;
mod runtime;
#[cfg(test)]
mod tests;

// an expression where each name is known
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Apply(Rc<Expr>, Rc<Expr>),
    Function {
        // variable_name: String,
        input_type: Rc<Expr>,
        output: Rc<Expr>,
    },
    // reference to local variable (debrujin style)
    Local(usize),
    // reference to another defined value as index in the grid
    Global(usize),
    // literal value
    Value(Rc<Val>),
    IntLit(i64),
    // based on the local variable referenced to by the usize
    Match {
        enum_name: String,
        local: usize,
        branches: Vec<Rc<Expr>>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    Type,
    Int,
    Unit,
    Bool,
    Pair(Rc<Type>, Rc<Type>),
    FunctionType(Rc<Type>, Rc<Type>),
    DepProd {
        input_type: Rc<Type>,
        // this function should always return a Type
        // and should have the same input type as the input_type
        function: Rc<ArrFunc>,
    },
    // TODO: Add usize here to show how many variants there are in a given Enum type
    Enum(String),
}

pub struct InternalValue {
    name: &'static str,
    val: Val,
}

pub fn make_internal_values() -> Vec<InternalValue> {
    vec![
        InternalValue {
            name: "Type",
            val: Val::Type(Rc::new(Type::Type)),
        },
        InternalValue {
            name: "Int",
            val: Val::Type(Rc::new(Type::Int)),
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
            val: Val::Type(Rc::new(Type::Unit)),
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
        InternalValue {
            name: "Bool",
            val: Val::Type(Rc::new(Type::Bool)),
        },
        InternalValue {
            name: "true",
            val: Val::Bool(true),
        },
        InternalValue {
            name: "false",
            val: Val::Bool(false),
        },
        InternalValue {
            name: "eq",
            val: Val::Function(Function::Arrow(ArrFunc::IntEq)),
        },
    ]
}

fn get_internal_val(name: &str) -> Option<Val> {
    for internal in make_internal_values().iter() {
        if internal.name == name {
            // println!(
            //     "Index: {} for internal value {} = {}",
            //     idx, internal.name, name
            // );
            return Some(internal.val.clone());
        }
    }
    // panic!("name: '{}', does not exist as an internal value", name)
    None
}

//TODO: create a better error message
#[derive(Debug)]
pub enum ResolveError {
    UnknownName(String),
    NotALocalVariable(String),
    UnknownSetOfVariants(HashSet<String>),
}

pub struct EnumDefinition {
    name: String,
    variants: HashSet<String>,
}

// Resolves all names inside an expression and converts them into an indices of the provided array
fn resolve_expr(
    global_names: &Vec<String>,
    local_names: &mut Vec<String>,
    case_groups: &HashMap<String, Vec<String>>,
    expr: UnresolvedExpr,
) -> Result<Expr, ResolveError> {
    match expr {
        UnresolvedExpr::Apply(func, arg) => {
            let rfunc = Rc::new(resolve_expr(global_names, local_names, case_groups, *func)?);
            let rarg = Rc::new(resolve_expr(global_names, local_names, case_groups, *arg)?);
            Ok(Expr::Apply(rfunc, rarg))
        }
        UnresolvedExpr::Function {
            name,
            input_type,
            output,
        } => {
            let input_type = resolve_expr(global_names, local_names, case_groups, *input_type)?;
            local_names.push(name.clone());
            let output = resolve_expr(global_names, local_names, case_groups, *output)?;
            assert_eq!(local_names.pop().unwrap(), name);
            Ok(Expr::Function {
                // variable_name: name,
                input_type: Rc::new(input_type),
                output: Rc::new(output),
            })
        }
        // TODO: Add resolving to enum variants and enum types
        UnresolvedExpr::Variable(s) => {
            // local variables shadow globals shadow internal
            if let Some(value) = get_from_locals(local_names, &s) {
                return Ok(Expr::Local(value));
            }
            for (i, name) in global_names.iter().enumerate() {
                if *name == s {
                    return Ok(Expr::Global(i));
                }
            }
            match get_internal_val(&s) {
                Some(v) => Ok(Expr::Value(Rc::new(v))),
                None => Err(ResolveError::UnknownName(s)),
            }
        }
        UnresolvedExpr::IntLit(n) => Ok(Expr::IntLit(n)),
        UnresolvedExpr::Unit => Ok(Expr::Value(Rc::new(Val::Unit))),
        UnresolvedExpr::Match(Matching { matchend, branches }) => {
            let Some(local_idx) = get_from_locals(local_names, &matchend) else {
                // right now I am only allowing for local variables in match statements.
                return Err(ResolveError::NotALocalVariable(matchend));
            };

            'outer: for (enum_name, enum_variants) in case_groups {
                // verify if this enum's variants are equal to the branches
                if enum_variants.len() != branches.len() {
                    continue;
                }
                for case in branches.keys() {
                    if !enum_variants.contains(case) {
                        continue 'outer;
                    }
                }
                // The branches have the same exact case names as the enum's variants,
                // Now we resolve the internal branches
                let mut resolved_branches = Vec::new();
                for variant in enum_variants {
                    let resolved_branch = resolve_expr(
                        global_names,
                        local_names,
                        case_groups,
                        branches.get(variant).unwrap().clone(),
                    )?;

                    resolved_branches.push(Rc::new(resolved_branch));
                }
                // dbg!(&resolved_branches);
                return Ok(Expr::Match {
                    enum_name: enum_name.clone(),
                    local: local_idx,
                    branches: resolved_branches,
                });
            }
            let case_names = HashSet::from_iter(branches.into_keys());

            Err(ResolveError::UnknownSetOfVariants(case_names))
        }
    }
}

// Find the name in a list of local names
fn get_from_locals(locals: &mut Vec<String>, s: &String) -> Option<usize> {
    for (i, name) in locals.iter().rev().enumerate() {
        // here `i` gives the debrujin indices
        if **name == *s {
            return Some(i);
        }
    }
    None
}

// resolves references to local, global, and internally defined names. Multiple variables in the same
// thing gives undefined behavior currently.
// TODO: Allow for name overloading (make the types of variables matter)
fn resolve_exprs(
    global_names: &Vec<String>,
    case_groups: &HashMap<String, Vec<String>>,
    exprs: Vec<UnresolvedExpr>,
) -> Result<Vec<Rc<Expr>>, ResolveError> {
    let mut resolved_program: Vec<Rc<Expr>> = Vec::new();
    for e in exprs {
        let resolved = resolve_expr(&global_names, &mut Vec::new(), case_groups, e.clone())?;
        resolved_program.push(Rc::new(resolved));
    }
    Ok(resolved_program)
}

impl Expr {
    // gets the type of a value. While obtaining the value it also recursively checks that
    // the type of everything inside the expression has no type errors.
    fn get_type_checked_with_locals(
        &self,
        globals: &Vec<Rc<Expr>>,
        locals: &mut Vec<Type>,
    ) -> Result<Rc<Type>, RuntimeError> {
        match self {
            Expr::Apply(func, args) => {
                let func_type = func.clone().get_type_checked_with_locals(globals, locals)?;
                let args_type = args.clone().get_type_checked_with_locals(globals, locals)?;
                match func_type.as_ref() {
                    Type::FunctionType(input_type, output_type) => {
                        if args_type == *input_type {
                            Ok(output_type.clone())
                        } else {
                            Err(RuntimeError::TypesMismatch {
                                expected: input_type.as_ref().clone(),
                                found: args_type.as_ref().clone(),
                            })
                        }
                    }
                    _ => Err(RuntimeError::NotFunctionType {
                        func: func.as_ref().clone(),
                        args: args.as_ref().clone(),
                    }),
                }
            }
            Expr::Function {
                // variable_name: _,
                input_type,
                output,
            } => {
                let runtime_val = interpret(globals.clone(), input_type)?;
                let input_type = runtime_val.clone().get_as_type()?;
                Ok(Rc::new(Type::FunctionType(
                    input_type,
                    output.get_type_checked_with_locals(globals, locals)?,
                )))
            }
            Expr::Local(i) => Ok(Rc::new(locals[locals.len() - 1 - i].clone())),
            Expr::Global(i) => {
                <Expr as Clone>::clone(&globals[*i]).get_type_checked_with_locals(globals, locals)
            }
            Expr::IntLit(_) => Ok(Rc::new(Type::Int)),
            Expr::Value(val) => Ok(val.get_type(globals)),
            Expr::Match {
                enum_name,
                local,
                branches,
            } => {
                let Some(e) = branches.get(0) else {
                    panic!("Don't know how to type check with 0 branches")
                };
                let target_type = e.get_type_checked_with_locals(globals, locals)?;
                for i in 1..branches.len() {
                    let other_branch_type =
                        branches[i].get_type_checked_with_locals(globals, locals)?;
                    if other_branch_type != target_type {
                        return Err(RuntimeError::DifferentlyTypedBranches(
                            e.as_ref().clone(),
                            branches[i].as_ref().clone(),
                        ));
                    }
                }
                Ok(target_type)
            }
        }
    }
}

pub fn is_wellformed_type(
    globals: &Vec<Rc<Expr>>,
    maybe_type: &Expr,
) -> Result<Rc<Type>, RuntimeError> {
    let yeah = interpret(globals.clone(), maybe_type)?;
    yeah.get_as_type()
}

// checks the type of each type signature and makes sure that it is a type
pub fn check_wellformed_types(
    globals: &Vec<Rc<Expr>>,
    globals_types: Vec<Rc<Expr>>,
) -> Result<Vec<Rc<Type>>, RuntimeError> {
    let mut types = Vec::new();
    for type_expr in globals_types {
        let type_sig = interpret(globals.clone(), &type_expr)?;
        types.push(type_sig.get_as_type()?);
    }

    Ok(types)
}

pub struct UnresolvedProgram {
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
                Some(v) => panic!("Multiple enums have the same name"),
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
}

// TODO: make a Program type
pub fn make_program<'a>(
    src: &'a str,
) -> Result<(Vec<String>, Vec<Rc<Expr>>, Vec<Rc<Expr>>), GenericError<'a>> {
    // parsing
    let ast: Vec<Command> = parsing::parse_src(src).map_err(GenericError::ParseError)?;
    let prog = separate_commands(ast);
    // Name resolution
    let globals = resolve_exprs(&prog.def_names, &prog.enums, prog.def_values)
        .map_err(GenericError::ResolutionError)?;
    let resolved_evals = resolve_exprs(&prog.def_names, &prog.enums, prog.to_evaluate)
        .map_err(GenericError::ResolutionError)?;
    let resolved_types = resolve_exprs(&prog.def_names, &prog.enums, prog.def_types)
        .map_err(GenericError::ResolutionError)?;
    // Type checking
    let checked_types =
        check_wellformed_types(&globals, resolved_types).map_err(GenericError::RuntimeError);
    dbg!(&globals);
    Ok((prog.def_names, globals, resolved_evals))
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
        let result = interpret(resolved_values.clone(), &e);
        println!("evaluation result := {:?}", result);
    }
}
