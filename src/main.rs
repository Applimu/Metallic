use std::env;
use std::fs::File;
use std::io::Read;

use parsing::{Binding, Command, Expr};

mod parsing;
#[cfg(test)]
mod tests;

// an expression where each name is known
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ResolvedExpr {
    Apply(Box<ResolvedExpr>, Box<ResolvedExpr>),
    Function {
        input_name: String,
        input_type: Box<ResolvedExpr>,
        output: Box<ResolvedExpr>,
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
pub const INTERNAL_VALUES: [InternalValue; 5] = [
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
];

// Resolves all names inside an expression and turns it into an index of the provided array
// TODO: make this a result
fn resolve_expr(
    globals: &Vec<String>,
    locals: &mut Vec<String>,
    expr: Expr,
) -> Option<ResolvedExpr> {
    match expr {
        Expr::Apply(func, arg) => {
            let rfunc = Box::new(resolve_expr(globals, locals, *func)?);
            let rarg = Box::new(resolve_expr(globals, locals, *arg)?);
            Some(ResolvedExpr::Apply(rfunc, rarg))
        }
        Expr::Function {
            name,
            input_type,
            output,
        } => {
            let input_type = resolve_expr(globals, locals, *input_type)?;
            locals.push(name.clone());
            let output = resolve_expr(globals, locals, *output)?;
            assert_eq!(locals.pop().unwrap(), name);
            Some(ResolvedExpr::Function {
                input_name: name,
                input_type: Box::new(input_type),
                output: Box::new(output),
            })
        }
        Expr::Variable(s) => {
            // local variables shadow globals shadow internal
            for (i, name) in locals.iter().rev().enumerate() {
                // here `i` gives the debrujin indices
                if **name == s {
                    return Some(ResolvedExpr::Local(i));
                }
            }
            for (i, name) in globals.iter().enumerate() {
                if *name == s {
                    return Some(ResolvedExpr::Global(i));
                }
            }
            for (i, internal) in INTERNAL_VALUES.iter().enumerate() {
                // println!("Testing {} against {} !!", &s, internal.name);
                if internal.name == &s {
                    return Some(ResolvedExpr::Internal(i));
                }
            }
            // if the variable name is not any of the above, crash
            None
        }
        Expr::IntLit(n) => Some(ResolvedExpr::IntLit(n)),
        Expr::Unit => Some(ResolvedExpr::Unit),
    }
}

fn resolve_exprs(names: &Vec<String>, exprs: Vec<Expr>) -> Option<Vec<ResolvedExpr>> {
    let mut resolved_program: Vec<ResolvedExpr> = Vec::new();
    for e in exprs {
        let resolved = resolve_expr(&names, &mut Vec::new(), e.clone())?;
        resolved_program.push(resolved);
    }
    Some(resolved_program)
}

impl ResolvedExpr {
    // gets the type of an expression without type checking anything inside.
    // Basically when it gets to a function type it doesn't check if the inputs are correct,
    // while `get_type_checked` does check if the inputs are correct. Idk which is more useful
    // so I am keeping both right now.
    fn get_type_unchecked(self, globals: &Vec<ResolvedExpr>) -> Option<Type> {
        match self {
            ResolvedExpr::Apply(func, _) => match func.get_type_unchecked(globals) {
                Some(Type::FunctionType(_, output_type)) => Some(*output_type),
                _ => None,
            },
            ResolvedExpr::Function {
                input_name,
                input_type,
                output,
            } => todo!(),
            ResolvedExpr::Local(i) => todo!(),
            ResolvedExpr::Global(i) => {
                todo!();
                // let mbtype = interpret_unchecked(globals, locals, globals[i].type_sig.clone())?;
                // mbtype.get_as_type()
            }
            ResolvedExpr::Internal(i) => Some(INTERNAL_VALUES[i].val.clone().get_type(globals)),
            ResolvedExpr::IntLit(_) => Some(Type::Int),
            ResolvedExpr::Unit => Some(Type::Unit),
        }
    }

    // gets the type of a value. While obtaining the value it also recursively checks
    // the type of everything inside the expression.
    fn get_type_checked(self, globals: &Vec<ResolvedExpr>) -> Option<Type> {
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
            ResolvedExpr::Function {
                input_name,
                input_type,
                output,
            } => todo!(),
            ResolvedExpr::Local(i) => todo!(),
            ResolvedExpr::Global(i) => {
                todo!();
                // let mbtype = interpret_unchecked(globals, globals[i].type_sig.clone())?;
                // mbtype.get_as_type()
            }
            ResolvedExpr::Internal(i) => Some(INTERNAL_VALUES[i].val.clone().get_type(globals)),
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

pub fn basic_type_check(
    globals: &Vec<ResolvedExpr>,
    global_type_sigs: &Vec<ResolvedExpr>,
) -> Option<Vec<CheckedDefinition>> {
    let mut out: Vec<CheckedDefinition> = Vec::new();
    for (def, type_sig) in globals.iter().zip(global_type_sigs.iter()) {
        out.push(CheckedDefinition {
            get_type: type_sig.clone().get_type_checked(globals)?,
            value: def.clone(),
        })
    }
    Some(out)
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RuntimeVal {
    Type(Type),
    IntLit(i64),
    Unit,
    Function(Type, ResolvedExpr),
    Bool(bool),
    Add, // add function
    PartialAdd(i64),
    Fun, // function type operator
    PartialFun(Type),
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
            RuntimeVal::Fun => Some(RuntimeVal::PartialFun(arg.get_as_type()?)),
            RuntimeVal::PartialFun(t1) => Some(RuntimeVal::Type({
                let t2 = arg.get_as_type()?;
                Type::FunctionType(Box::new(t1), Box::new(t2))
            })),
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

    fn get_type(self, globals: &Vec<ResolvedExpr>) -> Type {
        match self {
            RuntimeVal::Type(_) => Type::Type,
            RuntimeVal::IntLit(_) => Type::Int,
            RuntimeVal::Function(t, e) => Type::FunctionType(
                Box::new(t),
                Box::new(
                    e.get_type_checked(globals)
                        .expect("Bad expression caused function to have ill-formed type"),
                ),
            ),
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

fn interpret_unchecked(
    globals: &Vec<ResolvedExpr>,
    locals: &mut Vec<RuntimeVal>,
    to_eval: ResolvedExpr,
) -> Option<RuntimeVal> {
    match to_eval {
        ResolvedExpr::Apply(func, arg) => {
            let f: RuntimeVal = interpret_unchecked(globals, locals, *func)?;
            let x: RuntimeVal = interpret_unchecked(globals, locals, *arg)?;
            f.apply_as_fn(x)
        }
        ResolvedExpr::Function {
            input_name,
            input_type,
            output,
        } => todo!("Function evaluation not implemented yet!"),
        ResolvedExpr::Local(i) => Some(locals[locals.len() - i].clone()),
        ResolvedExpr::Global(i) => interpret_unchecked(globals, locals, globals.get(i)?.clone()),
        ResolvedExpr::Internal(i) => INTERNAL_VALUES.get(i).map(|v| v.val.clone()),
        ResolvedExpr::IntLit(n) => Some(RuntimeVal::IntLit(n.try_into().unwrap())),
        ResolvedExpr::Unit => Some(RuntimeVal::Unit),
    }
}

fn interpret(
    globals: &Vec<ResolvedExpr>,
    locals: &mut Vec<ResolvedExpr>,
    to_eval: ResolvedExpr,
) -> Option<RuntimeVal> {
    match to_eval {
        ResolvedExpr::Apply(func, arg) => {
            let f: RuntimeVal = interpret(globals, locals, *func)?;
            let x: RuntimeVal = interpret(globals, locals, *arg)?;
            f.apply_as_fn(x)
        }
        ResolvedExpr::Function {
            input_name,
            input_type,
            output,
        } => {
            let input_type = interpret(globals, locals, *input_type)?;
            Some(RuntimeVal::Function(input_type.get_as_type()?, *output))
        }
        ResolvedExpr::Local(i) => todo!(),
        ResolvedExpr::Global(i) => interpret(globals, locals, globals.get(i)?.clone()),
        ResolvedExpr::Internal(i) => INTERNAL_VALUES.get(i).map(|v| v.val.clone()),
        ResolvedExpr::IntLit(n) => Some(RuntimeVal::IntLit(n.try_into().unwrap())),
        ResolvedExpr::Unit => Some(RuntimeVal::Unit),
    }
}

// Unpacks the list of commands into the different types of commands.
// All three arrays are expected to have the same length, the first is the names of all bound
// values, the second is the type signatures and the third is the values
pub fn unpack(commands: Vec<Command>) -> (Vec<String>, Vec<Expr>, Vec<Expr>) {
    commands
        .into_iter()
        .map(|c| match c {
            Command::Binding(Binding {
                var_name,
                type_sig,
                value,
            }) => (var_name, type_sig, value),
        })
        .collect() // its so wild how powerful .collect() is
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

    let ast: Vec<Command> = parsing::parse_src(src.as_str());
    let (def_names, pre_type_exprs, pre_val_exprs) = unpack(ast);
    dbg!(&def_names);
    dbg!(&pre_type_exprs);
    dbg!(&pre_val_exprs);
    let resolved_values =
        resolve_exprs(&def_names, pre_val_exprs).expect("Failed to resolve value names");
    // let resolved_types =
    //     resolve_exprs(&def_names, pre_type_exprs).expect("Failed to resolve type names");
    // let checked = basic_type_check(&resolved).expect("Type checking failed");
    // dbg!(&checked);
    for i in 0..def_names.len() {
        let mut locals = Vec::new();
        let result = interpret(&resolved_values, &mut locals, resolved_values[i].clone());
        assert!(locals.len() == 0);
        println!("{} := {:?}", def_names[i].clone(), result);
    }
}
