use std::rc::Rc;

use crate::{
    Atomic, Expr, Type,
    runtime::{RuntimeError, Val, interpret},
};

// NOTE: I wrote this code before I realized that type checking with
// a dependent language requires the ability for there to be free-variables.
// Because of that, most of this code will likely need to be scrapped, but it's
// still useful to keep around right now.

impl Expr {
    // gets the type of this expression, given the global variables. It also
    // recursively checks that the type of everything inside the expression has no type errors.
    fn get_type_checked(
        &self,
        globals: &Vec<Rc<Expr>>,
        globals_types: &Vec<Rc<Type>>,
    ) -> Result<Rc<Type>, CheckerError> {
        let mut locals = Vec::new();
        let res = self.get_type_checked_with_locals(globals, globals_types, &mut locals);
        // If this assert is panicking its likely because you're returning an error
        // with a ? before popping a local variable off the stack
        assert_eq!(locals.len(), 0);
        res
    }
    fn get_type_checked_with_locals(
        &self,
        globals: &Vec<Rc<Expr>>,
        globals_types: &Vec<Rc<Type>>,
        locals: &mut Vec<Rc<Type>>,
    ) -> Result<Rc<Type>, CheckerError> {
        dbg!(self);
        // dbg!(&locals);
        match self {
            Expr::Apply(func, args) => {
                println!("checking Expr::Apply(\n\t{:?},\n\t{:?}\n)", func, args);
                let func_type =
                    func.get_type_checked_with_locals(globals, globals_types, locals)?;
                println!("function has type: {:?}", &func_type);
                let args_type =
                    args.get_type_checked_with_locals(globals, globals_types, locals)?;
                println!("argument has type: {:?}", &args_type);

                match func_type.as_ref() {
                    Type::FunctionType(input_type, output_type) => {
                        if args_type == *input_type {
                            println!("{:?} == {:?} checks!", &args_type, input_type);
                            Ok(output_type.clone())
                        } else {
                            Err(CheckerError::TypesMismatch {
                                expected: input_type.as_ref().clone(),
                                found: args_type.as_ref().clone(),
                            })
                        }
                    }
                    _ => Err(CheckerError::NotFunctionType {
                        func: func.as_ref().clone(),
                        args: args.as_ref().clone(),
                    }),
                }
            }
            Expr::Function {
                input_type: type_expr,
                output,
            } => {
                let prev_locals_len = locals.len();
                let val: Rc<Val> = interpret(globals.clone(), type_expr)?;
                let input_type = val.get_as_type()?;
                locals.push(input_type.clone());
                let checked_output_type =
                    output.get_type_checked_with_locals(globals, globals_types, locals);
                assert_eq!(locals.pop(), Some(input_type.clone()));
                assert_eq!(locals.len(), prev_locals_len);
                Ok(Rc::new(Type::FunctionType(
                    input_type,
                    checked_output_type?,
                )))
            }
            Expr::Atom(Atomic::StringLit(_)) => Ok(Rc::new(Type::String)),
            Expr::Atom(Atomic::Local(i)) => Ok(locals[locals.len() - 1 - i].clone()),
            Expr::Atom(Atomic::Global(i)) => Ok(globals_types[*i].clone()),
            Expr::Atom(Atomic::IntLit(_)) => Ok(Rc::new(Type::Int)),
            Expr::Atom(Atomic::Value(val)) => Ok(Rc::new(val.get_type())),
            Expr::Atom(Atomic::EnumVariant(ename, _)) => Ok(Rc::new(Type::Enum(ename.clone()))),
            Expr::Atom(Atomic::EnumType(_)) => Ok(Rc::new(Type::Type)),
            Expr::Match {
                enum_name: _,
                local: _,
                branches,
            } => {
                let Some(e) = branches.get(0) else {
                    panic!("Don't know how to type check match expression with 0 branches")
                };
                let target_type = e.get_type_checked_with_locals(globals, globals_types, locals)?;
                for i in 1..branches.len() {
                    let other_branch_type =
                        branches[i].get_type_checked_with_locals(globals, globals_types, locals)?;
                    if other_branch_type != target_type {
                        return Err(CheckerError::DifferentlyTypedBranches(
                            e.as_ref().clone(),
                            branches[i].as_ref().clone(),
                        ));
                    }
                }
                Ok(target_type)
            }
            Expr::Let {
                new_value_type,
                new_value,
                expr,
            } => {
                let new_value_type_given =
                    interpret(globals.clone(), new_value_type)?.get_as_type()?;

                let new_value_type_found =
                    new_value.get_type_checked_with_locals(globals, globals_types, locals)?;
                if new_value_type_given != new_value_type_found {
                    return Err(CheckerError::TypesMismatch {
                        expected: new_value_type_given.as_ref().clone(),
                        found: new_value_type_found.as_ref().clone(),
                    });
                };
                locals.push(new_value_type_given.clone());
                let res = expr.get_type_checked_with_locals(globals, globals_types, locals);
                assert_eq!(locals.pop().unwrap(), new_value_type_given);
                res
            }
        }
    }
}

#[derive(Debug)]
pub enum CheckerError {
    TypesMismatch { expected: Type, found: Type },
    NotFunctionType { func: Expr, args: Expr },
    DifferentlyTypedBranches(Expr, Expr),
    TypeCalculationError(RuntimeError),
}

impl From<RuntimeError> for CheckerError {
    fn from(value: RuntimeError) -> Self {
        CheckerError::TypeCalculationError(value)
    }
}

pub fn type_check_globals(
    globals: &Vec<Rc<Expr>>,
    given_global_types: &Vec<Rc<Type>>,
) -> Result<(), CheckerError> {
    for (expr, given) in globals.iter().zip(given_global_types.iter()) {
        let found_type = expr.get_type_checked(globals, given_global_types)?;
        if &found_type != given {
            return Err(CheckerError::TypesMismatch {
                expected: given.as_ref().clone(),
                found: found_type.as_ref().clone(),
            });
        }
    }
    Ok(())
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
        // wrt the note at the top, notice how this requires interpretting on non-typechecked code here.
        let type_sig = interpret(globals.clone(), &type_expr)?;
        types.push(type_sig.get_as_type()?);
    }

    Ok(types)
}
