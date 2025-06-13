use std::rc::Rc;

use crate::{
    Atomic, Expr, Type,
    runtime::{RuntimeError, Val, interpret},
};

// NOTE: I wrote this code before I realized that type checking with
// a dependent language requires the ability for there to be free-variables.
// Because of that, most of this code will likely need to be scrapped, but it's
// still useful to keep around right now.

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

// converts every type signature in to an actual Type
pub fn check_wellformed_types(
    globals: &[Rc<Expr>],
    globals_types: Vec<Rc<Expr>>,
) -> Result<Vec<Rc<Type>>, RuntimeError> {
    let mut types = Vec::new();
    for type_expr in globals_types.iter() {
        let type_sig = interpret(globals, &globals_types, type_expr.as_ref())?;
        types.push(type_sig.get_as_type()?);
    }

    Ok(types)
}

fn types_match(expect: &Type, found: &Type) -> Result<(), CheckerError> {
    if expect == found {
        Ok(())
    } else {
        Err(CheckerError::TypesMismatch {
            expected: expect.clone(),
            found: found.clone(),
        })
    }
}

// Verifies that an expression has a certain type in a context
fn check_type(
    globals: &[Rc<Expr>],
    globals_types: &[Rc<Type>],
    locals: &mut Vec<Rc<Type>>,
    expr: &Expr,
    signature: &Type,
) -> Result<(), CheckerError> {
    match expr {
        Expr::Apply(func, arg) => {
            // three options:
            // 1) infer type of func and then check arg's type and
            //     signature are equal to the type in func
            // 2) infer type of arg and then check func's type
            match infer_type(globals, globals_types, locals, func)?.as_ref() {
                Type::FunctionType(input_type, output_type) => {
                    types_match(signature, output_type)?;
                    check_type(globals, globals_types, locals, arg, input_type.as_ref())?;
                    Ok(())
                }
                _ => Err(CheckerError::NotFunctionType {
                    func: func.as_ref().clone(),
                    args: arg.as_ref().clone(),
                }),
            }
        }
        Expr::Function { input_type, output } => {
            check_type(globals, globals_types, locals, &input_type, &Type::Type)?;
            todo!("Implement interpret_with_locals_with_free_variables")
        }
        Expr::Atom(atomic) => {
            let a_type = atomic.get_type(globals_types, locals);
            types_match(signature, a_type.as_ref())
        }
        Expr::Match {
            enum_name,
            matchend,
            branches,
        } => {
            check_type(
                globals,
                globals_types,
                locals,
                &matchend,
                &Type::Enum(enum_name.clone()),
            )?;
            for branch in branches.iter() {
                check_type(globals, globals_types, locals, branch, signature)?;
            }
            Ok(())
        }
        Expr::Let {
            new_value_type,
            new_value,
            expr,
        } => {
            check_type(globals, globals_types, locals, new_value_type, &Type::Type)?;
            todo!();
            // let new_value_type =
            // interpret_with_locals(globals, locals, new_value_type)?.get_as_type()?;
            // locals.push(new_value_type);
            // let res = check_type(globals, globals_types, locals, expr, signature);
            // assert_eq!(locals.pop(), Some(new_value_type));
            // res
        }
    }
}

// Guesses what the type of an expression is in a context
fn infer_type(
    globals: &[Rc<Expr>],
    globals_types: &[Rc<Type>],
    locals: &mut Vec<Rc<Type>>,
    expr: &Expr,
) -> Result<Rc<Type>, CheckerError> {
    match expr {
        Expr::Apply(func, arg) => {
            match infer_type(globals, globals_types, locals, func)?.as_ref() {
                Type::FunctionType(input_type, output_type) => {
                    check_type(globals, globals_types, locals, arg, input_type)?;
                    return Ok(output_type.clone());
                }
                _ => Err(CheckerError::NotFunctionType {
                    func: func.as_ref().clone(),
                    args: arg.as_ref().clone(),
                }),
            }
        }
        Expr::Function { input_type, output } => {
            check_type(globals, globals_types, locals, input_type, &Type::Type)?;
            todo!("Implement interpret_with_locals_with_free_variables")
        }
        Expr::Atom(atomic) => Ok(atomic.get_type(globals_types, locals)),
        Expr::Match {
            enum_name,
            matchend,
            branches,
        } => {
            check_type(
                globals,
                globals_types,
                locals,
                &matchend,
                &Type::Enum(enum_name.clone()),
            )?;
            let first_branch = branches
                .get(0)
                .expect("Dont know how to type check an empty match");
            let output_type = infer_type(globals, globals_types, locals, &first_branch)?;
            for branch in branches.iter().skip(1) {
                check_type(globals, globals_types, locals, branch, output_type.as_ref())?;
            }
            Ok(output_type)
        }
        Expr::Let {
            new_value_type,
            new_value,
            expr,
        } => {
            check_type(globals, globals_types, locals, new_value_type, &Type::Type)?;
            todo!("Implement interpret_with_locals_with_free_variables")
        }
    }
}
