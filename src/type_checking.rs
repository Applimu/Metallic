use std::rc::Rc;

use crate::{
    Atomic, Expr, Program, Type,
    runtime::{Context, RuntimeError},
};

/// An error that could occur during type checking
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

/// A context for checking types
pub struct CheckingContext<'a> {
    pub globals: &'a [Rc<Expr>],
    pub global_types: &'a [Rc<Expr>],
    pub locals: Vec<Rc<Type>>,
}

impl Atomic {
    fn get_type(&self, ctx: &mut CheckingContext) -> Rc<Type> {
        match self {
            Atomic::Local(i) => ctx.locals[*i].clone(),
            Atomic::Global(i) => {
                let type_expr = ctx.global_types[*i].as_ref();
                // We assume that all types are well-formed types
                // check_type(ctx, type_expr, &Type::Type);
                let mut eval_ctx = Context::from_checking_ctx(ctx);
                eval_ctx
                    .interpret(type_expr)
                    .unwrap()
                    .get_as_type()
                    .unwrap()
            }
            Atomic::Internal(internal) => Rc::new(internal.get_type()),
            Atomic::EnumVariant(name, _) => Rc::new(Type::Enum(name.clone())),
            Atomic::EnumType(_) => Rc::new(Type::Type),
            Atomic::IntLit(_) => Rc::new(Type::Int),
            Atomic::StringLit(_) => Rc::new(Type::String),
        }
    }
}

/// Returns `Ok(())` if the types are definitionally equal, and otherwise returns
/// `Err(CheckerError::TypesMismatch)`
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

/// Verifies that an expression has a certain type in a given context
fn check_type(
    ctx: &mut CheckingContext,
    expr: &Expr,
    signature: &Type,
) -> Result<(), CheckerError> {
    match expr {
        Expr::Apply(func, arg) => {
            // three options:
            // 1) infer type of func and then check arg's type and
            //     signature are equal to the type in func
            // 2) infer type of arg and then check func's type
            // 3) infer both the func and arg and then verify everything

            // Here we chose option 1
            match infer_type(ctx, func)?.as_ref() {
                Type::FunctionType(input_type, output_type) => {
                    types_match(signature, output_type)?;
                    check_type(ctx, arg, input_type.as_ref())?;
                    Ok(())
                }
                _ => Err(CheckerError::NotFunctionType {
                    func: func.as_ref().clone(),
                    args: arg.as_ref().clone(),
                }),
            }
        }
        Expr::Function { input_type, output } => {
            check_type(ctx, &input_type, &Type::Type)?;
            match signature {
                Type::FunctionType(expected_inp, expected_out) => {
                    let mut eval_ctx = Context::from_checking_ctx(ctx);
                    let input_type = eval_ctx.interpret(input_type)?.get_as_type()?;
                    types_match(expected_inp, input_type.as_ref())?;
                    ctx.locals.push(input_type.clone());
                    check_type(ctx, output, expected_out)?;
                    assert_eq!(ctx.locals.pop(), Some(input_type.clone()));
                    Ok(())
                }
                _ => panic!("Make this checker error: checked non-function w/ function"),
            }
        }
        Expr::Atom(atomic) => {
            let a_type = atomic.get_type(ctx);
            types_match(signature, a_type.as_ref())
        }
        Expr::Match {
            enum_name,
            matchend,
            branches,
        } => {
            check_type(ctx, &matchend, &Type::Enum(enum_name.clone()))?;
            for branch in branches.iter() {
                check_type(ctx, branch, signature)?;
            }
            Ok(())
        }
        Expr::Let {
            new_value_type,
            new_value,
            expr,
        } => {
            check_type(ctx, new_value_type, &Type::Type)?;
            let mut eval_ctx = Context::from_checking_ctx(ctx);
            let new_value_type = eval_ctx.interpret(new_value_type)?.get_as_type()?;
            check_type(ctx, new_value, new_value_type.as_ref())?;
            ctx.locals.push(new_value_type.clone());
            check_type(ctx, expr, signature)?;
            // This shouldn't panic unless the check_type can change the length of ctx.locals
            assert_eq!(ctx.locals.pop(), Some(new_value_type.clone()));
            Ok(())
        }
    }
}

/// Infers what the type of an expression is in a given context
fn infer_type(ctx: &mut CheckingContext, expr: &Expr) -> Result<Rc<Type>, CheckerError> {
    match expr {
        Expr::Apply(func, arg) => match infer_type(ctx, func)?.as_ref() {
            Type::FunctionType(input_type, output_type) => {
                check_type(ctx, arg, input_type)?;
                return Ok(output_type.clone());
            }
            _ => Err(CheckerError::NotFunctionType {
                func: func.as_ref().clone(),
                args: arg.as_ref().clone(),
            }),
        },
        Expr::Function { input_type, output } => {
            check_type(ctx, input_type, &Type::Type)?;
            let mut eval_ctx = Context::from_checking_ctx(ctx);
            let input_type = eval_ctx.interpret(input_type)?.get_as_type()?;
            ctx.locals.push(input_type.clone());
            let output_type = infer_type(ctx, output)?;
            assert_eq!(ctx.locals.pop(), Some(input_type.clone()));
            Ok(Rc::new(Type::FunctionType(input_type, output_type)))
        }
        Expr::Atom(atomic) => Ok(atomic.get_type(ctx)),
        Expr::Match {
            enum_name,
            matchend,
            branches,
        } => {
            check_type(ctx, &matchend, &Type::Enum(enum_name.clone()))?;
            let first_branch = branches
                .get(0)
                .expect("Dont know how to type check an empty match");
            let output_type = infer_type(ctx, &first_branch)?;
            for branch in branches.iter().skip(1) {
                check_type(ctx, branch, output_type.as_ref())?;
            }
            Ok(output_type)
        }
        Expr::Let {
            new_value_type,
            new_value,
            expr,
        } => {
            check_type(ctx, new_value_type, &Type::Type)?;
            let mut eval_ctx = Context::from_checking_ctx(ctx);
            let new_value_type = eval_ctx.interpret(new_value_type)?.get_as_type()?;

            check_type(ctx, new_value, &new_value_type)?;

            ctx.locals.push(new_value_type.clone());
            let output_type = infer_type(ctx, expr);
            assert_eq!(ctx.locals.pop(), Some(new_value_type.clone()));
            output_type
        }
    }
}

/// Verifies that a program has no type errors
/// In the future I may want to change it so that it adds type information onto
/// every `Expr`
pub fn type_check_program(prog: &Program) -> Result<(), CheckerError> {
    for type_expr in prog.global_types.iter() {
        let mut new_ctx = CheckingContext {
            globals: &prog.globals,
            global_types: &prog.global_types,
            locals: Vec::new(),
        };
        check_type(&mut new_ctx, type_expr, &Type::Type)?
    }
    println!("All types are well-formed!");

    for i in 0..prog.globals.len() {
        let global = &prog.globals[i];
        let mut eval_ctx = Context::new(&prog.globals, &prog.global_types);
        let global_type = eval_ctx
            .interpret(&prog.global_types[i])
            .unwrap()
            .get_as_type()
            .expect("Verifying well-formedness of types did not work");
        let mut new_ctx = CheckingContext {
            globals: &prog.globals,
            global_types: &prog.global_types,
            locals: Vec::new(),
        };
        check_type(&mut new_ctx, global, global_type.as_ref())?
    }
    Ok(())
}
