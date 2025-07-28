use std::rc::Rc;

use crate::type_checking::CheckingContext;
use crate::{Atomic, Expr, Type};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Val {
    IntLit(i64),
    StringLit(String),
    // the unit value, not to be confused with Type::Unit
    Unit,
    // Pair (t1, t2, x,y) has t1: x, t2: y
    Pair(Rc<Type>, Rc<Type>, Rc<Val>, Rc<Val>),
    Function(Function),
    Type(Rc<Type>),
    Enum(String, usize),
    IO(IOAction),
    // usize refers to local variable
    FreeVariable(usize),
}

// TODO: create better error messages
#[derive(Debug, Clone)]
pub enum RuntimeError {
    TypeError { expected: Type, found: Val },
    NotAFunction { value: Val },
    NotAnEnum(Val),
    NotAPair(Val),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IOAction {
    PrintLn(String),
    GetLn(Function),
    Seq(Rc<IOAction>, Rc<IOAction>),
    Done,
}

fn run_io_action(ctx: &mut Context, action: &mut IOAction) -> Result<(), RuntimeError> {
    match action {
        IOAction::PrintLn(s) => {
            println!("{}", s);
            Ok(())
        }
        IOAction::GetLn(f) => {
            let mut s = String::new();
            std::io::stdin().read_line(&mut s).unwrap();
            let mut next_action = f.apply_to(ctx, Rc::new(Val::StringLit(s)))?.get_as_io()?;
            run_io_action(ctx, &mut next_action)
        }
        IOAction::Seq(a, b) => {
            run_io_action(ctx, &mut a.as_ref().clone())?;
            run_io_action(ctx, &mut b.as_ref().clone())
        }
        IOAction::Done => Ok(()),
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Function {
    Closure {
        captured_vars: Vec<Rc<Val>>,
        code: Rc<Expr>,
    },
    PartialApplication(FunctionConstant, Vec<Val>),
}

impl Function {
    fn apply_to(&self, ctx: &mut Context, arg: Rc<Val>) -> Result<Rc<Val>, RuntimeError> {
        match self {
            Function::Closure {
                captured_vars,
                code,
            } => {
                let mut new_locals: Vec<Rc<Val>> = captured_vars.clone();
                // important that we push the new argument on the end
                // to align with Expr::Local(_)s
                new_locals.push(arg);
                let mut new_ctx = Context {
                    globals: ctx.globals,
                    globals_types: ctx.globals_types,
                    // I *believe* that there are never free variables when closures are captured??
                    free_locals: Vec::new(),
                    bound_locals: new_locals,
                };
                new_ctx.interpret(code)
            }
            Function::PartialApplication(function_constant, args) => {
                function_constant.reduce(args.clone(), arg).map(Rc::new)
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FunctionConstant {
    Add,
    Mul,
    Sub,
    IntEq,
    IntLe,

    Fun,
    PairType,

    GetLn,
    PrintLn,

    TypeOfDepProd,      // fn Type: T do (T -> Type) -> Type
    OutputTypeOfMkPair, // fn Type: t1 do (Type: t2) -> t1 & t2

    DepProd,
    Pair,
}

impl FunctionConstant {
    fn reduce(self, args: Vec<Val>, arg: Rc<Val>) -> Result<Val, RuntimeError> {
        let args = Vec::from_iter(args.iter().chain(Some(arg.as_ref())).map(Clone::clone));
        match self {
            FunctionConstant::Add => {
                if args.len() >= 2 {
                    assert!(args.len() == 2);
                    let x = args[0].get_as_int()?;
                    let y = args[1].get_as_int()?;
                    Ok(Val::IntLit(x + y))
                } else {
                    Ok(Val::Function(Function::PartialApplication(self, args)))
                }
            }
            FunctionConstant::Mul => {
                if args.len() >= 2 {
                    assert!(args.len() == 2);
                    let x = args[0].get_as_int()?;
                    let y = args[1].get_as_int()?;
                    Ok(Val::IntLit(x * y))
                } else {
                    Ok(Val::Function(Function::PartialApplication(self, args)))
                }
            }
            FunctionConstant::Sub => {
                if args.len() >= 2 {
                    assert!(args.len() == 2);
                    let x = args[0].get_as_int()?;
                    let y = args[1].get_as_int()?;
                    Ok(Val::IntLit(x - y))
                } else {
                    Ok(Val::Function(Function::PartialApplication(self, args)))
                }
            }
            FunctionConstant::Fun => {
                if args.len() >= 2 {
                    assert!(args.len() == 2);
                    let x = args[0].get_as_type()?;
                    let y = args[1].get_as_type()?;
                    Ok(Val::Type(Rc::new(Type::FunctionType(x, y))))
                } else {
                    Ok(Val::Function(Function::PartialApplication(self, args)))
                }
            }
            FunctionConstant::PairType => {
                if args.len() >= 2 {
                    assert!(args.len() == 2);
                    let x = args[0].get_as_type()?;
                    let y = args[1].get_as_type()?;
                    Ok(Val::Type(Rc::new(Type::Pair(x, y))))
                } else {
                    Ok(Val::Function(Function::PartialApplication(self, args)))
                }
            }
            FunctionConstant::IntEq => {
                if args.len() >= 2 {
                    assert!(args.len() == 2);
                    let x = args[0].get_as_int()?;
                    let y = args[1].get_as_int()?;
                    Ok(Val::Enum("Bool".to_owned(), if x == y { 1 } else { 0 }))
                } else {
                    Ok(Val::Function(Function::PartialApplication(self, args)))
                }
            }
            FunctionConstant::IntLe => {
                if args.len() >= 2 {
                    assert!(args.len() == 2);
                    let x = args[0].get_as_int()?;
                    let y = args[1].get_as_int()?;
                    Ok(Val::Enum("Bool".to_owned(), if x <= y { 1 } else { 0 }))
                } else {
                    Ok(Val::Function(Function::PartialApplication(self, args)))
                }
            }
            FunctionConstant::GetLn => {
                if args.len() >= 1 {
                    assert!(args.len() == 1);
                    let x = args[0].get_as_fn()?;
                    Ok(Val::IO(IOAction::GetLn(x.clone())))
                } else {
                    Ok(Val::Function(Function::PartialApplication(self, args)))
                }
            }
            FunctionConstant::PrintLn => {
                if args.len() >= 1 {
                    assert!(args.len() == 1);
                    let x = args[0].get_as_string()?;
                    Ok(Val::IO(IOAction::PrintLn(x)))
                } else {
                    Ok(Val::Function(Function::PartialApplication(self, args)))
                }
            }
            FunctionConstant::TypeOfDepProd => {
                if args.len() >= 1 {
                    assert!(args.len() == 1);
                    let x = args[0].get_as_type()?;
                    let t = Rc::new(Type::Type);
                    Ok(Val::Type(Rc::new(Type::FunctionType(
                        Rc::new(Type::FunctionType(x, t.clone())),
                        t,
                    ))))
                } else {
                    Ok(Val::Function(Function::PartialApplication(self, args)))
                }
            }
            FunctionConstant::OutputTypeOfMkPair => {
                if args.len() >= 1 {
                    assert!(args.len() == 1);
                    let t = args[0].get_as_type()?;
                    todo!();
                } else {
                    Ok(Val::Function(Function::PartialApplication(self, args)))
                }
            }
            FunctionConstant::DepProd => {
                if args.len() >= 2 {
                    assert!(args.len() == 2);
                    let t = args[0].get_as_type()?;
                    let f = args[1].get_as_fn()?;
                    Ok(Val::Type(Rc::new(Type::DepProd {
                        family: Rc::new(f.clone()),
                    })))
                } else {
                    Ok(Val::Function(Function::PartialApplication(self, args)))
                }
            }
            FunctionConstant::Pair => {
                if args.len() >= 4 {
                    assert!(args.len() == 4);
                    let left_type = args[0].get_as_type()?;
                    let right_type = args[1].get_as_type()?;
                    let left = Rc::new(args[2].clone());
                    let right = Rc::new(args[3].clone());
                    Ok(Val::Pair(left_type, right_type, left, right))
                } else {
                    Ok(Val::Function(Function::PartialApplication(self, args)))
                }
            }
        }
    }
}

impl Val {
    pub fn get_as_int(&self) -> Result<i64, RuntimeError> {
        match self {
            Val::IntLit(n) => Ok(*n),
            _ => Err(RuntimeError::TypeError {
                expected: Type::Int,
                found: self.clone(),
            }),
        }
    }

    pub fn get_as_string(&self) -> Result<String, RuntimeError> {
        match self {
            Val::StringLit(s) => Ok(s.clone()),
            _ => Err(RuntimeError::TypeError {
                expected: Type::String,
                found: self.clone(),
            }),
        }
    }

    pub fn get_as_io(&self) -> Result<IOAction, RuntimeError> {
        match self {
            Val::IO(io) => Ok(io.clone()),
            _ => Err(RuntimeError::TypeError {
                expected: Type::IO,
                found: self.clone(),
            }),
        }
    }

    // Unwraps this runtime value as a function, and then applies that function to
    // the supplied argument
    pub fn get_as_fn(&self) -> Result<&Function, RuntimeError> {
        match self {
            Val::Function(f) => Ok(f),
            _ => Err(RuntimeError::NotAFunction {
                value: self.clone(),
            }),
        }
    }

    pub fn get_as_type(&self) -> Result<Rc<Type>, RuntimeError> {
        match self {
            Val::Type(t) => Ok(t.clone()),
            c => Err(RuntimeError::TypeError {
                expected: Type::Type,
                found: c.clone(),
            }),
        }
    }

    fn get_as_pair(&self) -> Result<(Rc<Val>, Rc<Val>), RuntimeError> {
        match self {
            Val::Pair(_, _, x, y) => Ok((x.clone(), y.clone())),
            _ => Err(RuntimeError::NotAPair(self.clone())),
        }
    }

    // Given a runtime value, obtains the type of the given value. This is different
    // from get_as_type which asserts that the given value is a type and unwraps it
    pub fn get_type(&self, ctx: &Context) -> Rc<Type> {
        Rc::new(match self {
            Val::Type(_) => Type::Type,
            Val::IntLit(_) => Type::Int,
            Val::StringLit(_) => Type::String,
            Val::Unit => Type::Unit,
            Val::Pair(t1, t2, _, _) => Type::Pair(t1.clone(), t2.clone()),
            Val::Function(Function::Closure {
                captured_vars: _,
                code: _,
            }) => todo!("getting types of closures not implemented :/"),
            Val::Function(Function::PartialApplication(f, args)) => {
                todo!("getting type of partial application not implemented :(")
            }
            Val::Enum(enum_name, _) => Type::Enum(enum_name.clone()),
            Val::IO(_) => Type::IO,
            Val::FreeVariable(idx) => return ctx.free_locals[*idx].clone(),
        })
    }
}

#[derive(Debug, Clone)]
pub struct Context<'a> {
    globals: &'a [Rc<Expr>],
    globals_types: &'a [Rc<Expr>],
    // Only local variables can ever be free variables, so debrujin
    // indices work fine here
    free_locals: Vec<Rc<Type>>,
    bound_locals: Vec<Rc<Val>>,
}

impl<'a> Context<'a> {
    pub const fn new(globals: &'a [Rc<Expr>], globals_types: &'a [Rc<Expr>]) -> Self {
        Self {
            globals,
            globals_types,
            free_locals: Vec::new(),
            bound_locals: Vec::new(),
        }
    }

    pub fn from_checking_ctx(
        CheckingContext {
            globals,
            global_types,
            locals,
        }: &CheckingContext<'a>,
    ) -> Self {
        Self {
            globals,
            globals_types: global_types,
            free_locals: locals.clone(),
            bound_locals: Vec::new(),
        }
    }

    pub fn get_local(&self, local_idx: &usize) -> Rc<Val> {
        if local_idx < &self.free_locals.len() {
            Rc::new(Val::FreeVariable(*local_idx))
        } else {
            self.bound_locals[local_idx - self.free_locals.len()].clone()
        }
    }

    fn interpret_atom(&mut self, atom: &Atomic) -> Result<Rc<Val>, RuntimeError> {
        match atom {
            Atomic::Local(i) => Ok(self.get_local(i).clone()),
            Atomic::Global(i) => {
                // keeping current context isn't necessary for this
                let mut context = Context::new(self.globals, self.globals_types);
                context.interpret(self.globals[*i].as_ref())
            }
            Atomic::IntLit(n) => Ok(Rc::new(Val::IntLit(*n))),
            Atomic::StringLit(s) => Ok(Rc::new(Val::StringLit(s.clone()))),
            Atomic::Internal(val) => Ok(Rc::new(val.val())),
            Atomic::EnumVariant(name, internal_num) => {
                Ok(Rc::new(Val::Enum(name.clone(), *internal_num)))
            }
            Atomic::EnumType(name) => Ok(Rc::new(Val::Type(Rc::new(Type::Enum(name.clone()))))),
        }
    }

    pub fn interpret(&mut self, to_eval: &Expr) -> Result<Rc<Val>, RuntimeError> {
        match to_eval {
            Expr::Apply(func, arg) => {
                let f: Rc<Val> = self.interpret(func)?;
                let x: Rc<Val> = self.interpret(arg)?;
                let res = f.get_as_fn()?.apply_to(self, x);
                res
            }
            Expr::Function {
                input_type: _,
                output,
            } => Ok(Rc::new(Val::Function(Function::Closure {
                captured_vars: self.bound_locals.clone(),
                code: output.clone(),
            }))),
            Expr::Atom(a) => self.interpret_atom(a),
            Expr::Match {
                enum_name,
                matchend,
                branches,
            } => {
                let enum_val = self.interpret(matchend)?;
                match enum_val.as_ref() {
                    Val::Enum(s, i) => {
                        assert_eq!(s, enum_name);
                        self.interpret(&branches[*i])
                    }
                    val => Err(RuntimeError::NotAnEnum(val.clone())),
                }
            }
            Expr::Let {
                new_value_type: _,
                new_value,
                expr,
            } => {
                let new_value = self.interpret(new_value)?;
                self.bound_locals.push(new_value.clone());
                let res = self.interpret(expr);
                assert_eq!(self.bound_locals.pop().unwrap(), new_value);
                res
            }
        }
    }
}

pub fn interpret(
    globals: &[Rc<Expr>],
    globals_types: &[Rc<Expr>],
    expr: &Expr,
) -> Result<Rc<Val>, RuntimeError> {
    let mut ctx = Context::new(globals, globals_types);
    let res = ctx.interpret(expr);
    assert!(ctx.free_locals.len() == 0);
    assert!(ctx.bound_locals.len() == 0);
    res
}
