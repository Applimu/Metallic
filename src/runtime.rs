use std::rc::Rc;

use crate::{Expr, Type};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Val {
    IntLit(i64),
    Bool(bool),
    Unit,
    // Should Pair keep the types of the values?
    Pair(Rc<Val>, Rc<Val>),
    Function(Function),
    Type(Rc<Type>),
    Enum(String, usize),
}

// TODO: create better error messages
#[derive(Debug, Clone)]
pub enum RuntimeError {
    TypeError { expected: Type, found: Val },
    TypesMismatch { expected: Type, found: Type },
    NotAFunction { value: Val },
    NotFunctionType { func: Expr, args: Expr },
    DifferentlyTypedBranches(Expr, Expr),
    NotAnEnum(Val),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ArrFunc {
    Closure {
        input_type: Rc<Type>,
        captured_vars: Vec<Rc<Val>>,
        code: Rc<Expr>,
    },
    Add,
    PartialAdd(i64),
    Fun,
    PartialFun(Rc<Type>),
    DepProdOf(Rc<Type>),
    PairOf(Rc<Type>, Rc<Type>), // this is of type: t1 -> t2 -> t1 & t2
    PartialPairOf(Rc<Val>, Rc<Type>), // of type: t2 -> t1 & t2
    TypeOfMakePair,             // this is the value: (Type: t1) -> (Type: t2) -> t1 & t2
    TypeOfPartialMakePair(Rc<Type>), // (Type: t2) -> t1 & t2
    IntEq,
    PartialIntEq(i64),
}

impl ArrFunc {
    // NOTE: PERFORMS NO TYPE CHECKING.
    fn apply_to(&self, ctx: &mut Context, arg: Rc<Val>) -> Result<Rc<Val>, RuntimeError> {
        match self {
            ArrFunc::Closure {
                input_type: _,
                captured_vars,
                code: expr,
            } => {
                // dbg!(bound_locals.len());
                let mut new_locals: Vec<Rc<Val>> = captured_vars.clone();
                // important that we push the new argument last as that is
                // the 0th debrujin index
                new_locals.push(arg);
                let mut new_ctx = Context {
                    globals: ctx.globals.clone(),
                    locals: new_locals,
                };
                let result = interpret_with_locals(&mut new_ctx, expr);

                // dbg!(&result);
                result
            }
            ArrFunc::Add => {
                let n: i64 = arg.get_as_int()?;
                Ok(Rc::new(Val::Function(Function::Arrow(
                    ArrFunc::PartialAdd(n),
                ))))
            }
            ArrFunc::PartialAdd(n) => {
                let m = arg.get_as_int()?;
                Ok(Rc::new(Val::IntLit(n + m)))
            }
            ArrFunc::Fun => arg
                .get_as_type()
                .map(|t| Rc::new(Val::Function(Function::Arrow(ArrFunc::PartialFun(t))))),
            ArrFunc::PartialFun(t1) => match arg.get_as_type() {
                Ok(t2) => Ok(Rc::new(Val::Type(Rc::new(Type::FunctionType(
                    t1.clone(),
                    t2,
                ))))),
                Err(e) => Err(e),
            },
            ArrFunc::DepProdOf(t) => Ok(Rc::new(Val::Type(Rc::new(Type::DepProd {
                input_type: t.clone(),
                function: Rc::new(arg.get_as_arr_func()?.clone()),
            })))),
            ArrFunc::PairOf(t1, t2) => Ok(Rc::new(Val::Function(Function::Arrow(
                ArrFunc::PartialPairOf(arg, t2.clone()),
            )))),
            ArrFunc::PartialPairOf(left, t2) => Ok(Rc::new(Val::Pair(left.clone(), arg))),
            ArrFunc::TypeOfMakePair => {
                let t1 = arg.get_as_type()?;
                Ok(Rc::new(Val::Function(Function::Arrow(
                    ArrFunc::TypeOfPartialMakePair(t1.clone()),
                ))))
            }
            ArrFunc::TypeOfPartialMakePair(t1) => {
                let t1_ptr = t1;
                let t2_ptr = arg.get_as_type()?;
                Ok(Rc::new(Val::Type(Rc::new(Type::FunctionType(
                    t1_ptr.clone(),
                    Rc::new(Type::FunctionType(
                        t2_ptr.clone(),
                        Rc::new(Type::Pair(t1_ptr.clone(), t2_ptr.clone())),
                    )),
                )))))
            }
            ArrFunc::IntEq => {
                let x = arg.get_as_int()?;
                Ok(Rc::new(Val::Function(Function::Arrow(
                    ArrFunc::PartialIntEq(x),
                ))))
            }
            ArrFunc::PartialIntEq(x) => {
                let y = arg.get_as_int()?;
                Ok(Rc::new(Val::Bool(*x == y)))
            }
        }
    }

    fn get_input_type(&self) -> Type {
        match self {
            ArrFunc::Closure {
                input_type,
                captured_vars: _,
                code: _,
            } => input_type.as_ref().clone(),
            ArrFunc::Add => Type::Int,
            ArrFunc::PartialAdd(_) => Type::Int,
            ArrFunc::Fun => Type::Type,
            ArrFunc::PartialFun(_) => Type::Type,
            ArrFunc::DepProdOf(t) => Type::FunctionType(t.clone(), Rc::new(Type::Type)),
            // these are bad solutions tbh
            ArrFunc::PairOf(t1, _) => (**t1).clone(),
            ArrFunc::PartialPairOf(_, t2) => (**t2).clone(),
            ArrFunc::TypeOfMakePair => Type::Type,
            ArrFunc::TypeOfPartialMakePair(_) => Type::Type,
            ArrFunc::IntEq => Type::Int,
            ArrFunc::PartialIntEq(_) => Type::Int,
        }
    }

    fn get_output_type(&self, globals: &Vec<Rc<Expr>>) -> Type {
        match self {
            ArrFunc::Closure {
                input_type,
                captured_vars,
                code,
            } => {
                let mut locals_types = captured_vars
                    .iter()
                    .map(|r| r.get_type(globals).as_ref().clone())
                    .collect();

                Type::clone(
                    code.get_type_checked_with_locals(globals, &mut locals_types)
                        .expect("Bad expression caused function to have ill-formed type")
                        .as_ref(),
                )
            }
            ArrFunc::Add => Type::Int,
            ArrFunc::PartialAdd(_) => Type::Int,
            ArrFunc::Fun => Type::Type,
            ArrFunc::PartialFun(_) => Type::Type,
            ArrFunc::DepProdOf(t) => Type::FunctionType(
                Rc::new(Type::FunctionType(t.clone(), Rc::new(Type::Type))),
                Rc::new(Type::Type),
            ),
            ArrFunc::PairOf(t1, t2) => Type::FunctionType(
                t1.clone(),
                Rc::new(Type::FunctionType(
                    t2.clone(),
                    Rc::new(Type::Pair(t1.clone(), t2.clone())),
                )),
            ),
            ArrFunc::PartialPairOf(left, t2) => Type::FunctionType(
                t2.clone(),
                Rc::new(Type::Pair(left.get_type(globals), t2.clone())),
            ),
            ArrFunc::TypeOfMakePair => Type::Type,
            ArrFunc::TypeOfPartialMakePair(_) => Type::Type,
            ArrFunc::IntEq => Type::FunctionType(Rc::new(Type::Int), Rc::new(Type::Bool)),
            ArrFunc::PartialIntEq(_) => Type::Bool,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DependentProduct {
    DepProd,
    Closure {
        // this function is always expected to return a Type
        type_family: ArrFunc,
        captured_vars: Vec<Rc<Val>>,
        code: Rc<Expr>,
    },
    Pair,
    PartialPair(Rc<Type>),
}

impl DependentProduct {
    fn get_input_type(&self) -> Type {
        match self {
            DependentProduct::DepProd => Type::Type,
            Self::Closure {
                type_family: family,
                captured_vars,
                code,
            } => family.get_input_type(),
            DependentProduct::Pair => Type::Type,
            DependentProduct::PartialPair(_) => Type::Type,
        }
    }

    fn get_output_type_fn(&self) -> ArrFunc {
        match self {
            DependentProduct::DepProd => ArrFunc::Closure {
                input_type: Rc::new(Type::Type),
                captured_vars: vec![],
                code: Rc::new(Expr::Apply(
                    Rc::new(Expr::Apply(
                        Rc::new(Expr::Value(Rc::new(Val::Function(Function::Arrow(
                            ArrFunc::Fun,
                        ))))),
                        Rc::new(Expr::Apply(
                            Rc::new(Expr::Apply(
                                Rc::new(Expr::Value(Rc::new(Val::Function(Function::Arrow(
                                    ArrFunc::Fun,
                                ))))),
                                Rc::new(Expr::Local(0)), // the input type
                            )),
                            Rc::new(Expr::Value(Rc::new(Val::Type(Rc::new(Type::Type))))),
                        )),
                    )),
                    Rc::new(Expr::Value(Rc::new(Val::Type(Rc::new(Type::Type))))),
                )),
            },
            DependentProduct::Closure {
                type_family: family,
                captured_vars,
                code,
            } => family.clone(),
            DependentProduct::Pair => ArrFunc::TypeOfMakePair,
            DependentProduct::PartialPair(t1) => ArrFunc::TypeOfPartialMakePair(t1.clone()),
        }
    }

    fn apply_to(&self, ctx: &mut Context, arg: Rc<Val>) -> Result<Rc<Val>, RuntimeError> {
        match self {
            DependentProduct::DepProd => {
                let input_type = arg.get_as_type()?;
                Ok(Rc::new(Val::Function(Function::Arrow(ArrFunc::DepProdOf(
                    input_type,
                )))))
            }
            DependentProduct::Closure {
                type_family,
                captured_vars,
                code,
            } => {
                let mut new_locals = captured_vars.clone();
                new_locals.push(arg);
                let mut new_ctx = Context {
                    globals: ctx.globals.clone(),
                    locals: new_locals,
                };
                let res = interpret_with_locals(&mut new_ctx, &code);

                res
            }
            DependentProduct::Pair => {
                let t = arg.get_as_type()?;
                Ok(Rc::new(Val::Function(Function::DepProd(
                    DependentProduct::PartialPair(t),
                ))))
            }
            DependentProduct::PartialPair(t1) => {
                let t2 = arg.get_as_type()?;
                Ok(Rc::new(Val::Function(Function::Arrow(ArrFunc::PairOf(
                    t1.clone(),
                    t2,
                )))))
            }
        }
    }
}
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Function {
    Arrow(ArrFunc),
    DepProd(DependentProduct),
}

impl Function {
    fn get_input_type(&self) -> Type {
        match self {
            Self::Arrow(f) => f.get_input_type(),
            Self::DepProd(f) => f.get_input_type(),
        }
    }

    fn apply_to(&self, ctx: &mut Context, arg: Rc<Val>) -> Result<Rc<Val>, RuntimeError> {
        match self {
            Function::Arrow(f) => f.apply_to(ctx, arg),
            Function::DepProd(f) => f.apply_to(ctx, arg),
        }
    }

    fn get_as_arrfunc(self) -> Result<ArrFunc, RuntimeError> {
        match self {
            Function::Arrow(f) => Ok(f),
            Function::DepProd(f) => {
                panic!("Not an arrow function. make this panic into a runtime error")
            }
        }
    }

    fn get_as_dep_prod(self) -> DependentProduct {
        match self {
            Function::Arrow(f) => todo!("Allow casting arrow functions into dependent products"),
            Function::DepProd(f) => f,
        }
    }
}

impl Val {
    fn Arrow(f: ArrFunc) -> Val {
        Val::Function(Function::Arrow(f))
    }

    fn DepProd(f: DependentProduct) -> Val {
        Val::Function(Function::DepProd(f))
    }

    fn get_as_int(&self) -> Result<i64, RuntimeError> {
        match self {
            Val::IntLit(n) => Ok(*n),
            _ => Err(RuntimeError::TypeError {
                expected: Type::Int,
                found: self.clone(),
            }),
        }
    }

    // Unwraps this runtime value as a function, and then applies that function to
    // the supplied argument
    fn get_as_fn(&self) -> Result<&Function, RuntimeError> {
        match self {
            Val::Function(f) => Ok(f),
            _ => Err(RuntimeError::NotAFunction {
                value: self.clone(),
            }),
        }
    }

    fn get_as_arr_func(&self) -> Result<&ArrFunc, RuntimeError> {
        match self {
            Val::Function(Function::Arrow(f)) => Ok(f),
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

    // Given a runtime value, obtains the type of the given value. This is different
    // from get_as_type which asserts that the given value is a type and returns that value
    pub fn get_type(&self, globals: &Vec<Rc<Expr>>) -> Rc<Type> {
        Rc::new(match self {
            Val::Type(_) => Type::Type,
            Val::IntLit(_) => Type::Int,
            Val::Unit => Type::Unit,
            Val::Bool(_) => Type::Bool,
            Val::Pair(left, right) => Type::Pair(left.get_type(globals), right.get_type(globals)),
            Val::Function(Function::Arrow(func)) => Type::FunctionType(
                Rc::new(func.get_input_type()),
                Rc::new(func.get_output_type(globals)),
            ),
            Val::Function(Function::DepProd(func)) => Type::DepProd {
                input_type: Rc::new(func.get_input_type()),
                function: Rc::new(func.get_output_type_fn()),
            },
            Val::Enum(enum_name, _) => Type::Enum(enum_name.clone()),
        })
    }
}

struct Context {
    // internals: Vec<InternalValue>,
    // TODO: turn globals into an Rc<[]>
    globals: Vec<Rc<Expr>>,
    locals: Vec<Rc<Val>>,
}

impl Context {
    pub fn new(globals: Vec<Rc<Expr>>) -> Self {
        Self {
            // internals: make_internal_values(),
            globals,
            locals: Vec::new(),
        }
    }

    pub fn get_local(&self, local_idx: &usize) -> &Rc<Val> {
        &self.locals[self.locals.len() - 1 - local_idx]
    }
}

fn interpret_with_locals(ctx: &mut Context, to_eval: &Expr) -> Result<Rc<Val>, RuntimeError> {
    match to_eval {
        Expr::Apply(func, arg) => {
            let f: Rc<Val> = interpret_with_locals(ctx, func)?;
            // println!("APPLYING FUNCTION: {:?}", f);
            let x: Rc<Val> = interpret_with_locals(ctx, arg)?;
            // println!("TO ARG: {:?}", x);
            let res = f.get_as_fn()?.apply_to(ctx, x);
            // println!("END APPLY ({:?})\n", res);
            res
        }
        Expr::Function { input_type, output } => {
            // println!("FUNCTION");
            let input_type = interpret_with_locals(ctx, input_type)?;
            let res = Ok(Rc::new(Val::Arrow(ArrFunc::Closure {
                input_type: input_type.get_as_type()?,
                captured_vars: ctx.locals.clone(),
                code: output.clone(),
            })));
            // println!("END FUNCTION");
            res
        }
        // The check here fails because when we evaluate during type checking it doesnt
        // have values of every single local variable
        Expr::Local(i) => Ok(ctx.get_local(i).clone()),
        &Expr::Global(i) => {
            // keeping current context isn't necessary for this
            interpret(ctx.globals.clone(), ctx.globals[i].as_ref())
        }
        &Expr::IntLit(n) => Ok(Rc::new(Val::IntLit(n))),
        Expr::Value(val) => Ok(val.clone()),
        Expr::Match {
            enum_name,
            local: local_idx,
            branches,
        } => {
            let local = ctx.get_local(local_idx);
            match local.as_ref() {
                Val::Enum(s, i) => {
                    assert_eq!(s, enum_name);
                    interpret_with_locals(ctx, &branches[*i])
                }
                Val::Bool(b) => {
                    assert_eq!(branches.len(), 2);
                    if *b {
                        interpret_with_locals(ctx, &branches[1])
                    } else {
                        interpret_with_locals(ctx, &branches[0])
                    }
                }
                val => Err(RuntimeError::NotAnEnum(val.clone())),
            }
        }
    }
}

pub fn interpret(globals: Vec<Rc<Expr>>, to_eval: &Expr) -> Result<Rc<Val>, RuntimeError> {
    // dbg!(&to_eval);
    let mut ctx: Context = Context::new(globals);
    let res = interpret_with_locals(&mut ctx, to_eval);
    assert!(ctx.locals.len() == 0);
    res
}
