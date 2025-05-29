use std::rc::Rc;

use crate::{Expr, Type};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Val {
    IntLit(i64),
    Unit,
    // Pair (t1, t2, x,y) has t1: x, t2: y
    Pair(Rc<Type>, Rc<Type>, Rc<Val>, Rc<Val>),
    Function(Function),
    Type(Rc<Type>),
    Enum(String, usize),
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
pub enum ArrFunc {
    Add,
    PartialAdd(i64),
    AddUncurried,
    Fun,
    PartialFun(Rc<Type>),
    DepProdOf(Rc<Type>),
    PairOf(Rc<Type>, Rc<Type>), // this is of type: t1 -> t2 -> t1 & t2
    PartialPairOf(Rc<Type>, Rc<Type>, Rc<Val>), // of type: t2 -> t1 & t2
    OutputTypeOfMkPair,         // this is the value: fn Type: t1 do (Type: t2) -> t1 & t2
    TypeOfPartialMakePair(Rc<Type>), // fn Type: t2 do  t1 & t2
    PairType,
    PartialPairType(Rc<Type>),
    IntEq,
    PartialIntEq(i64),
}

impl ArrFunc {
    fn apply_to(&self, arg: Rc<Val>) -> Result<Rc<Val>, RuntimeError> {
        match self {
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
            ArrFunc::AddUncurried => {
                let (n, m) = arg.get_as_pair()?;
                let n2 = n.get_as_int()?;
                let m2 = m.get_as_int()?;
                Ok(Rc::new(Val::IntLit(n2 + m2)))
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
            // NOTE: THIS DOES NOT CHECK THAT arg IS OF TYPE t1
            ArrFunc::PairOf(t1, t2) => Ok(Rc::new(Val::Function(Function::Arrow(
                ArrFunc::PartialPairOf(t1.clone(), t2.clone(), arg),
            )))),
            ArrFunc::PartialPairOf(t1, t2, left) => Ok(Rc::new(Val::Pair(
                t1.clone(),
                t2.clone(),
                left.clone(),
                arg,
            ))),
            ArrFunc::OutputTypeOfMkPair => Ok(Rc::new(Val::Function(Function::Arrow(
                ArrFunc::TypeOfPartialMakePair(arg.get_as_type()?),
            )))),
            ArrFunc::TypeOfPartialMakePair(t1) => {
                let t2 = arg.get_as_type()?;
                Ok(Rc::new(Val::Type(Rc::new(Type::FunctionType(
                    t1.clone(),
                    Rc::new(Type::FunctionType(
                        t2.clone(),
                        Rc::new(Type::Pair(t1.clone(), t2.clone())),
                    )),
                )))))
            }
            ArrFunc::PairType => {
                let t1 = arg.get_as_type()?;
                Ok(Rc::new(Val::Function(Function::Arrow(
                    ArrFunc::PartialPairType(t1),
                ))))
            }
            ArrFunc::PartialPairType(t1) => {
                let t2 = arg.get_as_type()?;
                Ok(Rc::new(Val::Type(Rc::new(Type::Pair(t1.clone(), t2)))))
            }
            ArrFunc::IntEq => {
                let x = arg.get_as_int()?;
                Ok(Rc::new(Val::Function(Function::Arrow(
                    ArrFunc::PartialIntEq(x),
                ))))
            }
            ArrFunc::PartialIntEq(x) => {
                let y = arg.get_as_int()?;
                Ok(Rc::new(Val::Enum(
                    "Bool".to_owned(),
                    if *x == y { 1 } else { 0 },
                )))
            }
        }
    }

    fn get_input_type(&self) -> Type {
        match self {
            ArrFunc::Add => Type::Int,
            ArrFunc::PartialAdd(_) => Type::Int,
            ArrFunc::AddUncurried => Type::Pair(Rc::new(Type::Int), Rc::new(Type::Int)),
            ArrFunc::Fun => Type::Type,
            ArrFunc::PartialFun(_) => Type::Type,
            ArrFunc::DepProdOf(t) => Type::FunctionType(t.clone(), Rc::new(Type::Type)),
            // these are bad solutions tbh
            ArrFunc::PairOf(t1, _) => t1.as_ref().clone(),
            ArrFunc::PartialPairOf(_, t2, _) => t2.as_ref().clone(),
            ArrFunc::OutputTypeOfMkPair => Type::Type,
            ArrFunc::TypeOfPartialMakePair(_) => Type::Type,
            ArrFunc::PairType => Type::Type,
            ArrFunc::PartialPairType(_) => Type::Type,
            ArrFunc::IntEq => Type::Int,
            ArrFunc::PartialIntEq(_) => Type::Int,
        }
    }

    fn get_output_type(&self) -> Type {
        match self {
            ArrFunc::Add => Type::FunctionType(Rc::new(Type::Int), Rc::new(Type::Int)),
            ArrFunc::PartialAdd(_) => Type::Int,
            ArrFunc::AddUncurried => Type::Int,
            ArrFunc::Fun => Type::FunctionType(Rc::new(Type::Type), Rc::new(Type::Type)),
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
            ArrFunc::PartialPairOf(t1, t2, _) => {
                Type::FunctionType(t2.clone(), Rc::new(Type::Pair(t1.clone(), t2.clone())))
            }
            ArrFunc::OutputTypeOfMkPair => Type::Type,
            ArrFunc::TypeOfPartialMakePair(_) => Type::Type,
            ArrFunc::PairType => Type::FunctionType(Rc::new(Type::Type), Rc::new(Type::Type)),
            ArrFunc::PartialPairType(_) => Type::Type,
            ArrFunc::IntEq => {
                Type::FunctionType(Rc::new(Type::Int), Rc::new(Type::Enum("Bool".to_owned())))
            }
            ArrFunc::PartialIntEq(_) => Type::Enum("Bool".to_owned()),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DependentProduct {
    DepProd,
    Pair,
    PartialPair(Rc<Type>),
}

impl DependentProduct {
    fn get_input_type(&self) -> Type {
        match self {
            DependentProduct::DepProd => Type::Type,
            DependentProduct::Pair => Type::Type,
            DependentProduct::PartialPair(_) => Type::Type,
        }
    }

    fn get_output_type_fn(&self) -> ArrFunc {
        match self {
            // DepProd: (Type: T) => fun (fun T Type) Type
            DependentProduct::DepProd => todo!("Implement type of DepProd internally"),
            /* ArrFunc::Closure {
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
            },*/
            DependentProduct::Pair => ArrFunc::OutputTypeOfMkPair,
            DependentProduct::PartialPair(t1) => ArrFunc::TypeOfPartialMakePair(t1.clone()),
        }
    }

    fn apply_to(&self, arg: Rc<Val>) -> Result<Rc<Val>, RuntimeError> {
        match self {
            DependentProduct::DepProd => {
                let input_type = arg.get_as_type()?;
                Ok(Rc::new(Val::Function(Function::Arrow(ArrFunc::DepProdOf(
                    input_type,
                )))))
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
    Closure {
        captured_vars: Vec<Rc<Val>>,
        code: Rc<Expr>,
    },
}

impl Function {
    fn get_input_type(&self) -> Type {
        match self {
            Function::Arrow(f) => f.get_input_type(),
            Function::DepProd(f) => f.get_input_type(),
            Function::Closure {
                captured_vars,
                code,
            } => todo!("Don't know how to get types of closures"),
        }
    }

    fn apply_to(&self, ctx: &mut Context, arg: Rc<Val>) -> Result<Rc<Val>, RuntimeError> {
        match self {
            Function::Arrow(f) => f.apply_to(arg),
            Function::DepProd(f) => f.apply_to(arg),
            Function::Closure {
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

    fn get_as_pair(&self) -> Result<(Rc<Val>, Rc<Val>), RuntimeError> {
        match self {
            Val::Pair(t1, t2, x, y) => Ok((x.clone(), y.clone())),
            _ => Err(RuntimeError::NotAPair(self.clone())),
        }
    }

    // Given a runtime value, obtains the type of the given value. This is different
    // from get_as_type which asserts that the given value is a type and returns that value
    pub fn get_type(&self) -> Rc<Type> {
        Rc::new(match self {
            Val::Type(_) => Type::Type,
            Val::IntLit(_) => Type::Int,
            Val::Unit => Type::Unit,
            Val::Pair(t1, t2, left, right) => Type::Pair(t1.clone(), t2.clone()),
            Val::Function(Function::Arrow(func)) => Type::FunctionType(
                Rc::new(func.get_input_type()),
                Rc::new(func.get_output_type()),
            ),
            Val::Function(Function::DepProd(func)) => Type::DepProd {
                input_type: Rc::new(func.get_input_type()),
                function: Rc::new(func.get_output_type_fn()),
            },
            Val::Function(_) => todo!("getting types of closures not implemented :/"),
            Val::Enum(enum_name, _) => Type::Enum(enum_name.clone()),
        })
    }
}

struct Context {
    // internals: Vec<InternalValue>,
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
            let res = Ok(Rc::new(Val::Function(Function::Closure {
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
        Expr::Value(val) => Ok(Rc::new(val.val())),
        Expr::EnumVariant(name, internal_num) => {
            Ok(Rc::new(Val::Enum(name.clone(), *internal_num)))
        }
        Expr::EnumType(name) => Ok(Rc::new(Val::Type(Rc::new(Type::Enum(name.clone()))))),
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
                val => Err(RuntimeError::NotAnEnum(val.clone())),
            }
        }
        Expr::Let {
            new_value_type,
            new_value,
            expr,
        } => {
            let new_value = interpret_with_locals(ctx, new_value)?;
            ctx.locals.push(new_value.clone());
            let res = interpret_with_locals(ctx, expr);
            assert_eq!(ctx.locals.pop().unwrap(), new_value);
            res
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
