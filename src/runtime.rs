use crate::{Expr, INTERNAL_VALUES, Type};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Val {
    IntLit(i64),
    Bool(bool),
    Unit,
    // Should Pair keep the types of the values?
    Pair(Box<Val>, Box<Val>),
    Function(Function),
    Type(Type),
}

// TODO: create better error messages
#[derive(Debug, Clone)]
pub enum RuntimeError {
    TypeError { expected: Type, found: Val },
    TypesMismatch { expected: Type, found: Type },
    NotAFunction { value: Val },
    NotFunctionType { func: Expr, args: Expr },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ArrFunc {
    Closure {
        input_type: Type,
        captured_vars: Vec<Val>,
        code: Expr,
    },
    Add,
    PartialAdd(i64),
    Fun,
    PartialFun(Type),
    DepProdOf(Type),
    PairOf(Type, Type),            // this has type: t1 -> t2 -> t1 & t2
    PartialPairOf(Box<Val>, Type), // has type: t2 -> t1 & t2
    TypeOfMakePair,                // this is the value: (Type: t1) -> (Type: t2) -> t1 & t2
    TypeOfPartialMakePair(Type),   // (Type: t2) -> t1 & t2
}

impl ArrFunc {
    // NOTE: PERFORMS NO TYPE CHECKING.
    fn apply_to(
        self,
        globals: &Vec<Expr>,
        locals: &mut Vec<Val>,
        arg: Val,
    ) -> Result<Val, RuntimeError> {
        match self {
            ArrFunc::Closure {
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
                // after all captured locals are added, we remove them all
                // as they aren't necessary anymore
                for _ in 0..num_new_locals {
                    locals.pop().expect("Number of locals changed????");
                }

                // dbg!(&result);
                result
            }
            ArrFunc::Add => match arg.clone().get_as_int() {
                Some(n) => Ok(Val::Function(Function::Arrow(ArrFunc::PartialAdd(n)))),
                None => Err(RuntimeError::TypeError {
                    expected: Type::Int,
                    found: arg.clone(),
                }),
            },
            ArrFunc::PartialAdd(n) => match arg.clone().get_as_int() {
                Some(m) => Ok(Val::IntLit(n + m)),
                None => Err(RuntimeError::TypeError {
                    expected: Type::Int,
                    found: arg.clone(),
                }),
            },
            ArrFunc::Fun => arg
                .get_as_type()
                .map(|t| Val::Function(Function::Arrow(ArrFunc::PartialFun(t)))),
            ArrFunc::PartialFun(t1) => match arg.clone().get_as_type() {
                Ok(t2) => Ok(Val::Type({
                    Type::FunctionType(Box::new(t1), Box::new(t2))
                })),
                Err(e) => Err(e),
            },
            ArrFunc::DepProdOf(t) => Ok(Val::Type(Type::DepProd {
                input_type: Box::new(t),
                function: Box::new(arg.get_as_fn()?.get_as_arrfunc()?),
            })),
            ArrFunc::PairOf(t1, t2) => Ok(Val::Function(Function::Arrow(ArrFunc::PartialPairOf(
                Box::new(arg),
                t2,
            )))),
            ArrFunc::PartialPairOf(left, t2) => Ok(Val::Pair(left, Box::new(arg))),
            ArrFunc::TypeOfMakePair => {
                let t1 = arg.get_as_type()?;
                Ok(Val::Function(Function::Arrow(
                    ArrFunc::TypeOfPartialMakePair(t1),
                )))
            }
            ArrFunc::TypeOfPartialMakePair(t1) => {
                let t2 = arg.get_as_type()?;
                Ok(Val::Type(Type::FunctionType(
                    Box::new(t1.clone()),
                    Box::new(Type::FunctionType(
                        Box::new(t2.clone()),
                        Box::new(Type::Pair(Box::new(t1), Box::new(t2))),
                    )),
                )))
            }
        }
    }

    fn get_input_type(&self) -> Type {
        match self {
            ArrFunc::Closure {
                input_type,
                captured_vars: _,
                code: _,
            } => input_type.clone(),
            ArrFunc::Add => Type::Int,
            ArrFunc::PartialAdd(_) => Type::Int,
            ArrFunc::Fun => Type::Type,
            ArrFunc::PartialFun(_) => Type::Type,
            ArrFunc::DepProdOf(t) => Type::FunctionType(Box::new(t.clone()), Box::new(Type::Type)),
            ArrFunc::PairOf(t1, _) => t1.clone(),
            ArrFunc::PartialPairOf(_, t2) => t2.clone(),
            ArrFunc::TypeOfMakePair => Type::Type,
            ArrFunc::TypeOfPartialMakePair(_) => Type::Type,
        }
    }

    fn get_output_type(self, globals: &Vec<Expr>) -> Type {
        match self {
            ArrFunc::Closure {
                input_type,
                captured_vars,
                code,
            } => {
                let mut locals_types = captured_vars
                    .iter()
                    .map(|r| r.clone().get_type(globals))
                    .collect();

                code.get_type_checked_with_locals(globals, &mut locals_types)
                    .expect("Bad expression caused function to have ill-formed type")
            }
            ArrFunc::Add => Type::Int,
            ArrFunc::PartialAdd(_) => Type::Int,
            ArrFunc::Fun => Type::Type,
            ArrFunc::PartialFun(_) => Type::Type,
            ArrFunc::DepProdOf(t) => Type::FunctionType(
                Box::new(Type::FunctionType(Box::new(t), Box::new(Type::Type))),
                Box::new(Type::Type),
            ),
            ArrFunc::PairOf(t1, t2) => Type::FunctionType(
                Box::new(t1.clone()),
                Box::new(Type::FunctionType(
                    Box::new(t2.clone()),
                    Box::new(Type::Pair(Box::new(t1), Box::new(t2))),
                )),
            ),
            ArrFunc::PartialPairOf(left, t2) => Type::FunctionType(
                Box::new(t2.clone()),
                Box::new(Type::Pair(Box::new(left.get_type(globals)), Box::new(t2))),
            ),
            ArrFunc::TypeOfMakePair => Type::Type,
            ArrFunc::TypeOfPartialMakePair(_) => Type::Type,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DependentProduct {
    DepProd,
    Closure {
        // this function is always expected to return a Type
        type_family: ArrFunc,
        captured_vars: Vec<Val>,
        code: Expr,
    },
    Pair,
    PartialPair(Type),
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
                input_type: Type::Type,
                captured_vars: vec![],
                code: Expr::Apply(
                    Box::new(Expr::Apply(
                        Box::new(Expr::Value(Box::new(Val::Function(Function::Arrow(
                            ArrFunc::Fun,
                        ))))),
                        Box::new(Expr::Apply(
                            Box::new(Expr::Apply(
                                Box::new(Expr::Value(Box::new(Val::Function(Function::Arrow(
                                    ArrFunc::Fun,
                                ))))),
                                Box::new(Expr::Local(0)), // the input type
                            )),
                            Box::new(Expr::Value(Box::new(Val::Type(Type::Type)))),
                        )),
                    )),
                    Box::new(Expr::Value(Box::new(Val::Type(Type::Type)))),
                ),
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

    fn apply_to(
        self,
        globals: &Vec<Expr>,
        locals: &mut Vec<Val>,
        arg: Val,
    ) -> Result<Val, RuntimeError> {
        match self {
            DependentProduct::DepProd => {
                let input_type = arg.get_as_type()?;
                Ok(Val::Function(Function::Arrow(ArrFunc::DepProdOf(
                    input_type,
                ))))
            }
            DependentProduct::Closure {
                type_family,
                mut captured_vars,
                code,
            } => {
                let num_new_locals = captured_vars.len() + 1;
                locals.append(&mut captured_vars);
                locals.push(arg);
                let res = interpret_with_locals(globals, locals, code.clone());

                for _ in 0..num_new_locals {
                    locals.pop().expect("Number of locals somehow changed :/");
                }
                res
            }
            DependentProduct::Pair => {
                let t = arg.get_as_type()?;
                Ok(Val::Function(Function::DepProd(
                    DependentProduct::PartialPair(t),
                )))
            }
            DependentProduct::PartialPair(t1) => {
                let t2 = arg.get_as_type()?;
                Ok(Val::Function(Function::Arrow(ArrFunc::PairOf(t1, t2))))
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

    fn apply_to(
        self,
        globals: &Vec<Expr>,
        locals: &mut Vec<Val>,
        arg: Val,
    ) -> Result<Val, RuntimeError> {
        match self {
            Function::Arrow(f) => f.apply_to(globals, locals, arg),
            Function::DepProd(f) => f.apply_to(globals, locals, arg),
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
    fn get_as_int(self) -> Option<i64> {
        match self {
            Val::IntLit(n) => Some(n),
            _ => None,
        }
    }

    // Unwraps this runtime value as a function, and then applies that function to
    // the supplied argument
    fn get_as_fn(self) -> Result<Function, RuntimeError> {
        match self {
            Val::Function(f) => Ok(f),
            _ => Err(RuntimeError::NotAFunction { value: self }),
        }
    }

    pub fn get_as_type(self) -> Result<Type, RuntimeError> {
        match self {
            Val::Type(t) => Ok(t),
            c => Err(RuntimeError::TypeError {
                expected: Type::Type,
                found: c,
            }),
        }
    }

    // Given a runtime value, obtains the type of the given value. This is different
    // from get_as_type which asserts that the given value is a type and returns that value
    pub fn get_type(self, globals: &Vec<Expr>) -> Type {
        match self {
            Val::Type(_) => Type::Type,
            Val::IntLit(_) => Type::Int,
            Val::Unit => Type::Unit,
            Val::Bool(_) => Type::Bool,
            Val::Pair(left, right) => Type::Pair(
                Box::new(left.get_type(globals)),
                Box::new(right.get_type(globals)),
            ),
            Val::Function(Function::Arrow(func)) => Type::FunctionType(
                Box::new(func.get_input_type()),
                Box::new(func.get_output_type(globals)),
            ),
            Val::Function(Function::DepProd(func)) => Type::DepProd {
                input_type: Box::new(func.get_input_type()),
                function: Box::new(func.get_output_type_fn()),
            },
        }
    }
}

fn interpret_with_locals(
    globals: &Vec<Expr>,
    locals: &mut Vec<Val>,
    to_eval: Expr,
) -> Result<Val, RuntimeError> {
    //dbg!(&locals);
    // dbg!(&to_eval);
    match to_eval {
        Expr::Apply(func, arg) => {
            let f: Function = interpret_with_locals(globals, locals, *func)?.get_as_fn()?;
            println!("APPLYING FUNCTION: {:?}", f);
            let x: Val = interpret_with_locals(globals, locals, *arg)?;
            println!("TO ARG: {:?}", x);
            let res = f.apply_to(globals, locals, x);
            println!("END APPLY ({:?})\n", res);
            res
        }
        Expr::Function { input_type, output } => {
            // println!("FUNCTION");
            let input_type = interpret_with_locals(globals, locals, *input_type)?;
            let res = Ok(Val::Function(Function::Arrow(ArrFunc::Closure {
                input_type: input_type.get_as_type()?,
                captured_vars: locals.clone(),
                code: *output,
            })));
            // println!("END FUNCTION");
            res
        }
        // The check here fails because when we evaluate during type checking it doesnt
        // have values of every single local variable
        Expr::Local(i) => Ok(locals[locals.len() - 1 - i].clone()),
        Expr::Global(i) => interpret_with_locals(globals, locals, globals[i].clone()),
        Expr::IntLit(n) => Ok(Val::IntLit(n)),
        Expr::Unit => Ok(Val::Unit),
        Expr::Value(val) => Ok(*val),
    }
}

pub fn interpret(globals: &Vec<Expr>, to_eval: Expr) -> Result<Val, RuntimeError> {
    dbg!(&to_eval);
    let mut locals = Vec::new();
    let res = interpret_with_locals(globals, &mut locals, to_eval);
    assert!(locals.len() == 0);
    res
}
