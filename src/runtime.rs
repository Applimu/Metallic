use std::rc::Rc;
use std::str::FromStr;

use crate::type_checking::CheckingContext;
use crate::{Atomic, Expr, Program, Type};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Val {
    IntLit(i64),
    StringLit(String),
    // the unit value, not to be confused with Type::Unit
    Unit,
    Pair(Rc<Val>, Rc<Val>),
    Function(Function),
    Type(Rc<Type>),
    Enum(String, usize),
    IO(IOAction),
    // usize refers to local variable
    FreeVariable(usize),
}

//TODO: create better error messages
#[derive(Debug, Clone, PartialEq, Eq)]
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

fn run_io_action(ctx: &mut Context, action: &IOAction) -> Result<(), RuntimeError> {
    match action {
        IOAction::PrintLn(s) => {
            println!("{}", s);
            Ok(())
        }
        IOAction::GetLn(f) => {
            let mut s = String::new();
            std::io::stdin().read_line(&mut s).unwrap();
            let mut next_action = f.apply_to(ctx, Rc::new(Val::StringLit(s)))?.get_as_io()?.clone();
            run_io_action(ctx, &mut next_action)
        }
        IOAction::Seq(a, b) => {
            run_io_action(ctx, a)?;
            run_io_action(ctx, b)
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
                    globals_names: ctx.globals_names,
                    // I *believe* that there are never free variables when closures are captured??
                    free_locals: Vec::new(),
                    bound_locals: new_locals,
                };
                new_ctx.interpret(code)
            }
            Function::PartialApplication(function_constant, args) => {
                function_constant.reduce(args.clone(), arg.as_ref()).map(Rc::new)
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
    IntLt,
    IntGt,
    IntLe,

    Fun,
    PairType,

    GetLn,
    PrintLn,
    Seq,

    TypeOfDepProd,      // fn Type: T do (T -> Type) -> Type
    OutputTypeOfMkPair, // fn Type: t1 do (Type: t2) -> t1 & t2

    DepProd,
    Pair,
}

impl FunctionConstant {
    /// Returns the number of arguments that the function takes before
    /// it is reducible to a different `Val`
    const fn args(&self) -> usize {
        match self {
            FunctionConstant::Add => 2,
            FunctionConstant::Mul => 2,
            FunctionConstant::Sub => 2,
            FunctionConstant::IntEq => 2,
            FunctionConstant::IntLt => 2,
            FunctionConstant::IntGt => 2,
            FunctionConstant::IntLe => 2,
            FunctionConstant::Fun => 2,
            FunctionConstant::PairType => 2,
            FunctionConstant::GetLn => 1,
            FunctionConstant::PrintLn => 1,
            FunctionConstant::Seq => 2,
            FunctionConstant::TypeOfDepProd => 1,
            FunctionConstant::OutputTypeOfMkPair => 1,
            FunctionConstant::DepProd => 2,
            FunctionConstant::Pair => 4,
        }
    }
    fn reduce(self, args: Vec<Val>, arg: &Val) -> Result<Val, RuntimeError> {
        // args is a new vector which is [args.., arg]
        let args : Vec<&Val> = Vec::from_iter(args.iter().chain(Some(arg)));
        if args.len() >= self.args() {
            assert!(args.len() == self.args());
            
            Ok(match self {
                FunctionConstant::Add => {
                                            let x = args[0].get_as_int()?;
                                            let y = args[1].get_as_int()?;
                                            Val::IntLit(x + y)
                                    }
                FunctionConstant::Mul => {
                                            let x = args[0].get_as_int()?;
                                            let y = args[1].get_as_int()?;
                                            Val::IntLit(x * y)
                                    }
                FunctionConstant::Sub => {
                                            let x = args[0].get_as_int()?;
                                            let y = args[1].get_as_int()?;
                                            Val::IntLit(x - y)
                                    }
                FunctionConstant::Fun => {
                                            let x = args[0].get_as_type()?;
                                            let y = args[1].get_as_type()?;
                                            Val::Type(Rc::new(Type::FunctionType(x, y)))
                                    }
                FunctionConstant::PairType => {
                                            let x = args[0].get_as_type()?;
                                            let y = args[1].get_as_type()?;
                                            Val::Type(Rc::new(Type::Pair(x, y)))
                                    }
                FunctionConstant::IntEq => {
                                            let x = args[0].get_as_int()?;
                                            let y = args[1].get_as_int()?;
                                            Val::Enum("Bool".to_owned(), if x == y { 1 } else { 0 })
                                    }
                FunctionConstant::IntLt => {
                                            let x = args[0].get_as_int()?;
                                            let y = args[1].get_as_int()?;
                                            Val::Enum("Bool".to_owned(), if x < y { 1 } else { 0 })
                                    }
                FunctionConstant::IntGt => {
                                            let x = args[0].get_as_int()?;
                                            let y = args[1].get_as_int()?;
                                            Val::Enum("Bool".to_owned(), if x > y { 1 } else { 0 })
                                    }
                FunctionConstant::IntLe => {
                                            let x = args[0].get_as_int()?;
                                            let y = args[1].get_as_int()?;
                                            Val::Enum("Bool".to_owned(), if x <= y { 1 } else { 0 })
                }
                FunctionConstant::GetLn => {
                                            let x = args[0].get_as_fn()?;
                                            Val::IO(IOAction::GetLn(x.clone()))
                                    }
                FunctionConstant::PrintLn => {
                                            let x = args[0].get_as_string()?;
                                            Val::IO(IOAction::PrintLn(x.clone()))
                                    }
                FunctionConstant::TypeOfDepProd => {
                                            let x = args[0].get_as_type()?;
                                            let t = Rc::new(Type::Type);
                                            Val::Type(Rc::new(Type::FunctionType(
                                                Rc::new(Type::FunctionType(x, t.clone())),
                                                t,
                                            )))
                                    }
                FunctionConstant::OutputTypeOfMkPair => {
                                            let t = args[0].get_as_type()?;
                                            todo!();
                                    }
                FunctionConstant::DepProd => {
                                            let t = args[0].get_as_type()?;
                                            let f = args[1].get_as_fn()?;
                                            Val::Type(Rc::new(Type::DepProd {
                                                family: Rc::new(f.clone()),
                                            }))
                                    }
                FunctionConstant::Pair => {
                                            let _left_type = args[0].get_as_type()?;
                                            let _right_type = args[1].get_as_type()?;
                                            let left = Rc::new(args[2].clone());
                                            let right = Rc::new(args[3].clone());
                                            Val::Pair(left, right)
                                    }
                FunctionConstant::Seq => {
                    let first = args[0].get_as_io()?;
                    let second = args[1].get_as_io()?;
                    Val::IO(IOAction::Seq(Rc::new(first.clone()), Rc::new(second.clone())))
                },
            })
        } else {
            Ok(Val::Function(Function::PartialApplication(self, args.into_iter().map(Clone::clone).collect())))
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

    pub fn get_as_string(&self) -> Result<&String, RuntimeError> {
        match self {
            Val::StringLit(s) => Ok(s),
            _ => Err(RuntimeError::TypeError {
                expected: Type::String,
                found: self.clone(),
            }),
        }
    }

    pub fn get_as_io(&self) -> Result<&IOAction, RuntimeError> {
        match self {
            Val::IO(io) => Ok(io),
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
            Val::Pair(x, y) => Ok((x.clone(), y.clone())),
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
            Val::Pair(val1, val2) => Type::Pair(val1.get_type(ctx).clone(), val2.get_type(ctx).clone()),
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

/// A context where evaluation of an expression can take place.
#[derive(Debug, Clone)]
pub struct Context<'a> {
    globals: &'a [Rc<Expr>],
    globals_types: &'a [Rc<Expr>],
    globals_names: &'a [String],
    // Only local variables can ever be free variables, so debrujin
    // indices work fine here
    free_locals: Vec<Rc<Type>>,
    bound_locals: Vec<Rc<Val>>,
}

impl<'a> Context<'a> {
    pub const fn new(
        globals: &'a [Rc<Expr>],
        globals_types: &'a [Rc<Expr>],
        globals_names: &'a [String],
    ) -> Self {
        Self {
            globals,
            globals_types,
            globals_names,
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
            globals_names: &[],
            free_locals: locals.clone(),
            bound_locals: Vec::new(),
        }
    }

    /// Gets a local variable's value given it's index
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
                let mut context =
                    Context::new(self.globals, self.globals_types, self.globals_names);
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

    fn display_atom(&self, atom: &Atomic) -> String {
        match atom {
            Atomic::Local(i) => format!("(Local #{})", i),
            Atomic::Global(i) => {
                if self.globals_names.len() != 0 {
                    self.globals_names[*i].clone()
                } else {
                    format!("(Global #{})", i)
                }
            }
            Atomic::Internal(internal) => format!("{:?}", internal),
            Atomic::EnumVariant(enum_type, i) => format!("Variant #{} of {}", i, enum_type),
            Atomic::EnumType(s) => s.clone(),
            Atomic::IntLit(n) => format!("{}", n),
            Atomic::StringLit(s) => format!("\"{}\"", s),
        }
    }

    fn display_expr(&self, expr: &Expr) -> String {
        match expr {
            Expr::Apply(expr, expr1) => {
                format!("({} {})", self.display_expr(expr), self.display_expr(expr1))
            }
            Expr::Function { input_type, output } => format!(
                "fn {} do {}",
                self.display_expr(input_type),
                self.display_expr(output)
            ),
            Expr::Atom(atomic) => self.display_atom(atomic),
            Expr::Match {
                enum_name,
                matchend,
                branches,
            } => {
                format!(
                    "match {} : {} {{...}}",
                    enum_name,
                    self.display_expr(matchend)
                )
            }
            Expr::Let {
                new_value_type,
                new_value,
                expr,
            } => format!(
                "let {} := {} in {}",
                self.display_expr(new_value_type),
                self.display_expr(new_value),
                self.display_expr(expr),
            ),
        }
    }

    fn display_val(&self, val: &Val) -> String {
        match val {
            Val::IntLit(n) => format!("{}", n),
            Val::StringLit(s) => format!("\"{}\"", s),
            Val::Unit => String::from_str("()").unwrap(),
            Val::Pair(val1, val2) => {
                format!("({}, {})", self.display_val(val1), self.display_val(val2))
            }
            Val::Function(Function::PartialApplication(f_const, vals)) => {
                let mut str = format!("{:?}", f_const);
                for val in vals.iter() {
                    str += " ";
                    str += &self.display_val(val)
                }
                str
            }
            Val::Function(Function::Closure {
                captured_vars: _,
                code: _,
            }) => {
                format!("[Closure]")
            }
            Val::Type(t) => {
                format!("{:?}", t)
            }
            Val::Enum(enum_type, i) => format!("{}::{}", enum_type, i),
            Val::IO(_ioaction) => format!("[IO Action]"),
            Val::FreeVariable(i) => format!("(Free var #{})", i),
        }
    }

    pub fn interpret(&mut self, to_eval: &Expr) -> Result<Rc<Val>, RuntimeError> {
        // println!(
        //     "\tinterpret {}:: {}",
        //     self.bound_locals
        //         .iter()
        //         .map(|v| self.display_val(v) + ", ")
        //         .collect::<String>(),
        //     self.display_expr(to_eval)
        // );
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
    globals_names: &[String],
    expr: &Expr,
) -> Result<Rc<Val>, RuntimeError> {
    let mut ctx = Context::new(globals, globals_types, globals_names);
    println!("\n\nNOW EVALUATING: {}", ctx.display_expr(expr));
    let res = ctx.interpret(expr);
    assert!(ctx.free_locals.len() == 0);
    assert!(ctx.bound_locals.len() == 0);
    res
}

pub fn interpret_program(prog: &Program) -> Vec<Result<Rc<Val>, RuntimeError>> {
    let mut results = Vec::new();
    for to_eval in prog.evals.iter() {
        results.push(interpret(
            &prog.globals,
            &prog.global_types,
            &prog.names,
            to_eval,
        ));
    }
    return results;
}
