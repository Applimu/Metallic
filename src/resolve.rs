use std::{
    collections::{HashMap, HashSet},
    rc::Rc,
};

use crate::{
    Atomic, Expr, Internal,
    parsing::{Binding, Matching},
};

//TODO: create a better error message
#[derive(Debug)]
pub enum ResolveError {
    UnknownName(String),
    NotALocalVariable(String),
    UnknownSetOfVariants(HashSet<String>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UnresolvedExpr {
    Apply(Box<UnresolvedExpr>, Box<UnresolvedExpr>),
    Function {
        name: String,
        input_type: Box<UnresolvedExpr>,
        output: Box<UnresolvedExpr>,
    },
    Variable(String),
    IntLit(i64),
    StringLit(String),
    Unit,
    Match(Matching),
    Let(Box<Binding>, Box<UnresolvedExpr>),
}

// Resolves all names inside an expression and converts them into an indices of the provided array
// TODO: Allow for a better variable shadowing system.
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
        UnresolvedExpr::Variable(name) => {
            resolve_name(global_names, local_names, case_groups, name).map(Expr::Atom)
        }
        UnresolvedExpr::StringLit(s) => Ok(Expr::Atom(Atomic::StringLit(s))),
        UnresolvedExpr::IntLit(n) => Ok(Expr::Atom(Atomic::IntLit(n))),
        UnresolvedExpr::Unit => Ok(Expr::Atom(Atomic::Value(Internal::Iunit))),
        UnresolvedExpr::Match(Matching { matchend, branches }) => {
            let resolved_matchend =
                resolve_expr(global_names, local_names, case_groups, *matchend)?;

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
                // The branches have the same exact case names as this enum's variants,
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

                return Ok(Expr::Match {
                    enum_name: enum_name.clone(),
                    matchend: Rc::new(resolved_matchend),
                    branches: resolved_branches,
                });
            }
            let case_names = HashSet::from_iter(branches.into_keys());

            Err(ResolveError::UnknownSetOfVariants(case_names))
        }
        UnresolvedExpr::Let(binding, expr) => {
            let Binding {
                var_name,
                type_sig,
                value,
            } = *binding;
            let new_value_type = resolve_expr(global_names, local_names, case_groups, type_sig)?;
            let new_value = resolve_expr(global_names, local_names, case_groups, value)?;
            local_names.push(var_name.clone());
            let expr = resolve_expr(global_names, local_names, case_groups, *expr)?;
            assert_eq!(local_names.pop().unwrap(), var_name);

            Ok(Expr::Let {
                new_value_type: Rc::new(new_value_type),
                new_value: Rc::new(new_value),
                expr: Rc::new(expr),
            })
        }
    }
}

fn resolve_name(
    global_names: &Vec<String>,
    local_names: &mut Vec<String>,
    case_groups: &HashMap<String, Vec<String>>,
    s: String,
) -> Result<Atomic, ResolveError> {
    // local variables shadow globals shadow internal
    if let Some(value) = get_from_locals(local_names, &s) {
        return Ok(Atomic::Local(value));
    }
    for (i, name) in global_names.iter().enumerate() {
        if *name == s {
            return Ok(Atomic::Global(i));
        }
    }

    for (k, v) in case_groups.iter() {
        // println!("{:?}: {:?}", k, v);
        if *k == s {
            return Ok(Atomic::EnumType(k.clone()));
        }
        for (i, variant) in v.iter().enumerate() {
            if *variant == s {
                return Ok(Atomic::EnumVariant(k.clone(), i));
            }
        }
    }

    match Internal::try_as_internal(&s) {
        Some(v) => Ok(Atomic::Value(v)),
        None => Err(ResolveError::UnknownName(s)),
    }
}

// Find the name in a list of local names and return the index of the variable
// if it exists. Local variables are currently ordered in the order that they are
// added to scope, which is the reverse of de brujin indices.
fn get_from_locals(locals: &mut Vec<String>, s: &String) -> Option<usize> {
    for (i, name) in locals.iter().enumerate() {
        // here `i` gives the debrujin indices
        if **name == *s {
            return Some(i);
        }
    }
    None
}

// resolves references to local, global, and internally defined names. Multiple variables with
// the same name give undefined behavior currently.
// TODO: Think about adding name overloading.
pub fn resolve_exprs(
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
