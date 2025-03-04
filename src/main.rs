#![allow(unused)]
#![allow(clippy::uninlined_format_args)]
mod types;

use core::panic;
use std::mem;
use types::CheckingError;
use types::Context;
use types::ContextElement;
use types::Term;
use types::Type;

impl Context {
    const fn new() -> Self {
        Self {
            elements: vec![],
            existentials: 0,
            markers: vec![],
        }
    }
    fn fresh_existential(&mut self) -> String {
        let result = format!("t{}", self.existentials);
        self.existentials += 1;
        result
    }
    fn is_well_formed(&self, ty: &Type) -> bool {
        match ty {
            Type::Unit | Type::BaseType(_) => true,
            Type::Variable(var) => self.contains(ContextElement::Variable(var.to_string())),
            Type::Existential(alpha_hat) => {
                self.contains(ContextElement::Existential(alpha_hat.to_string()))
                    || self.get_solved(alpha_hat).is_some()
            }
            Type::Quantification(alpha_hat, ty) => self
                .clone()
                .extend(ContextElement::Existential(alpha_hat.to_string()))
                .is_well_formed(ty),
            Type::Function(a, b) => self.is_well_formed(a) && self.is_well_formed(b),
            Type::HigherKinded(vec) => vec.iter().all(|ty| self.is_well_formed(ty)),
        }
    }
    fn contains(&self, c: ContextElement) -> bool {
        self.elements.iter().any(|elem| elem == &c)
    }
    fn any_matches<F: FnMut(&ContextElement) -> bool>(&self, f: F) -> bool {
        self.elements.iter().any(f)
    }
    fn mark_scope(mut self) -> Self {
        self.markers.push(self.elements.len());
        self
    }
    fn drop_scope(mut self) -> Self {
        let x = self
            .markers
            .pop()
            .expect("Called drop_mark without having called mark");
        self.elements.drain(x..);
        self
    }
    /// Γ -> Γ,α
    fn extend(self, alpha: ContextElement) -> Self {
        let mut elements = self.elements;
        elements.push(alpha);
        Self { elements, ..self }
    }
    /// Γ,α -> Γ
    fn drop(self, alpha: ContextElement) -> Self {
        let pos = self
            .elements
            .iter()
            .position(|elem| elem == &alpha)
            .unwrap_or_else(|| panic!("Could not find {} in context to drop", alpha));
        let mut elements = self.elements.clone();
        let rest = elements.split_off(pos);
        Self {
            elements,
            ..self.clone()
        }
    }
    /// Γ, α, Γ' ->  Γ, β, Γ'
    fn insert_at(&self, alpha: &ContextElement, beta: Vec<ContextElement>) -> Self {
        let pos = self
            .elements
            .iter()
            .position(|elem| elem == alpha)
            .unwrap_or_else(|| panic!("Could not find {} in context to replace", alpha));
        let mut elements = self.elements.clone();
        elements.splice(pos..=pos, beta);
        Self {
            elements,
            ..self.clone()
        }
    }
    /// Γ -> Γ [^α = τ]
    fn get_solved(&self, alpha_hat: &str) -> Option<&Type> {
        println!("looking for {alpha_hat} in {self}");
        for elem in &self.elements {
            if let ContextElement::Solved(a, b) = elem {
                if alpha_hat == a {
                    return Some(b);
                }
            }
        }
        None
    }
    /// Γ -> Γ [^α = τ]
    fn get_annotation(&self, alpha_hat: &str) -> Option<&Type> {
        for elem in &self.elements {
            if let ContextElement::TypedVariable(a, b) = elem {
                if alpha_hat == a {
                    return Some(b);
                }
            }
        }
        None
    }

    /// instantiate ^α to a subtype of A
    fn instantiate(mut self, alpha_hat: String, ty: &Type, dir: Direction) -> Context {
        println!("instantiate {alpha_hat} to a subtype of {ty} under Context {self}");
        let mut alpha = ContextElement::Existential(alpha_hat.clone());
        assert!(!occurs_check(&alpha_hat, ty));
        let (begin, rest) = self.elements.split_at(
            self.elements
                .iter()
                .position(|elem| elem == &alpha)
                .unwrap_or_else(|| panic!("Could not find {} in context to split", alpha)),
        );
        let (l, r) = (
            Context {
                elements: begin.to_vec(),
                ..self.clone()
            },
            Context {
                elements: rest.to_vec(),
                ..self.clone()
            },
        );

        if ty.is_monotype() && l.is_well_formed(ty) {
            println!("{:>20}", "InstLSolve");
            return self.insert_at(&alpha, vec![ContextElement::Solved(alpha_hat, ty.clone())]);
        }
        match (ty, dir) {
            (Type::Existential(beta), _) => {
                println!("{:>20}", "InstLReach");
                assert!(r.is_well_formed(ty));
                self.insert_at(&ContextElement::Existential(beta.to_string()), vec![
                    ContextElement::Solved(beta.to_string(), (Type::Existential(alpha_hat))),
                ])
            }
            (Type::Quantification(beta, ty), Direction::Left) => {
                println!("{:>20}", "InstLAllR");
                let beta_hat = self.fresh_existential();
                let mut extended_gamma = self.extend(ContextElement::Existential(beta_hat));
                let delta = extended_gamma
                    .instantiate(alpha_hat, ty, Direction::Left)
                    .drop(ContextElement::Existential(beta.to_string()));
                return delta;
            }
            (Type::Quantification(beta, ty), Direction::Right) => {
                println!("{:>20}", "InstRAllL");
                let beta_hat = self.fresh_existential();
                let extended_gamma = self
                    .mark_scope()
                    .extend(ContextElement::Existential(beta_hat.clone()));
                let delta = extended_gamma
                    .instantiate(
                        alpha_hat,
                        &substitute_existential(&beta_hat, &Type::Variable(beta.to_string()), ty),
                        Direction::Right,
                    )
                    .drop_scope();
                return delta;
            }
            (Type::Function(a, b), dir) => {
                println!("{:>20}", "InstArr");
                let alpha_hat1 = self.fresh_existential();
                let alpha_hat2 = self.fresh_existential();
                let extended_gamma = self.insert_at(&alpha, vec![
                    ContextElement::Existential(alpha_hat1.clone()),
                    ContextElement::Existential(alpha_hat2.clone()),
                    ContextElement::Solved(
                        alpha_hat,
                        Type::Function(
                            Box::new(Type::Existential(alpha_hat1.clone())),
                            Box::new(Type::Existential(alpha_hat2.clone())),
                        ),
                    ),
                ]);
                let mut theta = extended_gamma.instantiate(alpha_hat1, a, dir.flip());
                let b = apply_context(&theta, *b.clone());
                let delta = theta.instantiate(alpha_hat2, &b, dir);
                return delta;
            }
            (t, dir) => panic!(
                "Failed to handle {t} in direction {dir:?}, either is_well_formed has a problem or i need to handle more cases"
            ),
        }
    }
    /// Γ == ∆, ^α
    fn has_existential(&self, alpha_hat: &str) -> bool {
        self.elements
            .iter()
            .any(|elem| elem == &ContextElement::Existential(alpha_hat.to_string()))
    }
}

#[derive(Debug)]
enum Direction {
    Left,
    Right,
}
impl Direction {
    fn flip(&self) -> Self {
        match self {
            Direction::Left => Direction::Right,
            Direction::Right => Direction::Left,
        }
    }
}

fn check(e: Term, ty: Type, ctx: Context) -> Result<Context, (CheckingError, Context)> {
    println!("checking that {e} has type {ty} under context {ctx}");
    match (e, ty) {
        (Term::Unit, Type::Unit) => {
            println!("{:>20}", "1I");
            Ok(ctx)
        }
        (e, Type::Quantification(name, ty)) => {
            println!("{:>20}", "∀I");
            let mut extendet_gamma = ctx
                .mark_scope()
                .extend(ContextElement::Variable(name.clone()));
            let delta = check(e, *ty, extendet_gamma)?.drop_scope();
            return Ok(delta);
        }
        (Term::Abstraction(alpha, term), Type::Function(a, b)) => {
            println!("{:>20}", "->I");
            let typed = ContextElement::TypedVariable(alpha, *a);
            let extended_gamma = ctx.mark_scope().extend(typed.clone());
            let delta = check(*term, *b, extended_gamma)?.drop_scope();
            return Ok(delta);
        }
        (Term::Let(name, expr, tail), ty) => {
            if ctx.any_matches(
                |elem| matches!(elem, ContextElement::TypedVariable(name1, _) if *name1 == name),
            ) {
                panic!("Initialized variable twice");
            }
            let (a, theta) = synth(*expr, ctx)?;
            let delta = check(
                *tail,
                ty,
                theta.extend(ContextElement::TypedVariable(name, a)),
            );
            return delta;
        }
        (e, ty) => {
            println!("{:>20}", "Sub");
            let (a, theta) = synth(e, ctx)?;
            Ok(subtype(
                &apply_context(&theta, a),
                &apply_context(&theta, ty),
                theta,
            ))
        }
    }
}
fn synth(e: Term, mut ctx: Context) -> Result<(Type, Context), (CheckingError, Context)> {
    println!("synthesizing Type for {e} under context {ctx}");
    match e {
        Term::Variable(name) => {
            println!("{:>20}", "Var");
            let annot = ctx.get_annotation(&name);
            if let Some(ty) = annot {
                Ok((ty.clone(), ctx))
            } else {
                Err((CheckingError::UnannotatedVariable(name), ctx))
            }
        }
        Term::LitInt(_) => Ok((Type::BaseType("int".to_owned()), ctx)),
        Term::LitBool(_) => Ok((Type::BaseType("bool".to_owned()), ctx)),
        Term::Unit => {
            println!("{:>20}", "1I=>");
            Ok((Type::Unit, ctx.clone()))
        }
        Term::Abstraction(x, e) => {
            println!("{:>20}", "->I=>");
            let alpha = ctx.fresh_existential();
            let beta = ctx.fresh_existential();
            let typed =
                ContextElement::TypedVariable(x.clone(), { Type::Existential(alpha.clone()) });
            let extended_gamma = ctx
                .extend(ContextElement::Existential(alpha.clone()))
                .extend(ContextElement::Existential(beta.clone()))
                .mark_scope()
                .extend(typed.clone());
            Ok((
                Type::Function(
                    Box::new(Type::Existential(alpha)),
                    Box::new(Type::Existential(beta.clone())),
                ),
                check(*e, Type::Existential(beta), extended_gamma)?.drop_scope(),
            ))
        }
        Term::Annotation(term, ty) => {
            println!("{:>20}", "Anno");
            Ok((*ty.clone(), check(*term, *ty, ctx)?))
        }
        Term::Application(e, e2) => {
            println!("{:>20}", "->E");
            let (a, theta) = synth(*e, ctx)?;
            Ok(synth_function(&apply_context(&theta, a), *e2, theta)?)
        }
        Term::Functor(name, term) => {
            let (ty, ctx) = synth(*term, ctx)?;
            Ok((Type::HigherKinded(vec![ty]), ctx))
        }
        Term::Let(name, term, term1) => {
            if ctx.any_matches(
                |elem| matches!(elem, ContextElement::TypedVariable(name1, _) if *name1 == name),
            ) {
                panic!("Initialized variable twice");
            };
            let (a, theta) = synth(*term, ctx)?;
            let delta = synth(*term1, theta.extend(ContextElement::TypedVariable(name, a)));
            return delta;
        }
    }
}
fn synth_function(
    a: &Type,
    e: Term,
    mut ctx: Context,
) -> Result<(Type, Context), (CheckingError, Context)> {
    println!("synthesizing type if {a} is applied to {e} under Context {ctx}");
    match a {
        Type::Existential(alpha_hat) => {
            println!("{:>20}", "α^App");
            let alpha_hat1 = ctx.fresh_existential();
            let alpha_hat2 = ctx.fresh_existential();
            let extended_gamma =
                ctx.insert_at(&ContextElement::Existential(alpha_hat.to_string()), vec![
                    (ContextElement::Existential(alpha_hat1.clone())),
                    (ContextElement::Existential(alpha_hat2.clone())),
                    (ContextElement::Solved(
                        alpha_hat.to_string(),
                        Type::Function(
                            Box::new(Type::Existential(alpha_hat1.clone())),
                            Box::new(Type::Existential(alpha_hat2.clone())),
                        ),
                    )),
                ]);
            Ok((
                Type::Existential(alpha_hat2),
                check(e, Type::Existential(alpha_hat1), ctx)?,
            ))
        }
        Type::Quantification(alpha, ty) => {
            println!("{:>20}", "∀App");
            let alpha_hat = ctx.fresh_existential();
            let extendet_gamma = ctx.extend(ContextElement::Existential(alpha_hat.clone()));
            synth_function(
                &substitute_existential(alpha, &Type::Existential(alpha_hat.to_string()), ty),
                e,
                extendet_gamma,
            )
        }
        Type::Function(a, c) => {
            println!("{:>20}", "->App");
            Ok((*a.clone(), check(e, *a.clone(), ctx)?))
        }
        _ => panic!(),
    }
}
/// Under input context ctx, type A is a subtype of B
fn subtype(ty: &Type, ty2: &Type, mut ctx: Context) -> Context {
    println!("have {ty} be a subtype of {ty2} under Context {ctx}");
    match (ty, ty2) {
        (Type::Unit, Type::Unit) => ctx.clone(),
        (Type::BaseType(name), Type::BaseType(name2)) if name == name2 => ctx.clone(),
        (Type::Variable(alpha1), Type::Variable(alpha2)) => {
            if ctx.is_well_formed(ty) {
                if alpha1 == alpha2 {
                    ctx.clone()
                } else {
                    panic!("Variables don't match in subtyping")
                }
            } else {
                panic!("{alpha2} is not well formed")
            }
        }
        (Type::Existential(alpha_hat), Type::Existential(alpha_hat2))
            if alpha_hat == alpha_hat2 =>
        {
            if ctx.is_well_formed(ty) {
                ctx.clone()
            } else {
                panic!("{alpha_hat2} is not well formed")
            }
        }
        (Type::Function(arg_a1, arg_a2), Type::Function(arg_b1, arg_b2)) => {
            let theta = subtype(arg_a1, arg_b1, ctx);
            let delta = subtype(
                &apply_context(&theta, *arg_a1.clone()),
                &apply_context(&theta, *arg_b2.clone()),
                theta,
            );
            return delta;
        }
        (Type::HigherKinded(v1), Type::HigherKinded(v2)) => {
            if v1.len() != v2.len() {
                panic!("Cannot subtype two higher kinded types with different arity")
            }
            let mut ctx = ctx;
            for i in 0..v1.len() {
                ctx = subtype(&v1[i], &v2[i], ctx);
            }
            ctx
        }
        // If a function returns a type variable, then it is ceartainly polymorphic
        (a, Type::Quantification(name, b)) => {
            let extendet_gamma = ctx
                .mark_scope()
                .extend(ContextElement::Variable(name.to_string()));
            let delta = subtype(a, b, extendet_gamma).drop_scope();
            return delta;
        }
        // If a function takes a type variable, then it might be restricted by it's callers
        (Type::Quantification(name, b), a) => {
            let alpha_hat = ctx.fresh_existential();
            let extendet_gamma = ctx
                .mark_scope()
                .extend(ContextElement::Existential(alpha_hat.clone()));
            let delta = subtype(
                &substitute_existential(name, &Type::Variable(alpha_hat), a),
                b,
                extendet_gamma,
            )
            .drop_scope();
            return delta;
        }
        (Type::Existential(alpha_hat), ty) => {
            ctx.instantiate(alpha_hat.to_string(), ty, Direction::Left)
        }
        (ty, Type::Existential(alpha_hat)) => {
            ctx.instantiate(alpha_hat.to_string(), ty, Direction::Right)
        }
        (a, b) => panic!("Cannnot subtype {a} with {b}"),
    }
}

/// FV(A)
fn occurs_check(alpha_hat: &String, ty: &Type) -> bool {
    match ty {
        Type::Unit | Type::BaseType(_) => false,
        Type::Variable(a) | Type::Existential(a) => a == alpha_hat,
        Type::Quantification(a, ty) => a == alpha_hat || occurs_check(alpha_hat, ty),
        Type::Function(a, b) => occurs_check(alpha_hat, a) || occurs_check(alpha_hat, b),
        Type::HigherKinded(vec) => vec.iter().all(|ty| occurs_check(alpha_hat, ty)),
    }
}
fn substitute_existential(alpha_hat: &String, alpha: &Type, ty: &Type) -> Type {
    match ty {
        Type::Unit => Type::Unit,
        Type::BaseType(_) => ty.clone(),
        Type::Variable(var) => {
            if var == alpha_hat {
                alpha.clone()
            } else {
                ty.clone()
            }
        }
        Type::Existential(beta_hat) => {
            if alpha_hat == beta_hat {
                alpha.clone()
            } else {
                ty.clone()
            }
        }
        Type::Quantification(a, b) => {
            if alpha_hat == a {
                Type::Quantification(a.to_string(), Box::new(ty.clone()))
            } else {
                Type::Quantification(
                    a.to_string(),
                    Box::new(substitute_existential(alpha_hat, alpha, b)),
                )
            }
        }
        Type::Function(a, b) => Type::Function(
            Box::new(substitute_existential(alpha_hat, alpha, a)),
            Box::new(substitute_existential(alpha_hat, alpha, b)),
        ),
        Type::HigherKinded(vec) => todo!(),
    }
}
fn apply_context(ctx: &Context, ty: Type) -> Type {
    match ty {
        /// [Γ]1 = 1
        unit @ (Type::Unit | Type::BaseType(_)) => unit,
        /// [Γ]α = α
        alpha @ Type::Variable(_) => alpha,
        /// [Γ](∀α. A) = ∀α. [Γ]A
        Type::Quantification(n, alpha) => {
            Type::Quantification(n, Box::new(apply_context(ctx, *alpha)))
        }
        /// [Γ](A → B) = ([Γ]A) → ([Γ]B)
        Type::Function(a, b) => Type::Function(
            Box::new(apply_context(ctx, *a)),
            Box::new(apply_context(ctx, *b)),
        ),
        /// [Γ[`α_hat``α_hat`at = `α_hat`        
        /// [Γ[`α_hat` = τ`α_hat` = `α_hat`= τ]]τ
        Type::Existential(ref alpha_hat) => ctx
            .get_solved(alpha_hat)
            .map_or(ty, |tau| apply_context(ctx, tau.clone())),
        Type::HigherKinded(vec) => Type::HigherKinded(
            vec.iter()
                .map(|ty| apply_context(ctx, ty.clone()))
                .collect(),
        ),
        Type::Unit => todo!(),
        Type::BaseType(_) => todo!(),
    }
}

fn main() {}
#[test]
fn basic() -> Result<(), CheckingError> {
    let ctx = Context::new();
    let (ty, ctx) = synth(Term::Unit, ctx).map_err(|a| a.0)?;
    assert_eq!(apply_context(&ctx, ty), Type::Unit);
    Ok(())
}

#[test]
fn application() -> Result<(), CheckingError> {
    let ctx = Context::new();
    let (ty, omega) = synth(
        Term::Application(
            Term::Abstraction("x".into(), Term::Variable("x".into()).into()).into(),
            Box::new(Term::Unit),
        ),
        ctx,
    )
    .map_err(|a| a.0)?;
    assert_eq!(Type::Unit, apply_context(&omega, ty));
    Ok(())
}

#[test]
fn lambda() -> Result<(), CheckingError> {
    let ctx = Context::new();
    let (ty, omega) = synth(
        Term::Abstraction("x".into(), Term::Variable("x".into()).into()),
        ctx,
    )
    .map_err(|a| a.0)?;
    assert_eq!(
        apply_context(&omega, ty),
        Type::Function(
            Type::Existential("t0".into()).into(),
            Type::Existential("t0".into()).into()
        )
    );
    Ok(())
}

#[test]
fn idunit() -> Result<(), CheckingError> {
    let ctx = Context::new();
    let (ty, omega) =
        synth(Term::Application(id_fn().into(), Term::Unit.into()), ctx).map_err(|a| a.0)?;
    assert_eq!(Type::Unit, apply_context(&omega, ty));
    Ok(())
}

fn id_fn() -> Term {
    Term::Annotation(
        Term::Abstraction("x".into(), Term::Variable("x".into()).into()).into(),
        Box::new(Type::Quantification(
            "t".into(),
            Type::Function(
                Type::Variable("t".into()).into(),
                Type::Variable("t".into()).into(),
            )
            .into(),
        )),
    )
}
#[test]
fn nested_to_string() -> Result<(), CheckingError> {
    let ctx = Context::new();
    let app = Term::Application(
        Term::Annotation(
            Box::new(Term::Abstraction(
                "x".into(),
                Term::Functor("F".to_owned(), Term::LitBool(false).into()).into(),
            )),
            Type::Function(
                Type::HigherKinded(vec![Type::BaseType("int".into())]).into(),
                Type::HigherKinded(vec![Type::BaseType("bool".into())]).into(),
            )
            .into(),
        )
        .into(),
        Term::Functor("Option".into(), Term::LitInt(23).into()).into(),
    );
    println!("{app}");
    let (ty, omega) = synth(app, ctx).map_err(|a| a.0)?;
    assert_eq!(
        Type::HigherKinded(vec![Type::BaseType("int".into())]),
        apply_context(&omega, ty)
    );
    Ok(())
}
#[test]
fn let_with_fun() -> Result<(), CheckingError> {
    let ctx = Context::new();
    let (ty, omega) = synth(
        Term::Let(
            "id".to_owned(),
            id_fn().into(),
            Term::Application(Term::Variable("id".to_owned()).into(), Term::Unit.into()).into(),
        ),
        ctx,
    )
    .map_err(|a| a.0)?;
    assert_eq!(Type::Unit, apply_context(&omega, ty));
    Ok(())
}
