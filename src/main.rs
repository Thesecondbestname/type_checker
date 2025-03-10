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
            ident_level: 0,
        }
    }
    fn indent(&mut self) -> usize {
        self.ident_level += 1;
        self.ident_level
    }
    fn unindent(&mut self) -> usize {
        self.ident_level -= 1;
        self.ident_level
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
            Type::HigherKinded(_, generics, open) => generics
                .iter()
                .all(|ty| ty.as_ref().is_none_or(|ty| self.is_well_formed(ty))),
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
    fn instantiate<'a>(
        mut self,
        alpha_hat: String,
        ty: Type,
        dir: Direction,
    ) -> Result<Context, (CheckingError, Context)> {
        println!(
            "{} instantiate {alpha_hat} to a subtype of {ty} under Context {self}",
            "-".repeat(self.indent())
        );
        assert!(!occurs_check(&alpha_hat, &ty));
        let mut alpha = ContextElement::Existential(alpha_hat.clone());
        let (begin, rest) = &self.clone().split_at(&alpha);
        if ty.is_monotype() && begin.is_well_formed(&ty) {
            println!("{:>20}", "InstLSolve");
            return Ok(self.insert_at(&alpha, vec![ContextElement::Solved(alpha_hat, ty)]));
        }
        let t = match (ty, dir) {
            (ref ty @ Type::Existential(ref beta), _) => {
                println!("{:>20}", "InstLReach");
                assert!(rest.is_well_formed(ty));
                Ok(
                    self.insert_at(&ContextElement::Existential(beta.to_string()), vec![
                        ContextElement::Solved(beta.to_string(), (Type::Existential(alpha_hat))),
                    ]),
                )
            }
            (Type::Quantification(beta, ty), Direction::Left) => {
                println!("{:>20}", "InstLAllR");
                let beta_hat = self.fresh_existential();
                let mut extended_gamma = self.extend(ContextElement::Existential(beta_hat));
                let delta = extended_gamma
                    .instantiate(alpha_hat, *ty, Direction::Left)?
                    .drop(ContextElement::Existential(beta.to_string()));
                Ok(delta)
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
                        substitute_existential(&beta_hat, &Type::Variable(beta.to_string()), *ty),
                        Direction::Right,
                    )?
                    .drop_scope();
                Ok(delta)
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
                let mut theta = extended_gamma.instantiate(alpha_hat1, *a, dir.flip())?;
                let b = apply_context(&theta, *b.clone());
                let delta = theta.instantiate(alpha_hat2, b, dir);
                delta
            }
            (t, dir) => Err((CheckingError::InvalidInstantiation(t, alpha_hat), self)),
        };
        t.map(|mut a| {
            println!(
                "{} instantiate finished with context {a}",
                "-".repeat(a.unindent())
            );
            a
        })
    }

    fn split_at(mut self, alpha: &ContextElement) -> (Context, Context) {
        let (begin, rest) = self.elements.split_at(
            self.elements
                .iter()
                .position(|elem| elem == alpha)
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
        (l, r)
    }
    /// Γ == ∆, ^α
    fn has_existential(&self, alpha_hat: &str) -> bool {
        self.elements
            .iter()
            .any(|elem| elem == &ContextElement::Existential(alpha_hat.to_string()))
    }
}

#[derive(Debug, Clone, Copy)]
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

fn check(e: Term, ty: &Type, ctx: Context) -> Result<(Context), (CheckingError, Context)> {
    let mut ctx = ctx;
    println!(
        "{} checking that {e} has type {ty} under context {ctx}",
        "-".repeat(ctx.indent())
    );
    let mut t = match (e, ty) {
        (Term::Unit, ty @ Type::Unit) => {
            println!("{:>20}", "1I");
            Ok(ctx)
        }
        (e, Type::Quantification(name, ty)) => {
            println!("{:>20}", "∀I");
            let mut extendet_gamma = ctx
                .mark_scope()
                .extend(ContextElement::Variable(name.to_string()));
            let delta = check(e, ty, extendet_gamma)?.drop_scope();
            return Ok(delta);
        }
        (Term::Abstraction(x, term), Type::Function(a, b)) => {
            println!("{:>20}", "->I");
            let typed = ContextElement::TypedVariable(x, *a.clone());
            let extended_gamma = ctx.mark_scope().extend(typed);
            let delta = check(*term, &*b, extended_gamma)?.drop_scope();
            return Ok(delta);
        }
        (Term::Let(name, expr, tail), ty) => {
            println!("{:>20}", "Let");
            if ctx.any_matches(
                |elem| matches!(elem, ContextElement::TypedVariable(name1, _) if *name1 == name),
            ) {
                return Err((CheckingError::DoubelyInitializedVariable(name), ctx));
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
            subtype(
                apply_context(&theta, a.clone()),
                apply_context(&theta, ty.clone()),
                theta,
            )
        }
    };
    t.map(|mut a| {
        println!("{} checked context {}", "-".repeat(a.unindent() + 1), a,);
        a
    })
}
fn synth<'a>(e: Term, mut ctx: Context) -> Result<(Type, Context), (CheckingError, Context)> {
    let indent = ctx.indent();
    println!(
        "{} synthesizing Type for {e} under context {ctx}",
        "-".repeat(indent)
    );
    let mut t = match e {
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
            Ok((Type::Unit, ctx))
        }
        Term::Abstraction(x, e) => {
            println!("{:>20}", "->I=>");
            let alpha_hat = ctx.fresh_existential();
            let beta_hat = ctx.fresh_existential();
            let typed = ContextElement::TypedVariable(x, { Type::Existential(alpha_hat.clone()) });
            let extended_gamma = ctx
                .extend(ContextElement::Existential(alpha_hat.clone()))
                .extend(ContextElement::Existential(beta_hat.clone()))
                .mark_scope()
                .extend(typed);
            Ok((
                Type::Function(
                    Box::new(Type::Existential(alpha_hat)),
                    Box::new(Type::Existential(beta_hat.clone())),
                ),
                check(*e, &Type::Existential(beta_hat), extended_gamma)?,
            ))
        }
        Term::Annotation(term, ty) => {
            println!("{:>20}", "Anno");
            let delta = check(*term, &ty, ctx)?;
            Ok((*ty, delta))
        }
        Term::Application(e1, e2) => {
            println!("{:>20}", "->E");
            let (a, theta) = synth(*e1, ctx)?;
            Ok(synth_function(apply_context(&theta, a), *e2, theta)?)
        }
        Term::Functor(name, term) => {
            println!("{:>20}", "Cons");
            let (ty, ctx) = synth(*term, ctx)?;
            Ok((Type::HigherKinded(Some(name), vec![Some(ty)], false), ctx))
        }
        Term::Let(name, term, term1) => {
            println!("{:>20}", "=>Let");
            if ctx.any_matches(
                |elem| matches!(elem, ContextElement::TypedVariable(name1, _) if *name1 == name),
            ) {
                return Err((CheckingError::DoubelyInitializedVariable(name), ctx));
            };
            let (a, theta) = synth(*term, ctx)?;
            let delta = synth(*term1, theta.extend(ContextElement::TypedVariable(name, a)));
            delta
        }
    };
    let mut indent = 0;
    t.as_mut().map(|mut a| {
        indent = a.1.unindent();
        a
    });
    println!(
        "{} synthesized type {}",
        "-".repeat(indent),
        t.as_ref()
            .cloned()
            .map_or("".to_string(), |a| a.0.to_string()),
    );
    t
}
fn synth_function(
    a: Type,
    e: Term,
    mut ctx: Context,
) -> Result<(Type, Context), (CheckingError, Context)> {
    println!("synthesizing type if {a} is applied to {e} under Context {ctx}");
    let t = match a {
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
                check(e, &Type::Existential(alpha_hat1), ctx)?,
            ))
        }
        Type::Quantification(alpha, ty) => {
            println!("{:>20}", "∀App");
            let alpha_hat = ctx.fresh_existential();
            let extendet_gamma = ctx.extend(ContextElement::Existential(alpha_hat.clone()));
            synth_function(
                substitute_existential(&alpha, &Type::Existential(alpha_hat.to_string()), *ty),
                e,
                extendet_gamma,
            )
        }
        Type::Function(a, c) => {
            println!("{:>20}", "->App");
            Ok((*c, check(e, &a, ctx)?))
        }
        _ => panic!(),
    };
    println!(
        "synthesized type {}",
        t.as_ref()
            .cloned()
            .map_or("".to_string(), |a| a.0.to_string())
    );
    t
}
/// Under input context ctx, type A is a subtype of B
fn subtype<'a>(
    ty1: Type,
    ty2: Type,
    mut ctx: Context,
) -> Result<Context, (CheckingError, Context)> {
    println!(
        "{} have {ty1} be a subtype of {ty2} under Context {ctx}",
        "-".repeat(ctx.indent())
    );
    let is_well_formed_ty = ctx.is_well_formed(&ty1);
    let is_well_formed_ty2 = ctx.is_well_formed(&ty2);
    let ty1_hk_len = if let Type::HigherKinded(_, v, _) = &ty1 {
        Some(v.len())
    } else {
        None
    };
    let ty2_hk_len = if let Type::HigherKinded(_, v, _) = &ty2 {
        Some(v.len())
    } else {
        None
    };

    let t = match (ty1, ty2) {
        (Type::Unit, Type::Unit) => Ok(ctx),
        (Type::BaseType(name), Type::BaseType(name2)) if name == name2 => Ok(ctx),
        (Type::Variable(alpha1), Type::Variable(alpha2)) => {
            println!("{:>20}", "<:Var");
            if is_well_formed_ty {
                if alpha1 == alpha2 {
                    Ok(ctx)
                } else {
                    Err((
                        CheckingError::TypeMissmatch(
                            Type::Variable(alpha1),
                            Type::Variable(alpha2),
                        ),
                        ctx,
                    ))
                }
            } else {
                Err((CheckingError::NotWellFormed(Type::Variable(alpha2)), ctx))
            }
        }
        (Type::Existential(alpha_hat), Type::Existential(alpha_hat2))
            if alpha_hat == alpha_hat2 =>
        {
            println!("{:>20}", "<:Exvar");
            if is_well_formed_ty2 {
                Ok(ctx)
            } else {
                Err((
                    CheckingError::NotWellFormed(Type::Existential(alpha_hat2)),
                    ctx,
                ))
            }
        }
        (Type::Function(arg_a1, arg_a2), Type::Function(ref arg_b1, ref arg_b2)) => {
            println!("{:>20}", "<:->");
            let theta = subtype(*arg_b1.clone(), *arg_a1, ctx)?;
            let delta = subtype(
                apply_context(&theta, *arg_a2),
                apply_context(&theta, *arg_b2.clone()),
                theta,
            );
            return delta;
        }
        (ty1 @ Type::HigherKinded(_, _, true), ty2 @ Type::HigherKinded(_, _, false))
            if ty1_hk_len > ty2_hk_len =>
        {
            Err((CheckingError::KindMissmatch(ty1, ty2), ctx))
        }
        (ty1 @ Type::HigherKinded(_, _, false), ty2 @ Type::HigherKinded(_, _, true))
            if ty1_hk_len < ty2_hk_len =>
        {
            Err((CheckingError::KindMissmatch(ty1, ty2), ctx))
        }
        (ty1 @ Type::HigherKinded(_, _, false), ty2 @ Type::HigherKinded(_, _, false))
            if ty1_hk_len != ty2_hk_len =>
        {
            Err((CheckingError::KindMissmatch(ty1, ty2), ctx))
        }
        (Type::HigherKinded(Some(name), _, _), Type::HigherKinded(Some(name1), _, _))
            if name != name1 =>
        {
            Err((
                CheckingError::TypeMissmatch(Type::BaseType(name), Type::BaseType(name1)),
                ctx,
            ))
        }
        (Type::HigherKinded(name1, v1, open), Type::HigherKinded(name2, v2, open2)) => {
            println!("{:>20}", "<:HK");
            let mut ctx = ctx;
            for i in 0..(v1.len().min(v2.len())) {
                if let (Some(ty1), Some(ty2)) = (v1[i].clone(), v2[i].clone()) {
                    ctx = subtype(ty1, ty2, ctx)?
                }
            }
            Ok(ctx)
        }
        // If a function returns a type variable, then it is ceartainly polymorphic
        (a, Type::Quantification(ref name, ref b)) => {
            println!("{:>20}", "<:∀R");
            let extendet_gamma = ctx
                .mark_scope()
                .extend(ContextElement::Variable(name.to_string()));
            let delta = subtype(a, *b.clone(), extendet_gamma)?.drop_scope();
            return Ok(delta);
        }
        // If a function takes a type variable, then it might be restricted by it's callers
        (Type::Quantification(name, b), a) => {
            println!("{:>20}", "<:∀L");
            let alpha_hat = ctx.fresh_existential();
            let extendet_gamma = ctx
                .mark_scope()
                .extend(ContextElement::Existential(alpha_hat.clone()));
            let delta = subtype(
                substitute_existential(&name, &Type::Variable(alpha_hat), a),
                *b,
                extendet_gamma,
            )?
            .drop_scope();
            return Ok(delta);
        }
        (Type::Existential(alpha_hat), ty) => {
            ctx.instantiate(alpha_hat.to_string(), ty, Direction::Left)
        }
        (ty, Type::Existential(ref alpha_hat)) => {
            ctx.instantiate(alpha_hat.to_string(), ty, Direction::Right)
        }
        (a, b) => Err((CheckingError::TypeMissmatch(a, b), ctx)),
    };

    t.map(|mut a| {
        println!("{} checked context {}", "-".repeat(a.unindent() + 1), a,);
        a
    })
}

/// FV(A)
fn occurs_check(alpha_hat: &String, ty: &Type) -> bool {
    match ty {
        Type::Unit | Type::BaseType(_) => false,
        Type::Variable(a) | Type::Existential(a) => a == alpha_hat,
        Type::Quantification(a, ty) => a == alpha_hat || occurs_check(alpha_hat, ty),
        Type::Function(a, b) => occurs_check(alpha_hat, a) || occurs_check(alpha_hat, b),
        Type::HigherKinded(_, generics, open) => generics
            .iter()
            .all(|ty| ty.clone().is_some_and(|ref ty| occurs_check(alpha_hat, ty))),
    }
}
fn substitute_existential(alpha_hat: &String, alpha: &Type, ty: Type) -> Type {
    match ty {
        Type::Unit => Type::Unit,
        Type::BaseType(_) => ty,
        Type::Variable(ref var) => {
            if var == alpha_hat {
                alpha.clone()
            } else {
                ty
            }
        }
        Type::Existential(ref beta_hat) => {
            if *alpha_hat == *beta_hat {
                alpha.clone()
            } else {
                ty
            }
        }
        Type::Quantification(a, b) => {
            if *alpha_hat == a {
                Type::Quantification(a.to_string(), Box::new(Type::Quantification(a, b)))
            } else {
                Type::Quantification(
                    a.to_string(),
                    Box::new(substitute_existential(alpha_hat, alpha, *b.clone())),
                )
            }
        }
        Type::Function(a, b) => Type::Function(
            Box::new(substitute_existential(alpha_hat, alpha, *a)),
            Box::new(substitute_existential(alpha_hat, alpha, *b)),
        ),
        Type::HigherKinded(name, ty, open) => Type::HigherKinded(
            name,
            ty.into_iter()
                .map(|a| {
                    if let Some(ty) = a {
                        Some(substitute_existential(alpha_hat, alpha, ty))
                    } else {
                        a
                    }
                })
                .collect(),
            open,
        ),
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
        Type::HigherKinded(name, ty, open) => Type::HigherKinded(
            name,
            ty.into_iter()
                .map(|ty| ty.map(|ty| apply_context(ctx, ty)))
                .collect(),
            open,
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
    let ctx2 = Context::new();
    let app = Term::Application(
        Term::Annotation(
            Box::new(Term::Abstraction(
                "x".into(),
                Term::Functor("Option".to_owned(), Term::LitBool(false).into()).into(),
            )),
            Type::Function(
                Type::HigherKinded(None, vec![Some(Type::BaseType("int".into()))], true).into(),
                Type::HigherKinded(
                    Some("Option".to_owned()),
                    vec![Some(Type::BaseType("bool".into()))],
                    false,
                )
                .into(),
            )
            .into(),
        )
        .into(),
        Term::Functor("Option".into(), Term::LitInt(23).into()).into(),
    );
    println!("{app}");
    let (ty, omega) = synth(app, ctx).map_err(|a| a.0)?;
    println!("{omega}");
    assert_eq!(
        Type::HigherKinded(
            Some("Option".to_owned()),
            vec![Some(Type::BaseType("bool".into()))],
            false
        ),
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
