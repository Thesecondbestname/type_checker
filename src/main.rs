#![allow(unused)]
#![allow(clippy::uninlined_format_args)]
mod display;
mod lower;
mod resolve_names;
mod types;

use resolve_names::debrujin::resolve_names;
use types::Ast;
use types::CheckingError;
use types::ContextElement;
use types::TCContext;
use types::Type;
use types::TypedVar;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct VarId(pub usize);
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct TyId(pub usize);
impl TCContext {
    const fn new() -> Self {
        Self {
            elements: vec![],
            existentials: 0,
            markers: vec![],
            ident_level: 0,
        }
    }
    const fn indent(&mut self) -> usize {
        self.ident_level += 1;
        self.ident_level
    }
    const fn unindent(&mut self) -> usize {
        self.ident_level -= 1;
        self.ident_level
    }
    const fn fresh_existential(&mut self) -> VarId {
        self.existentials += 1;
        VarId(self.existentials)
    }
    fn is_well_formed(&self, ty: &Type<VarId>) -> bool {
        match ty {
            Type::Unit | Type::BaseType(_) => true,
            Type::Variable(var) => self.contains(&ContextElement::Variable(*var)),
            Type::Existential(alpha_hat) => {
                self.contains(&ContextElement::Existential(*alpha_hat))
                    || self.get_solved(alpha_hat).is_some()
            }
            Type::Quantification(alpha_hat, ty) => self
                .clone()
                .extend(ContextElement::Existential(*alpha_hat))
                .is_well_formed(ty),
            Type::Function(a, b) => self.is_well_formed(a) && self.is_well_formed(b),
            Type::HigherKinded(_, generics, open) => generics
                .iter()
                .all(|ty| ty.as_ref().is_none_or(|ty| self.is_well_formed(ty))),
            Type::Product(vec) => vec.iter().all(|a| self.is_well_formed(a)),
            Type::Sum(vec) => vec.iter().all(|a| self.is_well_formed(a)),
        }
    }
    fn contains(&self, c: &ContextElement) -> bool {
        self.elements.iter().any(|elem| elem == c)
    }
    fn any_matches<F: FnMut(&ContextElement) -> bool>(&self, f: F) -> bool {
        self.elements.iter().any(f)
    }
    fn mark_scope(mut self) -> Self {
        self.markers.push(self.elements.len());
        self
    }
    fn begin_scope_with(mut self, elem: ContextElement) -> Self {
        self.elements.push(elem);
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
        let mut elements = self.elements;
        let rest = elements.split_off(pos);
        Self { elements, ..self }
    }
    /// Γ, α, Γ' ->  Γ, β, Γ'
    fn insert_at(self, alpha: &ContextElement, beta: Vec<ContextElement>) -> Self {
        let pos = self
            .elements
            .iter()
            .position(|elem| elem == alpha)
            .unwrap_or_else(|| panic!("Could not find {} in context to replace", alpha));
        let mut elements = self.elements;
        elements.splice(pos..=pos, beta);
        Self { elements, ..self }
    }
    /// Γ -> Γ [^α = τ]
    fn get_solved(&self, alpha_hat: &VarId) -> Option<&Type<VarId>> {
        println!(
            "{} looking for {alpha_hat} in {self}",
            "-".repeat(self.ident_level)
        );
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
    fn get_annotation(&self, alpha_hat: VarId) -> Option<&Type<VarId>> {
        for elem in &self.elements {
            if let ContextElement::TypedVariable(a, b) = elem {
                if alpha_hat == *a {
                    return Some(b);
                }
            }
        }
        None
    }

    /// instantiate ^α to a subtype of A
    fn instantiate(
        mut self,
        alpha_hat: VarId,
        ty: Type<VarId>,
        dir: Direction,
    ) -> Result<Self, (CheckingError, Self)> {
        println!(
            "{} instantiate {alpha_hat} to a subtype of {ty} under Context {self}",
            "-".repeat(self.indent())
        );
        assert!(!occurs_check(alpha_hat, &ty));
        let mut alpha = ContextElement::Existential(alpha_hat);
        let (begin, rest) = &self.clone().split_at(&alpha);
        if ty.is_monotype() && begin.is_well_formed(&ty) {
            println!("{:>20}", "InstLSolve");
            return Ok(self.insert_at(&alpha, vec![ContextElement::Solved(alpha_hat, ty)]));
        }
        let t = match (ty, dir) {
            (ref ty @ Type::Existential(ref beta), _) => {
                println!("{:>20}", "InstLReach");
                assert!(rest.is_well_formed(ty));
                Ok(self.insert_at(
                    &ContextElement::Existential(*beta),
                    vec![ContextElement::Solved(
                        *beta,
                        (Type::Existential(alpha_hat)),
                    )],
                ))
            }
            (Type::Quantification(beta, ty), Direction::Left) => {
                println!("{:>20}", "InstLAllR");
                let beta_hat = self.fresh_existential();
                let mut extended_gamma = self.extend(ContextElement::Existential(beta_hat));
                let delta = extended_gamma
                    .instantiate(alpha_hat, *ty, Direction::Left)?
                    .drop(ContextElement::Existential(beta));
                Ok(delta)
            }
            (Type::Quantification(beta, ty), Direction::Right) => {
                println!("{:>20}", "InstRAllL");
                let beta_hat = self.fresh_existential();
                let extended_gamma = self
                    .mark_scope()
                    .extend(ContextElement::Existential(beta_hat));
                let delta = extended_gamma
                    .instantiate(
                        alpha_hat,
                        substitute_existential(&beta_hat, Type::Variable(beta), *ty),
                        Direction::Right,
                    )?
                    .drop_scope();
                Ok(delta)
            }
            (Type::Function(a, b), dir) => {
                println!("{:>20}", "InstArr");
                let alpha_hat1 = self.fresh_existential();
                let alpha_hat2 = self.fresh_existential();
                let extended_gamma = self.insert_at(
                    &alpha,
                    vec![
                        ContextElement::Existential(alpha_hat1),
                        ContextElement::Existential(alpha_hat2),
                        ContextElement::Solved(
                            alpha_hat,
                            Type::Function(
                                Box::new(Type::Existential(alpha_hat1)),
                                Box::new(Type::Existential(alpha_hat2)),
                            ),
                        ),
                    ],
                );
                let mut theta = extended_gamma.instantiate(alpha_hat1, *a, dir.flip())?;
                let b = apply_context(&theta, *b);
                let delta = theta.instantiate(alpha_hat2, b, dir);
                delta
            }
            (t, dir) => Err((
                CheckingError::InvalidInstantiation(t, alpha_hat.to_string()),
                self,
            )),
        };
        t.map(|mut a| {
            println!(
                "{} instantiate finished with context {a}",
                "-".repeat(a.unindent())
            );
            a
        })
    }

    fn split_at(mut self, alpha: &ContextElement) -> (TCContext, TCContext) {
        let (begin, rest) = self.elements.split_at(
            self.elements
                .iter()
                .position(|elem| elem == alpha)
                .unwrap_or_else(|| panic!("Could not find {} in context to split", alpha)),
        );
        let (l, r) = (
            TCContext {
                elements: begin.to_vec(),
                ..self.clone()
            },
            TCContext {
                elements: rest.to_vec(),
                ..self.clone()
            },
        );
        (l, r)
    }
    /// Γ == ∆, ^α
    fn has_existential(&self, alpha_hat: VarId) -> bool {
        self.elements
            .iter()
            .any(|elem| elem == &ContextElement::Existential(alpha_hat))
    }
}

#[derive(Debug, Clone, Copy)]
enum Direction {
    Left,
    Right,
}
impl Direction {
    const fn flip(self) -> Self {
        match self {
            Self::Left => Self::Right,
            Self::Right => Self::Left,
        }
    }
}

fn check(
    e: Ast<VarId>,
    ty: Type<VarId>,
    ctx: TCContext,
) -> Result<(Ast<TypedVar>, TCContext), (CheckingError, TCContext)> {
    let mut ctx = ctx;
    println!(
        "{} checking that {e} has type {ty} under context {ctx}",
        "-".repeat(ctx.indent())
    );
    let mut t = match (e, ty) {
        (Ast::Unit, ty @ Type::Unit) => {
            println!("{:>20}", "1I");
            Ok((Ast::Unit, ctx))
        }
        (e, Type::Quantification(name, ty)) => {
            println!("{:>20}", "∀I");
            let mut extendet_gamma = ctx.mark_scope().extend(ContextElement::Variable(name));
            let (ast_prime, delta) = check(e, *ty, extendet_gamma)?;
            return Ok((ast_prime, delta.drop_scope()));
        }
        (Ast::Abstraction(x, term), Type::Function(a, b)) => {
            println!("{:>20}", "->I");
            let typed = ContextElement::TypedVariable(x, *a.clone());
            let extended_gamma = ctx.mark_scope().extend(typed);
            let (ast_prime, delta) = check(*term, *b, extended_gamma)?;
            return Ok((
                Ast::Abstraction(TypedVar(x, *a), Box::new(ast_prime)),
                delta.drop_scope(),
            ));
        }
        (Ast::Let(name, expr, tail), ty) => {
            println!("{:>20}", "Let");
            if ctx.any_matches(
                |elem| matches!(elem, ContextElement::TypedVariable(name1, _) if *name1 == name),
            ) {
                return Err((CheckingError::DoubelyInitializedVariable(name), ctx));
            }
            let (typed_expr, a, theta) = synth(*expr, ctx)?;
            let (typed_tail, delta) = check(
                *tail,
                ty,
                theta.extend(ContextElement::TypedVariable(name, a.clone())),
            )?;
            return Ok((
                Ast::Let(TypedVar(name, a), typed_expr.into(), typed_tail.into()),
                delta,
            ));
        }
        (e, ty) => {
            println!("{:>20}", "Sub");
            let (typed_e, a, theta) = synth(e, ctx)?;
            subtype(apply_context(&theta, a), apply_context(&theta, ty), theta)
                .map(|a| (typed_e, a))
        }
    };
    t.map(|mut a| {
        println!("{} checked context {}", "-".repeat(a.1.unindent() + 1), a.1);
        a
    })
}
fn synth(
    e: Ast<VarId>,
    mut ctx: TCContext,
) -> Result<(Ast<TypedVar>, Type<VarId>, TCContext), (CheckingError, TCContext)> {
    let indent = ctx.indent();
    println!(
        "{} synthesizing Type for {e} under context {ctx}",
        "-".repeat(indent)
    );
    let mut t = match e {
        Ast::Variable(name) => {
            println!("{:>20}", "Var");
            let annot = ctx.get_annotation(name);
            if let Some(ty) = annot {
                Ok((Ast::Variable(TypedVar(name, ty.clone())), ty.clone(), ctx))
            } else {
                Err((CheckingError::UnannotatedVariable(name), ctx))
            }
        }
        Ast::LitInt(i) => Ok((Ast::LitInt(i), Type::BaseType("Int".to_owned()), ctx)),
        Ast::Unit => {
            println!("{:>20}", "1I=>");
            Ok((Ast::Unit, Type::Unit, ctx))
        }
        Ast::Abstraction(x, e) => {
            println!("{:>20}", "->I=>");
            let alpha_hat = ctx.fresh_existential();
            let beta_hat = ctx.fresh_existential();
            let typed = ContextElement::TypedVariable(x, { Type::Existential(alpha_hat) });
            let extended_gamma = ctx
                .extend(ContextElement::Existential(alpha_hat))
                .extend(ContextElement::Existential(beta_hat))
                .mark_scope()
                .extend(typed);
            let (typed_e, delta) = check(*e, Type::Existential(beta_hat), extended_gamma)?;
            Ok((
                Ast::Abstraction(TypedVar(x, Type::Existential(alpha_hat)), typed_e.into()),
                Type::Function(
                    Box::new(Type::Existential(alpha_hat)),
                    Box::new(Type::Existential(beta_hat)),
                ),
                delta,
            ))
        }
        Ast::Annotation(term, ty) => {
            println!("{:>20}", "Anno");
            let (typed_term, delta) = check(*term, *ty.clone(), ctx)?;
            Ok((typed_term, *ty, delta))
        }
        Ast::Application(e1, e2) => {
            println!("{:>20}", "->E");
            let (typed_e1, a, theta) = synth(*e1, ctx)?;
            let (typed_e2, b, delta) = synth_function(apply_context(&theta, a), *e2, theta)?;
            Ok((Ast::Application(typed_e1.into(), typed_e2.into()), b, delta))
        }
        Ast::Functor(name, term) => {
            println!("{:>20}", "Cons");
            let (typed_term, ty, ctx) = synth(*term, ctx)?;
            Ok((
                Ast::Functor(name.clone(), typed_term.into()),
                Type::HigherKinded(Some(name), vec![Some(ty)], false),
                ctx,
            ))
        }
        Ast::Let(name, term, term1) => {
            println!("{:>20}", "=>Let");
            if ctx.any_matches(
                |elem| matches!(elem, ContextElement::TypedVariable(name1, _) if *name1 == name),
            ) {
                return Err((CheckingError::DoubelyInitializedVariable(name), ctx));
            }
            let (typed_term, a, theta) = synth(*term, ctx)?;
            let (typed_term1, b, delta) = synth(
                *term1,
                theta.extend(ContextElement::TypedVariable(name, a.clone())),
            )?;
            Ok((
                Ast::Let(TypedVar(name, a), typed_term.into(), typed_term1.into()),
                b,
                delta,
            ))
        }
        Ast::Tuple(vec) => {
            let mut ctx = ctx;
            let mut tys = Vec::with_capacity(vec.len());
            let mut typed_es = Vec::with_capacity(vec.len());
            for e in vec {
                let (e_typed, ty, ctx_hat) = synth(e, ctx)?;
                ctx = ctx_hat;
                typed_es.push(e_typed);
                tys.push(ty);
            }
            Ok((Ast::Tuple(typed_es), Type::Product(tys), ctx))
        }
    };
    let mut indent = 0;
    t.as_mut().map(|mut a| {
        indent = a.2.unindent();
        a
    });
    println!(
        "{} synthesized type {}",
        "-".repeat(indent),
        t.as_ref().map_or("".to_string(), |a| a.0.to_string()),
    );
    t
}
fn synth_function(
    a: Type<VarId>,
    e: Ast<VarId>,
    mut ctx: TCContext,
) -> Result<(Ast<TypedVar>, Type<VarId>, TCContext), (CheckingError, TCContext)> {
    println!("synthesizing type if {a} is applied to {e} under Context {ctx}");
    let t = match a {
        Type::Existential(alpha_hat) => {
            println!("{:>20}", "α^App");
            let alpha_hat1 = ctx.fresh_existential();
            let alpha_hat2 = ctx.fresh_existential();
            let extended_gamma = ctx.insert_at(
                &ContextElement::Existential(alpha_hat),
                vec![
                    (ContextElement::Existential(alpha_hat1)),
                    (ContextElement::Existential(alpha_hat2)),
                    (ContextElement::Solved(
                        alpha_hat,
                        Type::Function(
                            Box::new(Type::Existential(alpha_hat1)),
                            Box::new(Type::Existential(alpha_hat2)),
                        ),
                    )),
                ],
            );
            let (typed_e, delta) = check(e, Type::Existential(alpha_hat1), extended_gamma)?;
            Ok((typed_e, Type::Existential(alpha_hat2), delta))
        }
        Type::Quantification(alpha, ty) => {
            println!("{:>20}", "∀App");
            let alpha_hat = ctx.fresh_existential();
            let extendet_gamma = ctx.extend(ContextElement::Existential(alpha_hat));
            synth_function(
                substitute_existential(&alpha, Type::Existential(alpha_hat), *ty),
                e,
                extendet_gamma,
            )
        }
        Type::Function(a, c) => {
            println!("{:>20}", "->App");
            let (typed_e, delta) = check(e, *a, ctx)?;
            Ok((typed_e, *c, delta))
        }
        _ => panic!(),
    };
    println!(
        "synthesized type as {}",
        t.as_ref().map_or("".to_string(), |a| a.0.to_string())
    );
    t
}
/// Under input context ctx, type `ty1` is a subtype of `ty2`
fn subtype(
    ty1: Type<VarId>,
    ty2: Type<VarId>,
    mut ctx: TCContext,
) -> Result<TCContext, (CheckingError, TCContext)> {
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
        (Type::Function(arg_a1, arg_a2), Type::Function(arg_b1, arg_b2)) => {
            println!("{:>20}", "<:->");
            let theta = subtype(*arg_b1, *arg_a1, ctx)?;
            let delta = subtype(
                apply_context(&theta, *arg_a2),
                apply_context(&theta, *arg_b2),
                theta,
            );
            delta
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
        (Type::Product(tup1), Type::Product(tup2)) if tup1.len() != tup2.len() => Err((
            CheckingError::MissmatchedArity(Type::Product(tup1), Type::Product(tup2)),
            ctx,
        )),
        (Type::Product(tup1), Type::Product(tup2)) => {
            println!("{:>20}", "<:Prod");
            let mut ctx = ctx;
            for i in 0..(tup1.len().min(tup2.len())) {
                ctx = subtype(tup1[i].clone(), tup2[i].clone(), ctx)?;
            }
            Ok(ctx)
        }
        (Type::Sum(tup), sum @ Type::Sum(_)) => {
            let mut duped_gamma = ctx;
            let mut errs = vec![];
            for ty in tup {
                match subtype(ty, sum.clone(), duped_gamma) {
                    Ok(ctx) => return Ok(ctx),
                    Err((e, ctx)) => {
                        duped_gamma = ctx;
                        errs.push(e);
                    }
                }
            }
            Err((CheckingError::AllOptionsFailed(errs), duped_gamma))
        }
        // If a function returns a type variable, then it is ceartainly polymorphic
        (a, Type::Quantification(name, b)) => {
            println!("{:>20}", "<:∀R");
            let extendet_gamma = ctx.mark_scope().extend(ContextElement::Variable(name));
            let delta = subtype(a, *b, extendet_gamma)?.drop_scope();
            Ok(delta)
        }
        // If a function takes a type variable, then it might be restricted by it's callers
        (Type::Quantification(name, b), a) => {
            println!("{:>20}", "<:∀L");
            let alpha_hat = ctx.fresh_existential();
            let extendet_gamma = ctx
                .mark_scope()
                .extend(ContextElement::Existential(alpha_hat));
            let delta = subtype(
                substitute_existential(&name, Type::Variable(alpha_hat), a),
                *b,
                extendet_gamma,
            )?
            .drop_scope();
            Ok(delta)
        }
        /*
        ∀a. a -> (int | (String -> int) | a) = "hello"
        */
        (a, Type::Sum(tup)) => {
            if tup.iter().any(|ty| *ty == a) {
                Ok(ctx)
            } else {
                let mut duped_gamma = ctx;
                let mut errs = vec![];
                for ty in tup {
                    match subtype(a.clone(), ty, duped_gamma) {
                        Ok(ctx) => return Ok(ctx),
                        Err((e, ctx)) => {
                            duped_gamma = ctx;
                            errs.push(e);
                        }
                    }
                }
                Err((CheckingError::AllOptionsFailed(errs), duped_gamma))
            }
        }
        (Type::Existential(alpha_hat), ty) => ctx.instantiate(alpha_hat, ty, Direction::Left),
        (ty, Type::Existential(ref alpha_hat)) => ctx.instantiate(*alpha_hat, ty, Direction::Right),
        (a, b) => Err((CheckingError::TypeMissmatch(a, b), ctx)),
    };
    t.map(|mut a| {
        println!("{} checked context {}", "-".repeat(a.unindent() + 1), a,);
        a
    })
}

/// FV(A)
fn occurs_check(alpha_hat: VarId, ty: &Type<VarId>) -> bool {
    match ty {
        Type::Unit | Type::BaseType(_) => false,
        Type::Variable(a) | Type::Existential(a) => *a == alpha_hat,
        Type::Quantification(a, ty) => *a == alpha_hat || occurs_check(alpha_hat, ty),
        Type::Function(a, b) => occurs_check(alpha_hat, a) || occurs_check(alpha_hat, b),
        Type::HigherKinded(_, generics, open) => generics
            .iter()
            .any(|ty| ty.as_ref().is_some_and(|ty| occurs_check(alpha_hat, ty))),
        Type::Product(vec) => vec.iter().any(|ty| occurs_check(alpha_hat, ty)),
        Type::Sum(vec) => vec.iter().any(|ty| occurs_check(alpha_hat, ty)),
    }
}
/// substitutes all occurances of one existential `alpha_hat` with concrete type `alpha` in `ty`
fn substitute_existential(alpha_hat: &VarId, alpha: Type<VarId>, ty: Type<VarId>) -> Type<VarId> {
    match ty {
        Type::Unit => Type::Unit,
        Type::BaseType(_) => ty,
        Type::Variable(ref var) => {
            if var == alpha_hat {
                alpha
            } else {
                ty
            }
        }
        Type::Existential(ref beta_hat) => {
            if *alpha_hat == *beta_hat {
                alpha
            } else {
                ty
            }
        }
        Type::Quantification(a, b) => {
            if *alpha_hat == a {
                Type::Quantification(a, Box::new(Type::Quantification(a, b)))
            } else {
                Type::Quantification(
                    a,
                    Box::new(substitute_existential(alpha_hat, alpha, *b.clone())),
                )
            }
        }
        Type::Function(a, b) => Type::Function(
            Box::new(substitute_existential(alpha_hat, alpha.clone(), *a)),
            Box::new(substitute_existential(alpha_hat, alpha, *b)),
        ),
        Type::HigherKinded(name, ty, open) => Type::HigherKinded(
            name,
            ty.into_iter()
                .map(|a| {
                    if let Some(ty) = a {
                        Some(substitute_existential(alpha_hat, alpha.clone(), ty))
                    } else {
                        a
                    }
                })
                .collect(),
            open,
        ),
        Type::Product(vec) => Type::Product(
            vec.into_iter()
                .map(|ty| substitute_existential(alpha_hat, alpha.clone(), ty))
                .collect(),
        ),
        Type::Sum(vec) => Type::Sum(
            vec.into_iter()
                .map(|ty| substitute_existential(alpha_hat, alpha.clone(), ty))
                .collect(),
        ),
    }
}
fn apply_context(ctx: &TCContext, ty: Type<VarId>) -> Type<VarId> {
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
        Type::Existential(alpha_hat) => ctx
            .get_solved(&alpha_hat)
            .map_or(ty, |tau| apply_context(ctx, tau.clone())),
        Type::HigherKinded(name, ty, open) => Type::HigherKinded(
            name,
            ty.into_iter()
                .map(|ty| ty.map(|ty| apply_context(ctx, ty)))
                .collect(),
            open,
        ),
        Type::Product(vec) => {
            Type::Product(vec.into_iter().map(|ty| apply_context(ctx, ty)).collect())
        }
        Type::Sum(vec) => Type::Sum(vec.into_iter().map(|ty| apply_context(ctx, ty)).collect()),
        Type::Unit => Type::Unit,
        this @ Type::BaseType(_) => this,
    }
}
fn main() {}
#[test]
fn basic() -> Result<(), CheckingError> {
    let ctx = TCContext::new();
    let (a, ty, omega) = synth(Ast::Unit, ctx).map_err(|a| a.0)?;
    assert!(omega.is_complete());
    assert_eq!(apply_context(&omega, ty), Type::Unit);
    Ok(())
}

#[test]
fn application() -> Result<(), CheckingError> {
    let ctx = TCContext::new();
    let e = Ast::Application(
        Ast::Abstraction("x".into(), Ast::Variable("x".into()).into()).into(),
        Box::new(Ast::Unit),
    );
    let (e, id) = resolve_names(e);
    let (a, ty, omega) = synth(e, ctx).map_err(|a| a.0)?;
    assert!(omega.is_complete());
    assert_eq!(Type::Unit, apply_context(&omega, ty));
    Ok(())
}

#[test]
fn lambda() -> Result<(), CheckingError> {
    let ctx = TCContext::new();
    let e = Ast::Abstraction("x".into(), Ast::Variable("x".into()).into());
    let (e, id) = resolve_names(e);
    let (a, ty, omega) = synth(e, ctx).map_err(|a| a.0)?;
    assert_eq!(
        apply_context(&omega, ty),
        Type::Function(
            Type::Existential(VarId(1)).into(),
            Type::Existential(VarId(1)).into()
        )
    );
    Ok(())
}

#[test]
fn idunit() -> Result<(), CheckingError> {
    let ctx = TCContext::new();
    let e = id_fn();
    let (e, id) = resolve_names(e);
    let (a, ty, omega) =
        synth(Ast::Application(e.into(), Ast::Unit.into()), ctx).map_err(|a| a.0)?;
    assert!(omega.is_complete());
    assert_eq!(Type::Unit, apply_context(&omega, ty));
    Ok(())
}

fn id_fn() -> Ast<String> {
    Ast::Annotation(
        Ast::Abstraction("x".into(), Ast::Variable("x".into()).into()).into(),
        Box::new(Type::Quantification(
            "A".into(),
            Type::Function(
                Type::Variable("A".into()).into(),
                Type::Variable("A".into()).into(),
            )
            .into(),
        )),
    )
}
#[test]
fn nested_to_string() -> Result<(), CheckingError> {
    let ctx = TCContext::new();
    let ctx2 = TCContext::new();
    let app = Ast::Application(
        Ast::Annotation(
            Box::new(Ast::Abstraction(
                "x".into(),
                Ast::Functor("Option".to_owned(), Ast::LitInt(3).into()).into(),
            )),
            Type::Function(
                Type::HigherKinded(None, vec![Some(Type::BaseType("Int".into()))], true).into(),
                Type::HigherKinded(
                    Some("Option".to_owned()),
                    vec![Some(Type::BaseType("Int".into()))],
                    false,
                )
                .into(),
            )
            .into(),
        )
        .into(),
        Ast::Functor("Option".into(), Ast::LitInt(23).into()).into(),
    );
    println!("{app}");
    let (e, id) = resolve_names(app);
    let (a, ty, omega) = synth(e, ctx).map_err(|a| a.0)?;
    assert!(omega.is_complete());
    assert_eq!(
        Type::HigherKinded(
            Some("Option".to_owned()),
            vec![Some(Type::BaseType("Int".into()))],
            false
        ),
        apply_context(&omega, ty)
    );
    Ok(())
}
#[test]
fn let_with_fun() -> Result<(), CheckingError> {
    let ctx = TCContext::new();
    let e = Ast::Let(
        "id".to_owned(),
        id_fn().into(),
        Ast::Application(Ast::Variable("id".to_owned()).into(), Ast::Unit.into()).into(),
    );
    let (e, id) = resolve_names(e);
    let (a, ty, omega) = synth(e, ctx).map_err(|a| a.0)?;
    assert_eq!(Type::Unit, apply_context(&omega, ty));
    Ok(())
}
#[test]
fn tuples() -> Result<(), CheckingError> {
    let ctx = TCContext::new();
    let e = Ast::Tuple(vec![
        Ast::Application(
            Ast::Annotation(
                Box::new(Ast::Abstraction(
                    "x".into(),
                    Ast::Functor("Option".to_owned(), Ast::LitInt(48).into()).into(),
                )),
                Type::Function(
                    Type::HigherKinded(None, vec![Some(Type::BaseType("Int".into()))], true).into(),
                    Type::HigherKinded(
                        Some("Option".to_owned()),
                        vec![Some(Type::BaseType("Int".into()))],
                        false,
                    )
                    .into(),
                )
                .into(),
            )
            .into(),
            Ast::Functor("Option".into(), Ast::LitInt(23).into()).into(),
        ),
        Ast::Let(
            "id".to_owned(),
            id_fn().into(),
            Ast::Application(Ast::Variable("id".to_owned()).into(), Ast::Unit.into()).into(),
        ),
    ]);
    let (e, names) = resolve_names(e);
    let (a, ty, omega) = synth(e, ctx).map_err(|a| a.0)?;
    assert_eq!(
        Type::Product(vec![
            Type::HigherKinded(
                Some("Option".to_owned()),
                vec![Some(Type::BaseType("Int".into()))],
                false
            ),
            Type::Unit
        ]),
        apply_context(&omega, ty)
    );
    panic!();
    Ok(())
}
