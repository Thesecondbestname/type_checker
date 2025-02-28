#![allow(unused)]
#![allow(clippy::uninlined_format_args)]
use core::fmt;
use std::mem;

enum Term {
    Variable(String),
    Unit,
    Abstraction(String, Box<Term>),
    Application(Box<Term>, Box<Term>),
    Annotation(Box<Term>, Box<Type>),
}
impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::Unit => write!(f, "()"),
            Self::Variable(var) => write!(f, "{}", var),
            Self::Abstraction(alpha, e) => write!(f, "(\\{} -> {})", alpha, e),
            Self::Application(e1, e2) => write!(f, "{} {}", e1, e2),
            Self::Annotation(e, a) => write!(f, "({}: {})", e, a),
        }
    }
}
/// 1 | α | ^α | ∀α. A | A → B
#[derive(PartialEq, Debug, Clone, Eq)]
enum Type {
    /// 1
    Unit,
    /// α
    Variable(String),
    /// ^α MAYBE SOLVED!!
    Existential(String),
    /// ∀α. A
    Quantification(String, Box<Type>),
    /// A → B
    Function(Box<Type>, Box<Type>),
}
impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::Unit => write!(f, "()"),
            Self::Variable(var) => write!(f, "{var}"),
            Self::Existential(ex) => write!(f, "'{ex}"),
            Self::Quantification(a, ty) => write!(f, "(∀{a}. {ty})"),
            Self::Function(a, c) => write!(f, "({a} -> {c})"),
        }
    }
}
impl Type {
    fn is_monotype(&self) -> bool {
        match self {
            Type::Unit => true,
            Type::Variable(_) => true,
            Type::Existential(_) => true,
            Type::Quantification(_, _) => false,
            Type::Function(a, b) => a.is_monotype() && b.is_monotype(),
        }
    }
}
/// Θ ::= · | Γ, α | Γ, x : A | Γ, ^α | Γ, ^α = τ | Γ, I^
#[derive(PartialEq, Debug, Clone, Eq)]
enum ContextElement {
    /// Γ, α
    Variable(String),
    /// Γ, x : A
    TypedVariable(String, Type),
    /// Γ, ^α
    Existential(String),
    /// Γ, ^α = τ
    Solved(String, Type),
    /// Γ, I^α
    Marker(String),
}

impl fmt::Display for ContextElement {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::Variable(var) => write!(f, "{}", var),
            Self::Existential(ex) => write!(f, "'{}", ex),
            Self::Solved(a, ty) => write!(f, "'{}: {}", a, ty),
            Self::Marker(a) => write!(f, "<|{}", a),
            Self::TypedVariable(x, ty) => write!(f, "{}: {}", x, ty),
        }
    }
}

/// As the context needs to be ordered, it is implemented as a simple Vector.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Context {
    elements: Vec<ContextElement>,
}

impl fmt::Display for Context {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "[").unwrap();
        let _ = self.elements.iter().fold(true, |first, ele| {
            if !first {
                write!(f, ", ").unwrap();
            }
            write!(f, "{}", ele).unwrap();
            false
        });
        write!(f, "]")
    }
}
struct State(usize);
impl State {
    const fn new() -> Self {
        Self(0)
    }
    fn fresh_existential(&mut self) -> String {
        let result = format!("t{}", self.0);
        self.0 += 1;
        result
    }
}
impl Context {
    const fn new() -> Self {
        Self { elements: vec![] }
    }
    /// Γ -> Γ,α
    fn extend(&self, α: ContextElement) -> Self {
        let mut elements = self.elements.clone();
        elements.push(α);
        Self { elements }
    }
    /// Γ,α -> Γ
    fn drop(&self, α: ContextElement) -> Self {
        let pos = self
            .elements
            .iter()
            .position(|elem| elem == &α)
            .unwrap_or_else(|| panic!("Could not find {} in context to drop", α));
        let mut elements = self.elements.clone();
        let rest = elements.split_off(pos);
        Self { elements }
    }
    /// Γ = Γ0[^β] -> (^α, ^β, x : ^β)
    fn split_at(&self, β_hat: &ContextElement) -> (Self, Self) {
        let pos = self
            .elements
            .iter()
            .position(|elem| elem == β_hat)
            .unwrap_or_else(|| panic!("Could not find {} in context to split", β_hat));
        let (α_hat, rest) = self.elements.split_at(pos);
        (
            Self {
                elements: α_hat.to_vec(),
            },
            Self {
                elements: rest.to_vec(),
            },
        )
    }
    /// Γ, α, Γ' ->  Γ, β, Γ'
    fn insert_at(&self, α: &ContextElement, β: Vec<ContextElement>) -> Self {
        let pos = self
            .elements
            .iter()
            .position(|elem| elem == α)
            .unwrap_or_else(|| panic!("Could not find {} in context to replace", α));
        let mut elements = self.elements.clone();
        elements.splice(pos..=pos, β);
        Self { elements }
    }
    /// Γ -> Γ [^α = τ]
    fn get_solved(&self, α_hat: &str) -> Option<&Type> {
        for elem in &self.elements {
            if let ContextElement::Solved(a, b) = elem {
                if α_hat == a {
                    return Some(b);
                }
            }
        }
        None
    }
    /// Γ == ∆, α
    fn has_variable(&self, α: &str) -> bool {
        self.elements
            .iter()
            .any(|elem| elem == &ContextElement::Variable(α.to_string()))
    }
    /// Γ == ∆, ^α
    fn has_existential(&self, α_hat: &str) -> bool {
        self.elements
            .iter()
            .any(|elem| elem == &ContextElement::Existential(α_hat.to_string()))
    }
    fn is_well_typed(&self) -> bool {
        if self.elements.is_empty() {
            return true;
        }
        self.elements.iter().fold(true, |acc, elem| {
            if let ContextElement::Solved(α, ty) = elem {
                acc && is_well_formed(self, ty) && !self.has_variable(α)
            } else {
                false
            }
        })
    }
}
/// instantiate ^α to a supertype of A
fn instantiate_r(state: &mut State, ctx: &Context, α_hat: String, ty: &Type) -> Context {
    let mut α = ContextElement::Existential(α_hat.clone());
    let (l, r) = ctx.split_at(&α);
    if ty.is_monotype() && is_well_formed(&l, ty) {
        return ctx.insert_at(&α, vec![ContextElement::Solved(α_hat, ty.clone())]);
    }
    match ty {
        Type::Existential(beta) => {
            assert!(is_well_formed(&r, ty));
            ctx.insert_at(&ContextElement::Existential(beta.to_string()), vec![
                ContextElement::Solved(α_hat, ty.clone()),
            ])
        }
        Type::Quantification(beta, ty) => {
            let beta_hat = state.fresh_existential();
            let extended_gamma = ctx
                .extend(ContextElement::Marker(beta.to_string()))
                .extend(ContextElement::Existential(beta_hat.clone()));
            let delta_prime = instantiate_r(
                state,
                &extended_gamma,
                α_hat,
                &substitute_existential(&beta_hat, &Type::Variable(beta.to_string()), ty),
            );
            let delta = delta_prime.drop(ContextElement::Marker(beta.to_string()));
            return delta;
        }
        Type::Function(a, b) => {
            let α_hat1 = state.fresh_existential();
            let α_hat2 = state.fresh_existential();
            let extended_gamma = ctx
                .extend(ContextElement::Existential(α_hat1.clone()))
                .extend(ContextElement::Existential(α_hat2.clone()))
                .extend(ContextElement::Solved(
                    α_hat,
                    Type::Function(
                        Box::new(Type::Existential(α_hat1.clone())),
                        Box::new(Type::Existential(α_hat2.clone())),
                    ),
                ));
            let theta = instantiate_l(state, &extended_gamma, α_hat1, a);
            let delta = instantiate_r(state, &theta, α_hat2, &apply_context(&theta, *b.clone()));
            return delta;
        }
        t => panic!(
            "Failed to handle {t}, either is_well_formed has a problem or i need to handle more cases"
        ),
    }
}
/// instantiate ^α to a subtype of A
fn instantiate_l(state: &mut State, ctx: &Context, α_hat: String, ty: &Type) -> Context {
    let mut α = ContextElement::Existential(α_hat.clone());
    let (l, r) = ctx.split_at(&α);
    if ty.is_monotype() && is_well_formed(&l, ty) {
        return ctx.insert_at(&α, vec![ContextElement::Solved(α_hat, ty.clone())]);
    }
    match ty {
        Type::Existential(beta) => {
            assert!(is_well_formed(&r, ty));
            ctx.insert_at(&ContextElement::Existential(beta.to_string()), vec![
                ContextElement::Solved(α_hat, ty.clone()),
            ])
        }
        Type::Quantification(beta, ty) => {
            let beta_hat = state.fresh_existential();
            let extended_gamma = ctx.extend(ContextElement::Existential(beta_hat));
            let delta_prime = instantiate_l(state, &extended_gamma, α_hat, ty);
            let delta = delta_prime.drop(ContextElement::Existential(beta.to_string()));
            return delta;
        }
        Type::Function(a, b) => {
            let α_hat1 = state.fresh_existential();
            let α_hat2 = state.fresh_existential();
            let extended_gamma = ctx
                .extend(ContextElement::Existential(α_hat1.clone()))
                .extend(ContextElement::Existential(α_hat2.clone()))
                .extend(ContextElement::Solved(
                    α_hat,
                    Type::Function(
                        Box::new(Type::Existential(α_hat1.clone())),
                        Box::new(Type::Existential(α_hat2.clone())),
                    ),
                ));
            let theta = instantiate_r(state, &extended_gamma, α_hat1, a);
            let delta = instantiate_l(state, &theta, α_hat2, &apply_context(&theta, *b.clone()));
            return delta;
        }
        t => panic!(
            "Failed to handle {t}, either is_well_formed has a problem or i need to handle more cases"
        ),
    }
}
fn check(state: &mut State, ctx: &Context, e: Term, ty: Type) -> Context {
    match (e, ty) {
        (Term::Unit, Type::Unit) => ctx.clone(),
        (e, Type::Quantification(name, ty)) => {
            let extendet_gamma = ctx.extend(ContextElement::Existential(name.clone()));
            check(state, &extendet_gamma, e, *ty).drop(ContextElement::Existential(name))
        }
        (Term::Abstraction(alpha, term), Type::Function(a, b)) => {
            let solved = ContextElement::Solved(alpha.clone(), *a);
            let extended_gamma = ctx.extend(solved.clone());
            check(state, &extended_gamma, *term, *b).drop(solved)
        }
        (e, ty) => {
            let (a, theta) = synth(state, ctx, e);
            subtype(
                state,
                &theta,
                &apply_context(&theta, a),
                &apply_context(&theta, ty),
            )
        }
    }
}
fn synth(state: &mut State, ctx: &Context, e: Term) -> (Type, Context) {
    match e {
        Term::Variable(name) => (
            ctx.get_solved(&name)
                .expect("variable {name} not sufficiently annotated")
                .clone(),
            ctx.clone(),
        ),
        Term::Unit => (Type::Unit, ctx.clone()),
        Term::Abstraction(x, e) => {
            let alpha = state.fresh_existential();
            let beta = state.fresh_existential();
            let solved = ContextElement::Solved(alpha.clone(), Type::Existential(x));
            let extended_gamma = ctx
                .extend(ContextElement::Existential(alpha.clone()))
                .extend(ContextElement::Existential(alpha.clone()))
                .extend(solved.clone());
            (
                Type::Function(
                    Box::new(Type::Existential(alpha)),
                    Box::new(Type::Existential(beta.clone())),
                ),
                check(state, &extended_gamma, *e, Type::Existential(beta)).drop(solved.clone()),
            )
        }
        Term::Annotation(term, ty) => (*ty.clone(), check(state, ctx, *term, *ty)),
        Term::Application(term, term1) => {
            let (a, theta) = synth(state, ctx, *term);
            synth_function(state, &theta, &apply_context(&theta, a), *term1)
        }
    }
}
fn synth_function(state: &mut State, ctx: &Context, a: &Type, e: Term) -> (Type, Context) {
    match a {
        Type::Existential(_) => todo!(),
        Type::Unit => todo!(),
        Type::Variable(_) => todo!(),
        Type::Quantification(alpha, ty) => {
            let alpha_hat = state.fresh_existential();
            let extendet_gamma = ctx.extend(ContextElement::Existential(alpha_hat.clone()));
            synth_function(
                state,
                &extendet_gamma,
                &substitute_existential(&alpha_hat, &Type::Variable(alpha.to_string()), ty),
                e,
            )
        }
        Type::Function(a, c) => (*a.clone(), check(state, ctx, e, *a.clone())),
    }
}
/// Under input context ctx, type A is a subtype of B
fn subtype(state: &mut State, ctx: &Context, ty: &Type, ty2: &Type) -> Context {
    match (ty, ty2) {
        (Type::Unit, Type::Unit) => ctx.clone(),
        (Type::Variable(α), Type::Variable(a)) => {
            if α == a {
                if is_well_formed(ctx, ty) {
                    ctx.clone()
                } else {
                    panic!("{a} is not well typed")
                }
            } else {
                panic!("Variables don't match in subtyping")
            }
        }
        (Type::Existential(α_hat), Type::Existential(a_hat)) => {
            if α_hat == a_hat {
                if is_well_formed(ctx, ty) {
                    ctx.clone()
                } else {
                    panic!("{a_hat} is not well typed")
                }
            } else {
                panic!("Variables don't match in subtyping")
            }
        }
        (Type::Function(arg_a1, arg_b1), Type::Function(arg_a2, arg_b2)) => {
            let theta = subtype(state, ctx, arg_a1, arg_a2);
            subtype(
                state,
                &theta,
                &apply_context(&theta, *arg_b1.clone()),
                &apply_context(&theta, *arg_b2.clone()),
            )
        }
        (a, Type::Quantification(name, b)) => {
            let theta = ctx.extend(ContextElement::Variable(name.to_string()));
            let delta = subtype(state, &theta, a, b);
            delta.drop(ContextElement::Variable(name.to_string()))
        }
        (Type::Quantification(name, b), a) => {
            let a_hat = state.fresh_existential();
            let theta = ctx
                .extend(ContextElement::Marker(name.to_string()))
                .extend(ContextElement::Existential(a_hat.clone()));
            let delta = subtype(
                state,
                &theta,
                &substitute_existential(name, &Type::Variable(a_hat), a),
                b,
            );
            delta.drop(ContextElement::Variable(name.to_string()))
        }
        (Type::Existential(a_hat), ty) => todo!(),
        (ty, Type::Existential(_)) => todo!(),
        (a, b) => panic!("Cannnot subtype {a} with {b}"),
    }
}

/// FV(A)
fn occurs_check(α_hat: &String, ty: &Type) -> bool {
    match ty {
        Type::Unit => false,
        Type::Variable(a) | Type::Existential(a) => a == α_hat,
        Type::Quantification(a, ty) => a == α_hat || occurs_check(α_hat, ty),
        Type::Function(a, b) => occurs_check(α_hat, a) || occurs_check(α_hat, b),
    }
}
fn substitute_existential(α_hat: &String, α: &Type, ty: &Type) -> Type {
    match ty {
        Type::Unit => Type::Unit,
        Type::Variable(var) => {
            if α_hat == var {
                α.clone()
            } else {
                ty.clone()
            }
        }
        Type::Existential(β_hat) => {
            if α_hat == β_hat {
                α.clone()
            } else {
                ty.clone()
            }
        }
        Type::Quantification(a, b) => {
            Type::Quantification(a.to_string(), Box::new(substitute_existential(α_hat, α, b)))
        }
        Type::Function(a, b) => Type::Function(
            Box::new(substitute_existential(α_hat, α, a)),
            Box::new(substitute_existential(α_hat, α, b)),
        ),
    }
}
fn is_well_formed(ctx: &Context, ty: &Type) -> bool {
    match ty {
        Type::Unit => true,
        Type::Variable(var) => ctx.has_variable(var),
        Type::Existential(α_hat) => ctx.has_existential(α_hat) || ctx.get_solved(α_hat).is_some(),
        Type::Quantification(α_hat, ty) => is_well_formed(
            &ctx.extend(ContextElement::Existential(α_hat.to_string())),
            ty,
        ),
        Type::Function(a, b) => is_well_formed(ctx, a) && is_well_formed(ctx, b),
    }
}
fn apply_context(ctx: &Context, ty: Type) -> Type {
    match ty {
        /// [Γ]1 = 1
        unit @ Type::Unit => unit,
        /// [Γ]α = α
        α @ Type::Variable(_) => α,
        /// [Γ](∀α. A) = ∀α. [Γ]A
        Type::Quantification(n, α) => Type::Quantification(n, Box::new(apply_context(ctx, *α))),
        /// [Γ](A → B) = ([Γ]A) → ([Γ]B)
        Type::Function(a, b) => Type::Function(
            Box::new(apply_context(ctx, *a)),
            Box::new(apply_context(ctx, *b)),
        ),
        /// [Γ[`α_hat``α_hat`at = `α_hat`        
        /// [Γ[`α_hat` = τ`α_hat` = `α_hat`= τ]]τ
        Type::Existential(ref α_hat) => ctx
            .get_solved(α_hat)
            .map_or(ty, |tau| apply_context(ctx, tau.clone())),
    }
}
fn main() {}

#[test]
fn test_substitute() {
    let unit = Type::Unit;
    let t1 = "t1".to_string();
    let t2 = "t2".to_string();
    let replace = Type::Function(
        Box::new(Type::Existential(t1.clone())),
        Box::new(Type::Quantification(
            "t3".to_owned(),
            Box::new(Type::Function(
                Box::new(Type::Existential(t1.clone())),
                Box::new(Type::Existential("t3".to_owned())),
            )),
        )),
    );
    let res = Type::Function(
        Box::new(unit.clone()),
        Box::new(Type::Quantification(
            "t3".to_owned(),
            Box::new(Type::Function(
                Box::new(unit.clone()),
                Box::new(Type::Existential("t3".to_owned())),
            )),
        )),
    );
    println!("{}", substitute_existential(&t1, &unit, &replace));
    assert_eq!(substitute_existential(&t1, &unit, &replace), res);
}
