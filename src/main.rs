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
    /// Named Type
    Constructor(String),
}
impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::Unit => write!(f, "()"),
            Self::Variable(var) => write!(f, "{var}"),
            Self::Existential(ex) => write!(f, "'{ex}"),
            Self::Quantification(a, ty) => write!(f, "(∀{a}. {ty})"),
            Self::Function(a, c) => write!(f, "({a} -> {c})"),
            Type::Constructor(id) => write!(f, "{id}"),
        }
    }
}
impl Type {
    fn is_monotype(&self) -> bool {
        match self {
            Type::Quantification(_, _) => false,
            Type::Function(a, b) => a.is_monotype() && b.is_monotype(),
            _ => true,
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
}

impl fmt::Display for ContextElement {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::Variable(var) => write!(f, "{}", var),
            Self::Existential(ex) => write!(f, "'{}", ex),
            Self::Solved(a, ty) => write!(f, "'{}: {}", a, ty),
            Self::TypedVariable(x, ty) => write!(f, "{}: {}", x, ty),
        }
    }
}

/// As the context needs to be ordered, it is implemented as a simple Vector.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Context {
    elements: Vec<ContextElement>,
    existentials: usize,
    markers: Vec<usize>,
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
struct Existential(usize);
impl Context {
    fn fresh_existential(&mut self) -> String {
        let result = format!("t{}", self.existentials);
        self.existentials += 1;
        result
    }
    const fn new() -> Self {
        Self {
            elements: vec![],
            existentials: 0,
            markers: vec![],
        }
    }
    fn mark(mut self) -> Self {
        self.markers.push(self.elements.len());
        self
    }
    fn drop_mark(mut self) -> Self {
        let x = self
            .markers
            .pop()
            .expect("Called drop_mark without having called mark");
        self.elements.drain(x..);
        self
    }
    /// Γ -> Γ,α
    fn extend(&self, alpha: ContextElement) -> Self {
        let mut elements = self.elements.clone();
        elements.push(alpha);
        Self {
            elements,
            ..self.clone()
        }
    }
    /// Γ,α -> Γ
    fn drop(&self, alpha: ContextElement) -> Self {
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
    /// Γ = Γ0[^β] -> (^α, ^β, x : ^β)
    fn split_at(&self, beta_hat: &ContextElement) -> (Self, Self) {
        let pos = self
            .elements
            .iter()
            .position(|elem| elem == beta_hat)
            .unwrap_or_else(|| panic!("Could not find {} in context to split", beta_hat));
        let (alpha_hat, rest) = self.elements.split_at(pos);
        (
            Self {
                elements: alpha_hat.to_vec(),
                ..self.clone()
            },
            Self {
                elements: rest.to_vec(),
                ..self.clone()
            },
        )
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
        println!("looking for {alpha_hat} in {self}");
        for elem in &self.elements {
            if let ContextElement::TypedVariable(a, b) = elem {
                if alpha_hat == a {
                    return Some(b);
                }
            }
        }
        None
    }
    /// Γ == ∆, α
    fn has_variable(&self, alpha: &str) -> bool {
        self.elements
            .iter()
            .any(|elem| elem == &ContextElement::Variable(alpha.to_string()))
    }
    /// Γ == ∆, ^α
    fn has_existential(&self, alpha_hat: &str) -> bool {
        self.elements
            .iter()
            .any(|elem| elem == &ContextElement::Existential(alpha_hat.to_string()))
    }
    fn is_well_typed(&self) -> bool {
        if self.elements.is_empty() {
            return true;
        }
        self.elements.iter().fold(true, |acc, elem| {
            if let ContextElement::Solved(alpha, ty) = elem {
                acc && is_well_formed(self, &ty) && !self.has_variable(alpha)
            } else {
                false
            }
        })
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
/// instantiate ^α to a subtype of A
fn instantiate(alpha_hat: String, ty: &Type, mut ctx: Context, dir: Direction) -> Context {
    println!("instantiate {alpha_hat} to a subtype of {ty} under Context {ctx}");
    let mut alpha = ContextElement::Existential(alpha_hat.clone());
    let (l, r) = ctx.split_at(&alpha);
    if ty.is_monotype() && is_well_formed(&l, ty) {
        print_rule("InstLSolve");
        return ctx.insert_at(&alpha, vec![ContextElement::Solved(alpha_hat, ty.clone())]);
    }
    match (ty, dir) {
        (Type::Existential(beta), _) => {
            print_rule("InstLReach");
            assert!(is_well_formed(&r, ty));
            ctx.insert_at(&ContextElement::Existential(beta.to_string()), vec![
                ContextElement::Solved(beta.to_string(), (Type::Existential(alpha_hat))),
            ])
        }
        (Type::Quantification(beta, ty), Direction::Left) => {
            print_rule("InstLAllR");
            let beta_hat = ctx.fresh_existential();
            let mut extended_gamma = ctx.extend(ContextElement::Existential(beta_hat));
            let delta_prime = instantiate(alpha_hat, ty, extended_gamma, Direction::Left);
            let delta = delta_prime.drop(ContextElement::Existential(beta.to_string()));
            return delta;
        }
        (Type::Quantification(beta, ty), Direction::Right) => {
            print_rule("InstRAllL");
            let beta_hat = ctx.fresh_existential();
            let mut extended_gamma = ctx
                .mark()
                .extend(ContextElement::Existential(beta_hat.clone()));
            let delta_prime = instantiate(
                alpha_hat,
                &substitute_existential(&beta_hat, &Type::Variable(beta.to_string()), ty),
                extended_gamma,
                Direction::Right,
            );
            let delta = delta_prime.drop_mark();
            return delta;
        }
        (Type::Function(a, b), dir) => {
            print_rule("InstLArr");
            let alpha_hat1 = ctx.fresh_existential();
            let alpha_hat2 = ctx.fresh_existential();
            let mut extended_gamma = ctx
                .extend(ContextElement::Existential(alpha_hat1.clone()))
                .extend(ContextElement::Existential(alpha_hat2.clone()))
                .extend(ContextElement::Solved(
                    alpha_hat,
                    Type::Function(
                        Box::new({
                            let name = alpha_hat1.clone();
                            Type::Existential(name)
                        }),
                        Box::new({
                            let name = alpha_hat2.clone();
                            Type::Existential(name)
                        }),
                    ),
                ));
            let mut theta = instantiate(alpha_hat1, a, extended_gamma, dir.flip());
            let delta = instantiate(alpha_hat2, &apply_context(&theta, *b.clone()), theta, dir);
            return delta;
        }
        (t, dir) => panic!(
            "Failed to handle {t} in direction {dir:?}, either is_well_formed has a problem or i need to handle more cases"
        ),
    }
}
fn check(e: Term, ty: Type, ctx: Context) -> Context {
    println!("checking that {e} has type {ty} under context {ctx}");
    match (e, ty) {
        (Term::Unit, Type::Unit) => {
            print_rule("1I");
            ctx
        }
        (e, Type::Quantification(name, ty)) => {
            print_rule("∀I");
            let mut extendet_gamma = ctx.extend(ContextElement::Variable(name.clone()));
            check(e, *ty, extendet_gamma).drop(ContextElement::Variable(name))
        }
        (Term::Abstraction(alpha, term), Type::Function(a, b)) => {
            print_rule("->I");
            let typed = ContextElement::TypedVariable(alpha, *a);
            let mut extended_gamma = ctx.extend(typed.clone());
            check(*term, *b, extended_gamma).drop(typed)
        }
        (e, ty) => {
            print_rule("Sub");
            let (a, mut theta) = synth(e, ctx);
            subtype(&apply_context(&theta, a), &apply_context(&theta, ty), theta)
        }
    }
}
fn synth(e: Term, mut ctx: Context) -> (Type, Context) {
    println!("synthesizing Type for {e} under context {ctx}");
    match e {
        Term::Variable(name) => {
            print_rule("Var");
            (
                ctx.get_annotation(&name)
                    .unwrap_or_else(|| panic!("variable {name} not sufficiently annotated"))
                    .clone(),
                ctx,
            )
        }
        Term::Unit => {
            print_rule("1I=>");
            (Type::Unit, ctx.clone())
        }
        Term::Abstraction(x, e) => {
            print_rule("->I=>");
            let alpha = ctx.fresh_existential();
            let beta = ctx.fresh_existential();
            let typed = ContextElement::TypedVariable(x.clone(), {
                let name = alpha.clone();
                Type::Existential(name)
            });
            let mut extended_gamma = ctx
                .extend(ContextElement::Existential(alpha.clone()))
                .extend(ContextElement::Existential(beta.clone()))
                .extend(typed.clone());
            (
                Type::Function(
                    Box::new(Type::Existential(alpha)),
                    Box::new({
                        let name = beta.clone();
                        Type::Existential(name)
                    }),
                ),
                check(*e, Type::Existential(beta), extended_gamma).drop(typed.clone()),
            )
        }
        Term::Annotation(term, ty) => {
            print_rule("Anno");
            (*ty.clone(), check(*term, *ty, ctx))
        }
        Term::Application(e, e2) => {
            print_rule("->E");
            let (a, mut theta) = synth(*e, ctx);
            synth_function(&apply_context(&theta, a), *e2, theta)
        }
    }
}
fn synth_function(a: &Type, e: Term, mut ctx: Context) -> (Type, Context) {
    println!("synthesizing type if {a} is applied to {e} under Context {ctx}");
    match a {
        Type::Existential(alpha_hat) => {
            print_rule("α^App");
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
            (
                Type::Existential(alpha_hat2),
                check(e, Type::Existential(alpha_hat1), ctx),
            )
        }
        Type::Quantification(alpha, ty) => {
            print_rule("∀App");
            let alpha_hat = ctx.fresh_existential();
            let mut extendet_gamma = ctx.extend(ContextElement::Existential(alpha_hat.clone()));
            synth_function(
                &substitute_existential(alpha, &Type::Existential(alpha_hat.to_string()), ty),
                e,
                extendet_gamma,
            )
        }
        Type::Function(a, c) => {
            print_rule("->App");
            (*a.clone(), check(e, *a.clone(), ctx))
        }
        _ => panic!(),
    }
}
/// Under input context ctx, type A is a subtype of B
fn subtype(ty: &Type, ty2: &Type, mut ctx: Context) -> Context {
    println!("have {ty} be a subtype of {ty2} under Context {ctx}");
    match (ty, ty2) {
        (Type::Unit, Type::Unit) => ctx.clone(),
        (Type::Constructor(name), Type::Constructor(name2)) if name == name2 => ctx.clone(),
        (Type::Variable(alpha1), Type::Variable(alpha2)) => {
            if is_well_formed(&ctx, ty) {
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
            if is_well_formed(&ctx, ty) {
                ctx.clone()
            } else {
                panic!("{alpha_hat2} is not well formed")
            }
        }
        (Type::Function(arg_a1, arg_a2), Type::Function(arg_b1, arg_b2)) => {
            let mut theta = subtype(arg_a1, arg_b1, ctx);
            subtype(
                &apply_context(&theta, *arg_a1.clone()),
                &apply_context(&theta, *arg_b2.clone()),
                theta,
            )
        }
        (a, Type::Quantification(name, b)) => {
            let mut theta = ctx.extend(ContextElement::Variable(name.to_string()));
            let delta = subtype(a, b, theta);
            delta.drop(ContextElement::Variable(name.to_string()))
        }
        (Type::Quantification(name, b), a) => {
            let alpha_hat = ctx.fresh_existential();
            let mut theta = ctx
                .mark()
                .extend(ContextElement::Existential(alpha_hat.clone()));
            let delta = subtype(
                &substitute_existential(name, &Type::Variable(alpha_hat), a),
                b,
                theta,
            );
            delta.drop_mark()
        }
        (Type::Existential(alpha_hat), ty) => {
            instantiate(alpha_hat.to_string(), ty, ctx, Direction::Left)
        }
        (ty, Type::Existential(alpha_hat)) => {
            instantiate(alpha_hat.to_string(), ty, ctx, Direction::Right)
        }
        (a, b) => panic!("Cannnot subtype {a} with {b}"),
        (Type::Unit, _) => todo!(),
        (Type::Constructor(_), _) => todo!(),
        (Type::Variable(_), _) => todo!(),
        (Type::Function(_, _), _) => todo!(),
    }
}

/// FV(A)
fn occurs_check(alpha_hat: &String, ty: &Type) -> bool {
    match ty {
        Type::Unit | Type::Constructor(_) => false,
        Type::Variable(a) | Type::Existential(a) => a == alpha_hat,
        Type::Quantification(a, ty) => a == alpha_hat || occurs_check(alpha_hat, ty),
        Type::Function(a, b) => occurs_check(alpha_hat, a) || occurs_check(alpha_hat, b),
    }
}
fn substitute_existential(alpha_hat: &String, alpha: &Type, ty: &Type) -> Type {
    let ty = match ty {
        Type::Unit => Type::Unit,
        Type::Constructor(_) => ty.clone(),
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
    };
    println!("result: {ty}");
    ty
}
fn is_well_formed(ctx: &Context, ty: &Type) -> bool {
    match ty {
        Type::Unit | Type::Constructor(_) => true,
        Type::Variable(var) => ctx.has_variable(var),
        Type::Existential(alpha_hat) => {
            ctx.has_existential(alpha_hat) || ctx.get_solved(alpha_hat).is_some()
        }
        Type::Quantification(alpha_hat, ty) => is_well_formed(
            &ctx.extend(ContextElement::Existential(alpha_hat.to_string())),
            ty,
        ),
        Type::Function(a, b) => is_well_formed(ctx, a) && is_well_formed(ctx, b),
    }
}
fn apply_context(ctx: &Context, ty: Type) -> Type {
    match ty {
        /// [Γ]1 = 1
        unit @ (Type::Unit | Type::Constructor(_)) => unit,
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
        Type::Existential(ref lpha_hat) => ctx
            .get_solved(lpha_hat)
            .map_or(ty, |tau| apply_context(ctx, tau.clone())),
    }
}
fn print_rule(rule: &str) {
    println!("{:>20}", rule);
}
fn main() {}
#[test]
fn basic() {
    let mut ctx = Context::new();
    let (ty, ctx) = synth(Term::Unit, ctx);
    assert_eq!(apply_context(&ctx, ty), Type::Unit);
}

#[test]
fn application() {
    let mut ctx = Context::new();
    let (ty, omega) = synth(
        Term::Application(
            Term::Abstraction("x".into(), Term::Variable("x".into()).into()).into(),
            Box::new(Term::Unit),
        ),
        ctx,
    );
    assert_eq!(Type::Unit, apply_context(&omega, ty));
}

#[test]
fn lambda() {
    let mut ctx = Context::new();
    let (ty, omega) = synth(
        Term::Abstraction("x".into(), Term::Variable("x".into()).into()),
        ctx,
    );
    assert_eq!(
        apply_context(&omega, ty),
        Type::Function(
            Type::Existential("t0".into()).into(),
            Type::Existential("t0".into()).into()
        )
    );
}

#[test]
fn idunit() {
    let mut ctx = Context::new();
    let (ty, omega) = synth(Term::Application(id_fn().into(), Term::Unit.into()), ctx);
    assert_eq!(Type::Unit, apply_context(&omega, ty))
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
