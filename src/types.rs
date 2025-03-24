use core::{fmt, panic};
use std::{
    any::TypeId,
    fmt::Write,
    mem::{self, transmute},
};

use crate::{TyId, VarId};

pub(crate) enum Ast<Var> {
    Variable(Var),
    Unit,
    Abstraction(Var, Box<Self>),
    Application(Box<Self>, Box<Self>),
    Annotation(Box<Self>, Box<Type<Var>>),
    Functor(String, Box<Self>),
    Let(Var, Box<Self>, Box<Self>),
    Tuple(Vec<Self>),
    LitInt(usize),
}
pub struct TypedVar(pub VarId, pub Type<VarId>);
/// 1 | α | ^α | ∀α. A | A →  B | (A, B) | (A | B) | F[α]
#[derive(PartialEq, Debug, Clone, Eq)]
pub(crate) enum Type<Var> {
    /// 1
    Unit,
    /// α
    Variable(Var),
    /// ^α MAYBE SOLVED!!
    Existential(Var),
    /// ∀α. A
    Quantification(Var, Box<Self>),
    /// A →  B
    Function(Box<Self>, Box<Self>),
    /// Tuple (A,B,C)
    Product(Vec<Self>),
    /// Enum Tuple (A + B + C)
    Sum(Vec<Self>),
    /// Named Type
    BaseType(String),
    /// Option[T, ..], F[_]
    HigherKinded(Option<String>, Vec<Option<Self>>, bool),
}
/// Θ ::= · | Γ, α | Γ, x : A | Γ, ^α | Γ, ^α = τ | Γ, I^
#[derive(PartialEq, Debug, Clone, Eq)]
pub(crate) enum ContextElement {
    /// Γ, α
    Variable(VarId),
    /// Γ, x : A
    TypedVariable(VarId, Type<VarId>),
    /// Γ, ^α
    Existential(VarId),
    /// Γ, ^α = τ
    Solved(VarId, Type<VarId>),
}
/// As the context needs to be ordered, it is implemented as a simple Vector.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Context {
    pub elements: Vec<ContextElement>,
    pub existentials: usize,
    pub markers: Vec<usize>,
    pub ident_level: usize,
}

struct Existential(usize);
#[derive(Debug)]
pub(crate) enum CheckingError {
    UnannotatedVariable(VarId),
    DoubelyInitializedVariable(VarId),
    // Expected, found
    TypeMissmatch(Type<VarId>, Type<VarId>),
    AllOptionsFailed(Vec<Self>),
    InvalidInstantiation(Type<VarId>, String),
    NotWellFormed(Type<VarId>),
    MissmatchedArity(Type<VarId>, Type<VarId>),
    KindMissmatch(Type<VarId>, Type<VarId>),
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
impl fmt::Display for ContextElement {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            ContextElement::Variable(var) => write!(f, "{}", var),
            ContextElement::Existential(ex) => write!(f, "'{}", ex),
            ContextElement::Solved(a, ty) => write!(f, "'{}: {}", a, ty),
            ContextElement::TypedVariable(x, ty) => write!(f, "{}: {}", x, ty),
        }
    }
}

impl<T: std::fmt::Display> fmt::Display for Ast<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Ast::Unit => write!(f, "()"),
            Ast::Variable(var) => write!(f, "{}", var),
            Ast::Abstraction(alpha, e) => write!(f, "(\\{} -> {})", alpha, e),
            Ast::Application(e1, e2) => write!(f, "{} {}", e1, e2),
            Ast::Annotation(e, a) => write!(f, "({}: {})", e, a),
            Ast::LitInt(i) => write!(f, "{i}"),
            Ast::Functor(name, term) => write!(f, "{name}::new({term})"),
            Ast::Let(name, term, term1) => write!(f, "let {name} = {term} in {term1}"),
            Ast::Tuple(vec) => write!(
                f,
                "({})",
                vec.iter()
                    .map(|a| a.to_string())
                    .collect::<Vec<_>>()
                    .join(",")
            ),
        }
    }
}
impl fmt::Display for TypedVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({}: {})", self.0, self.1)
    }
}
impl fmt::Display for VarId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
impl fmt::Display for TyId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
impl<T: fmt::Display> fmt::Display for Type<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Type::Unit => write!(f, "()"),
            Type::Variable(var) => write!(f, "{var}"),
            Type::Existential(ex) => write!(f, "'{ex}"),
            Type::Quantification(a, ty) => write!(f, "(∀{a}. {ty})"),
            Type::Function(a, c) => write!(f, "({a} -> {c})"),
            Type::BaseType(name) => write!(f, "{name}"),
            Type::HigherKinded(name, generics, open) => write!(
                f,
                "{}[{}, {}]",
                name.as_ref().map_or("F", |v| v),
                generics
                    .iter()
                    .map(|a| a.as_ref().map_or("_".to_string(), |a| a.to_string()))
                    .reduce(|acc, e| acc + "," + &e)
                    .unwrap_or("_".to_string()),
                open.then_some("..").unwrap_or_default()
            ),
            Type::Product(vec) => {
                write!(
                    f,
                    "({})",
                    vec.iter().map(|a| a.to_string() + ",").collect::<String>()
                )
            }
            Type::Sum(vec) => write!(
                f,
                "({})",
                vec.iter().map(|a| a.to_string() + "|").collect::<String>()
            ),
        }
    }
}
impl ContextElement {
    pub fn to_type(self) -> TypedVar {
        match self {
            ContextElement::TypedVariable(name, ty) => TypedVar(name, ty),
            ContextElement::Solved(name, ty) => TypedVar(name, ty),
            _ => panic!("Context Element not solved!"),
        }
    }
}
impl Context {
    pub fn is_complete(&self) -> bool {
        println!("{:?}", self.elements);
        self.elements.iter().all(|elem| match elem {
            ContextElement::Variable(alpha) => false,
            ContextElement::TypedVariable(var, ty) => self.is_well_formed(&ty),
            ContextElement::Existential(alpha_hat) => false,
            ContextElement::Solved(var, ty) => self.is_well_formed(&ty),
        })
    }
}

impl<T> Type<T> {
    pub fn is_monotype(&self) -> bool {
        match self {
            Type::Quantification(_, _) => false,
            Type::Function(a, b) => a.is_monotype() && b.is_monotype(),
            _ => true,
        }
    }
}
