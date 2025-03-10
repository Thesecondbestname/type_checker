use core::fmt;
use std::fmt::Write;
pub(crate) enum Term {
    Variable(String),
    Unit,
    Abstraction(String, Box<Term>),
    Application(Box<Term>, Box<Term>),
    Annotation(Box<Term>, Box<Type>),
    Functor(String, Box<Term>),
    Let(String, Box<Term>, Box<Term>),
    LitInt(usize),
    LitBool(bool),
}
/// 1 | α | ^α | ∀α. A | A → B
#[derive(PartialEq, Debug, Clone, Eq)]
pub(crate) enum Type {
    /// 1
    Unit,
    /// α
    Variable(String),
    /// ^α MAYBE SOLVED!!
    Existential(String),
    /// ∀α. A
    Quantification(String, Box<Type>),
    /// A →  B
    Function(Box<Type>, Box<Type>),
    /// Named Type
    BaseType(String),
    /// Option[T, ..], F[_]
    HigherKinded(Option<String>, Vec<Option<Type>>, bool),
}
/// Θ ::= · | Γ, α | Γ, x : A | Γ, ^α | Γ, ^α = τ | Γ, I^
#[derive(PartialEq, Debug, Clone, Eq)]
pub(crate) enum ContextElement {
    /// Γ, α
    Variable(String),
    /// Γ, x : A
    TypedVariable(String, Type),
    /// Γ, ^α
    Existential(String),
    /// Γ, ^α = τ
    Solved(String, Type),
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
    UnannotatedVariable(String),
    DoubelyInitializedVariable(String),
    // Expected, found
    TypeMissmatch(Type, Type),
    InvalidInstantiation(Type, String),
    NotWellFormed(Type),
    KindMissmatch(Type, Type),
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

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Term::Unit => write!(f, "()"),
            Term::Variable(var) => write!(f, "{}", var),
            Term::Abstraction(alpha, e) => write!(f, "(\\{} -> {})", alpha, e),
            Term::Application(e1, e2) => write!(f, "{} {}", e1, e2),
            Term::Annotation(e, a) => write!(f, "({}: {})", e, a),
            Term::LitBool(b) => write!(f, "{b}"),
            Term::LitInt(i) => write!(f, "{i}"),
            Term::Functor(name, term) => write!(f, "{name}::new({term})"),
            Term::Let(name, term, term1) => write!(f, "let {name} = {term} in {term1}"),
        }
    }
}
impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::Unit => write!(f, "()"),
            Self::Variable(var) => write!(f, "{var}"),
            Self::Existential(ex) => write!(f, "'{ex}"),
            Self::Quantification(a, ty) => write!(f, "(∀{a}. {ty})"),
            Self::Function(a, c) => write!(f, "({a} -> {c})"),
            Type::BaseType(name) => write!(f, "{name}"),
            Self::HigherKinded(name, generics, open) => write!(
                f,
                "{}[{}, {}]",
                name.as_ref().map_or("F", |v| v),
                generics
                    .iter()
                    .map(|a| a.clone().map_or("_".to_string(), |a| a.to_string()))
                    .reduce(|acc, e| acc + "," + &e)
                    .unwrap_or("_".to_string()),
                open.then_some("..").unwrap_or_default()
            ),
        }
    }
}
impl Type {
    pub fn is_monotype(&self) -> bool {
        match self {
            Type::Quantification(_, _) => false,
            Type::Function(a, b) => a.is_monotype() && b.is_monotype(),
            _ => true,
        }
    }
}
/*
trait[T, F[T]] Monad {
  lift# (T -> F[T]); // Lift a value into the monad
  flat_map#((F[T], fn(T) -> F[U]) -> F[U]);
}
impl Monad[F[T]] for F[T] {
    lift(t) =
}
*/
