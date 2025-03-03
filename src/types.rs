use core::fmt;
pub(crate) enum Term {
    Variable(String),
    Unit,
    Abstraction(String, Box<Term>),
    Application(Box<Term>, Box<Term>),
    Annotation(Box<Term>, Box<Type>),
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
    /// A → B
    Function(Box<Type>, Box<Type>),
    /// Named Type
    Constructor(String),
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
}

struct Existential(usize);
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
            Self::Variable(var) => write!(f, "{}", var),
            Self::Existential(ex) => write!(f, "'{}", ex),
            Self::Solved(a, ty) => write!(f, "'{}: {}", a, ty),
            Self::TypedVariable(x, ty) => write!(f, "{}: {}", x, ty),
        }
    }
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
    pub fn is_monotype(&self) -> bool {
        match self {
            Type::Quantification(_, _) => false,
            Type::Function(a, b) => a.is_monotype() && b.is_monotype(),
            _ => true,
        }
    }
}
