use crate::VarId;

pub enum Expr<Var> {
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
pub enum Type<Var> {
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
pub(crate) struct TCContext {
    pub elements: Vec<ContextElement>,
    pub existentials: usize,
    pub markers: Vec<usize>,
    pub ident_level: usize,
}

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
impl ContextElement {
    pub fn to_type(self) -> TypedVar {
        match self {
            Self::TypedVariable(name, ty) => TypedVar(name, ty),
            Self::Solved(name, ty) => TypedVar(name, ty),
            _ => panic!("Context Element not solved!"),
        }
    }
}
impl TCContext {
    pub fn is_complete(&self) -> bool {
        println!("{:?}", self.elements);
        self.elements.iter().all(|elem| match elem {
            ContextElement::Variable(alpha) => false,
            ContextElement::TypedVariable(var, ty) => self.is_well_formed(ty),
            ContextElement::Existential(alpha_hat) => false,
            ContextElement::Solved(var, ty) => self.is_well_formed(ty),
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
