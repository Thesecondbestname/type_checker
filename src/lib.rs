#![allow(dead_code)]
mod typecheck;

use std::fmt;

#[derive(Clone, Debug, Default)]
enum Constraint {
    #[default]
    Unsolved,
    Conjunction(Box<Self>, Box<Self>),
    Eq(Type),
    TypeClass(String, Vec<Type>),
    Empty, // Implication
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum LitType {
    Unit,
    Char,
    String,
    Int,
    Float,
    Bool,
}

impl fmt::Display for LitType {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::Unit => write!(f, "()"),
            Self::Char => write!(f, "Char"),
            Self::String => write!(f, "String"),
            Self::Int => write!(f, "Int"),
            Self::Float => write!(f, "Float"),
            Self::Bool => write!(f, "Bool"),
        }
    }
}
/// Figure 6
#[derive(Clone, Debug, PartialEq, Eq)]
enum Type {
    /// Literal type
    Lit(LitType),
    /// Signifies that the variable exists
    Exists,
    /// Forall quantifier
    Forall(TypeId, Box<Type>),
    /// Function type
    Fun(Box<Type>, Box<Type>),
    /// Tuple type
    Tup(Box<Type>, Box<Type>),
}
#[derive(Clone, Debug, Copy, PartialEq, Eq)]
struct TypeId(usize);
impl Into<usize> for TypeId {
    fn into(self) -> usize {
        self.0
    }
}
