use crate::Ast;
use crate::ContextElement;
use crate::TCContext;
use crate::Type;
use crate::TypedVar;
use crate::VarId;
use std::fmt;

impl fmt::Display for TCContext {
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

impl<T: std::fmt::Display> fmt::Display for Ast<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::Unit => write!(f, "()"),
            Self::Variable(var) => write!(f, "{}", var),
            Self::Abstraction(alpha, e) => write!(f, "(\\{} -> {})", alpha, e),
            Self::Application(e1, e2) => write!(f, "{} {}", e1, e2),
            Self::Annotation(e, a) => write!(f, "({}: {})", e, a),
            Self::LitInt(i) => write!(f, "{i}"),
            Self::Functor(name, term) => write!(f, "{name}::new({term})"),
            Self::Let(name, term, term1) => write!(f, "let {name} = {term} in {term1}"),
            Self::Tuple(vec) => write!(
                f,
                "({})",
                vec.iter()
                    .map(std::string::ToString::to_string)
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
impl<T: fmt::Display> fmt::Display for Type<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Type::Unit => write!(f, "()"),
            Type::Variable(var) => write!(f, "'{var}"),
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
                    .map(|a| a
                        .as_ref()
                        .map_or("_".to_string(), std::string::ToString::to_string))
                    .reduce(|acc, e| acc + "," + &e)
                    .unwrap_or_else(|| "_".to_string()),
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
