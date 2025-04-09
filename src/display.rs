use crate::Ast;
use crate::Context;
use crate::ContextElement;
use crate::Type;
use crate::TypeId;
use crate::TypedVar;
use crate::VarId;
use crate::types::NamedType;
use crate::types::SolvedType;
use std::fmt;

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

impl<T: std::fmt::Display, Ty: std::fmt::Display> fmt::Display for Ast<T, Ty> {
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
impl Ast<VarId, Type<VarId>> {
    pub fn as_string(&self, names: &Vec<String>, type_arena: &Vec<Type<VarId>>) -> String {
        match self {
            Ast::Unit => "()".to_string(),
            Ast::Variable(var) => names[var.0].to_string(),
            Ast::Abstraction(alpha, e) => format!("(\\{} -> {})", names[alpha.0], e),
            Ast::Application(e1, e2) => format!("{} {}", e1, e2),
            Ast::Annotation(e, a) => format!("({}: {})", e, a.as_string(type_arena)),
            Ast::LitInt(i) => format!("{i}"),
            Ast::Functor(name, term) => format!("{name}::new({term})"),
            Ast::Let(name, term, term1) => {
                format!("let {} = {term} in {term1}", names[name.0])
            }
            Ast::Tuple(vec) => format!(
                "({})",
                vec.iter()
                    .map(|a| a.as_string(names, type_arena))
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
impl fmt::Display for TypeId {
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
impl fmt::Display for SolvedType {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            SolvedType::Unit => write!(f, "()"),
            SolvedType::Variable(var) => write!(f, "{var}"),
            SolvedType::Quantification(a, ty) => write!(f, "(∀{a}. {ty})"),
            SolvedType::Function(a, c) => write!(f, "({a} -> {c})"),
            SolvedType::BaseType(name) => write!(f, "{name}"),
            SolvedType::HigherKinded(name, generics, open) => write!(
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
            SolvedType::Product(vec) => {
                write!(
                    f,
                    "({})",
                    vec.iter().map(|a| a.to_string() + ",").collect::<String>()
                )
            }
            SolvedType::Sum(vec) => write!(
                f,
                "({})",
                vec.iter().map(|a| a.to_string() + "|").collect::<String>()
            ),
        }
    }
}
impl<T: fmt::Display> fmt::Display for NamedType<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            NamedType::Unit => write!(f, "()"),
            NamedType::Variable(var) => write!(f, "{var}"),
            NamedType::Existential(ex) => write!(f, "'{ex}"),
            NamedType::Quantification(a, ty) => write!(f, "(∀{a}. {ty})"),
            NamedType::Function(a, c) => write!(f, "({a} -> {c})"),
            NamedType::BaseType(name) => write!(f, "{name}"),
            NamedType::HigherKinded(name, generics, open) => write!(
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
            NamedType::Product(vec) => {
                write!(
                    f,
                    "({})",
                    vec.iter().map(|a| a.to_string() + ",").collect::<String>()
                )
            }
            NamedType::Sum(vec) => write!(
                f,
                "({})",
                vec.iter().map(|a| a.to_string() + "|").collect::<String>()
            ),
        }
    }
}
impl Type<VarId> {
    pub fn as_string(&self, ty_arena: &Vec<Self>) -> String {
        match self {
            Type::Unit => "Unit".to_string(),
            Type::Variable(v) => v.to_string(),
            Type::Existential(v) => v.to_string() + "'",
            Type::Quantification(v, type_id) => {
                "∀".to_string() + &v.to_string() + "." + &ty_arena[type_id.0].as_string(ty_arena)
            }
            Type::Function(type_id, type_id1) => {
                ty_arena[type_id.0].as_string(ty_arena)
                    + " -> "
                    + &ty_arena[type_id1.0].as_string(ty_arena)
            }
            Type::Product(type_ids) => todo!(),
            Type::Sum(type_ids) => todo!(),
            Type::BaseType(_) => todo!(),
            Type::HigherKinded(_, type_ids, _) => todo!(),
        }
    }
}
