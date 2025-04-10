use std::hash::DefaultHasher;

use crate::{
    apply_context,
    types::{Ast, TCContext, TypedVar},
};

struct Var(VarId);
#[derive(Clone, Copy)]
struct VarId(usize);
enum Kind {
    Type,
}
enum Type {
    Base(isize),
    Var(Var),
    Fun(Box<Self>, Box<Self>),
    TyFun(Kind, Box<Self>),
    Prod(Vec<Self>),
    Sum(Vec<Self>),
}

enum SystemF {
    Var(Var),
    Int(isize),
    Fun(Var, Box<Self>),
    App(Box<Self>, Box<Self>),
    TyFun(Kind, Box<Self>),
    TyApp(Box<Self>, Type),
    Local(Var, Box<Self>, Box<Self>),
}
struct LowerTypes {
    type_env: Vec<VarId>,
    index: usize,
}
impl LowerTypes {
    const fn incr_index(&mut self) -> VarId {
        let i = self.index;
        self.index += 1;
        VarId(i)
    }
    fn store_var(&mut self, id: crate::VarId, item: VarId) {
        self.type_env[id.0] = item;
    }
    fn lookup_var(&self, id: crate::VarId) -> VarId {
        *self.type_env.get(id.0).expect("COMPILER ERRORRRR")
    }
    fn lower_types(&mut self, ty: crate::types::Type<crate::VarId>) -> Type {
        match ty {
            crate::Type::Unit => Type::Base(0),
            crate::Type::Variable(v) => Type::Var(Var(self.lookup_var(v))),
            crate::Type::Quantification(id, ty) => {
                let i = self.incr_index();
                self.store_var(id, i);
                Type::TyFun(Kind::Type, Box::new(self.lower_types(*ty)))
            }
            crate::Type::Function(a, b) => Type::Fun(
                Box::new(self.lower_types(*a)),
                Box::new(self.lower_types(*b)),
            ),
            crate::Type::Product(items) => {
                Type::Prod(items.into_iter().map(|ty| self.lower_types(ty)).collect())
            }
            crate::Type::Sum(items) => {
                Type::Sum(items.into_iter().map(|ty| self.lower_types(ty)).collect())
            }
            crate::Type::BaseType(n) => Type::Base(3),
            crate::Type::HigherKinded(_, items, _) => todo!(),
            _ => panic!("Unsanitized Input >:("),
        }
    }
}
