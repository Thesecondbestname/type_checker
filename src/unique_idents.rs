use crate::{
    VarId,
    types::{Ast, IdAst, Type},
};
use std::collections::{HashMap, HashSet};
#[derive(Clone, Copy)]
struct ForallId(usize);

pub fn resolve_names(ast: Ast<String>) -> (Ast<VarId>, Vec<String>) {
    let mut ctx = VarContext {
        vars: HashMap::new(),
        next_id: 0,
        names: vec![],
    };
    let ast = ctx.resolve_ident_names(ast);
    (ast, ctx.names)
}
struct VarContext {
    vars: HashMap<String, VarId>,
    next_id: usize,
    names: Vec<String>,
}
impl VarContext {
    fn lookup_var(&self, var: &str) -> VarId {
        self.vars
            .get(var)
            .map_or_else(|| panic!("Use of undeclared Variable {var}"), |var| *var)
    }
    fn lookup_ty(&self, var: &str) -> VarId {
        self.vars.get(var).map_or_else(
            || panic!("Use of undeclared Quantification {var}"),
            |var| *var,
        )
    }
    fn fresh_id(&mut self, name: String) -> VarId {
        self.names.push(name);
        VarId(self.names.len() - 1)
    }
    fn resolve_names_shadowing(&mut self, ast: Ast<String>, name: String) -> (Ast<VarId>, VarId) {
        let id = self.fresh_id(name.clone());
        let n = self.vars.insert(name.clone(), id);
        let e = self.resolve_ident_names(ast);
        if let Some(v) = n {
            self.vars.get_mut(&name).map(|_| v);
        }
        (e, id)
    }
    fn resolve_type(&mut self, ty: Type<String>) -> Type<VarId> {
        match ty {
            Type::Unit => Type::Unit,
            Type::Variable(v) => Type::Variable(self.lookup_var(&v)),
            Type::Existential(v) => Type::Existential(self.lookup_var(&v)),
            Type::Quantification(n, ty) => {
                let id = self.fresh_id(n.clone());
                let nid = self.vars.insert(n.clone(), id);
                let ty = self.resolve_type(*ty);
                if let Some(v) = nid {
                    self.vars.get_mut(&n).map(|_| v);
                }
                Type::Quantification(id, Box::new(ty))
            }
            Type::Function(a, b) => Type::Function(
                Box::new(self.resolve_type(*a)),
                Box::new(self.resolve_type(*b)),
            ),
            Type::Product(items) => {
                Type::Product(items.into_iter().map(|a| self.resolve_type(a)).collect())
            }
            Type::Sum(items) => {
                Type::Sum(items.into_iter().map(|a| self.resolve_type(a)).collect())
            }
            Type::BaseType(a) => Type::BaseType(a),
            Type::HigherKinded(a, items, c) => Type::HigherKinded(
                a,
                items
                    .into_iter()
                    .map(|a| a.map(|a| self.resolve_type(a)))
                    .collect(),
                c,
            ),
        }
    }
    fn resolve_ident_names(&mut self, ast: Ast<String>) -> Ast<VarId> {
        match ast {
            Ast::Variable(var) => Ast::Variable(self.lookup_var(&var)),
            Ast::Unit => Ast::Unit,
            Ast::Abstraction(name, e) => {
                let (e, id) = self.resolve_names_shadowing(*e, name);
                Ast::Abstraction(id, e.into())
            }
            Ast::Application(e1, e2) => Ast::Application(
                self.resolve_ident_names(*e1).into(),
                self.resolve_ident_names(*e2).into(),
            ),
            Ast::Annotation(e, t) => Ast::Annotation(
                self.resolve_ident_names(*e).into(),
                Box::new(self.resolve_type(*t)),
            ),
            Ast::Functor(n, ast) => Ast::Functor(n, self.resolve_ident_names(*ast).into()),
            Ast::Let(name, e1, e2) => {
                let e1 = self.resolve_ident_names(*e1);
                let (e2, id) = self.resolve_names_shadowing(*e2, name);
                Ast::Let(id, e1.into(), e2.into())
            }
            Ast::Tuple(asts) => Ast::Tuple(
                asts.into_iter()
                    .map(|e| self.resolve_ident_names(e))
                    .collect(),
            ),
            Ast::LitInt(i) => Ast::LitInt(i),
        }
    }
}
