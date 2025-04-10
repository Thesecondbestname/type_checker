use crate::{
    VarId,
    types::{Ast, IdAst, Type},
};
use std::collections::{HashMap, HashSet};

pub mod unique_id {
    use crate::Type;
    use crate::VarId;
    use std::collections::HashMap;

    use crate::types::Ast;

    pub fn resolve_names(ast: Ast<String>) -> (Ast<VarId>, Vec<String>) {
        let mut ctx = VarContext {
            vars: HashMap::new(),
            names: vec![],
            scope: 0,
        };
        let ast = ctx.resolve_ident_names(ast);
        (ast, ctx.names)
    }

    pub(crate) struct VarContext {
        pub(crate) vars: HashMap<String, VarId>,
        pub(crate) names: Vec<String>,
        pub(crate) scope: usize,
    }

    impl VarContext {
        pub(crate) fn lookup_var(&self, var: &str) -> VarId {
            self.vars
                .get(var)
                .map_or_else(|| panic!("Use of undeclared Variable {var}"), |var| *var)
        }
        pub(crate) fn lookup_ty(&self, var: &str) -> VarId {
            self.vars.get(var).map_or_else(
                || panic!("Use of undeclared Quantification {var}"),
                |var| *var,
            )
        }
        pub(crate) fn fresh_id(&mut self, name: String) -> VarId {
            self.names.push(name);
            VarId(self.names.len() - 1)
        }
        pub(crate) fn resolve_names_shadowing(
            &mut self,
            ast: Ast<String>,
            name: String,
        ) -> (Ast<VarId>, VarId) {
            let id = self.fresh_id(name.clone());
            let n = self.vars.insert(name.clone(), id);
            let e = self.resolve_ident_names(ast);
            if let Some(v) = n {
                self.vars.get_mut(&name).map(|_| v);
            }
            (e, id)
        }
        pub(crate) fn resolve_type(&mut self, ty: Type<String>) -> Type<VarId> {
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
        pub(crate) fn resolve_ident_names(&mut self, ast: Ast<String>) -> Ast<VarId> {
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
}
pub mod debrujin {
    use crate::{Type, VarId, types::Ast};
    use std::collections::HashMap;

    struct VarContext {
        vars: HashMap<String, VarId>,
        names: Vec<String>,
        scope: usize,
        ty_scope: usize,
    }
    pub fn resolve_names(ast: Ast<String>) -> (Ast<VarId>, Vec<String>) {
        let mut ctx = VarContext {
            vars: HashMap::new(),
            names: vec![],
            scope: 0,
            ty_scope: 0,
        };
        let ast = ctx.resolve_ident_names(ast);
        (ast, ctx.names)
    }
    impl VarContext {
        const fn get_index(&self) -> VarId {
            VarId(self.scope)
        }
        fn resolve_ident_names(&mut self, ast: Ast<String>) -> Ast<VarId> {
            match ast {
                Ast::Variable(var) => Ast::Variable(self.lookup_var(&var)),
                Ast::Unit => Ast::Unit,
                // \x. \y. (\z. y z ) x
                // Fun(x, Fun(y, Call(Fun(z, Call(y, z)), x)))
                // Fun(2, Fun(1, Call(Fun(0, Call(1, 0)), 2)))
                Ast::Abstraction(name, e) => {
                    let index = self.get_index();
                    let e = self.resolve_names_shadowing(*e, name);
                    self.incr_index();
                    Ast::Abstraction(index, Box::new(e))
                }
                Ast::Application(e1, e2) => {
                    (Ast::Application(
                        self.resolve_ident_names(*e1).into(),
                        self.resolve_ident_names(*e2).into(),
                    ))
                }
                Ast::Annotation(e, t) => {
                    (Ast::Annotation(
                        self.resolve_ident_names(*e).into(),
                        Box::new(self.resolve_type(*t)),
                    ))
                }
                Ast::Functor(n, ast) => (Ast::Functor(n, self.resolve_ident_names(*ast).into())),
                Ast::Let(name, e1, e2) => {
                    self.incr_index();
                    let e1 = self.resolve_ident_names(*e1);
                    let e2 = self.resolve_names_shadowing(*e2, name);
                    (Ast::Let(self.get_index(), e1.into(), e2.into()))
                }
                Ast::Tuple(asts) => {
                    (Ast::Tuple(
                        asts.into_iter()
                            .map(|e| {
                                self.new_scope();
                                self.resolve_ident_names(e)
                            })
                            .collect(),
                    ))
                }
                Ast::LitInt(i) => (Ast::LitInt(i)),
            }
        }
        const fn new_scope(&mut self) {
            self.scope = 0;
        }
        fn lookup_var(&self, var: &str) -> VarId {
            self.vars
                .get(var)
                .map_or_else(|| panic!("Use of undeclared Variable {var}"), |var| *var)
        }
        fn resolve_names_shadowing(&mut self, ast: Ast<String>, name: String) -> Ast<VarId> {
            let id = self.get_index();
            let n = self.vars.insert(name.clone(), id);
            let e = self.resolve_ident_names(ast);
            if let Some(v) = n {
                self.vars.get_mut(&name).map(|_| v);
            }
            e
        }
        const fn incr_index(&mut self) {
            self.scope += 1;
        }
        fn resolve_type(&mut self, ty: Type<String>) -> Type<VarId> {
            match ty {
                Type::Unit => Type::Unit,
                Type::Variable(v) => Type::Variable(self.lookup_var(&v)),
                Type::Existential(v) => Type::Existential(self.lookup_var(&v)),
                Type::Quantification(n, ty) => {
                    let id = VarId(self.vars.len());
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
    }
}
