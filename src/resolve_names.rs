pub mod unique_id {
    use crate::Type;
    use crate::VarId;
    use std::collections::HashMap;

    use crate::types::Expr;

    pub fn resolve_names(ast: Expr<String>) -> (Expr<VarId>, Vec<String>) {
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
            ast: Expr<String>,
            name: String,
        ) -> (Expr<VarId>, VarId) {
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
        pub(crate) fn resolve_ident_names(&mut self, ast: Expr<String>) -> Expr<VarId> {
            match ast {
                Expr::Variable(var) => Expr::Variable(self.lookup_var(&var)),
                Expr::Unit => Expr::Unit,
                Expr::Abstraction(name, e) => {
                    let (e, id) = self.resolve_names_shadowing(*e, name);
                    Expr::Abstraction(id, e.into())
                }
                Expr::Application(e1, e2) => Expr::Application(
                    self.resolve_ident_names(*e1).into(),
                    self.resolve_ident_names(*e2).into(),
                ),
                Expr::Annotation(e, t) => Expr::Annotation(
                    self.resolve_ident_names(*e).into(),
                    Box::new(self.resolve_type(*t)),
                ),
                Expr::Functor(n, ast) => Expr::Functor(n, self.resolve_ident_names(*ast).into()),
                Expr::Let(name, e1, e2) => {
                    let e1 = self.resolve_ident_names(*e1);
                    let (e2, id) = self.resolve_names_shadowing(*e2, name);
                    Expr::Let(id, e1.into(), e2.into())
                }
                Expr::Tuple(asts) => Expr::Tuple(
                    asts.into_iter()
                        .map(|e| self.resolve_ident_names(e))
                        .collect(),
                ),
                Expr::LitInt(i) => Expr::LitInt(i),
            }
        }
    }
}
pub mod debrujin {
    use crate::{Type, VarId, types::Expr};
    use std::collections::HashMap;

    struct VarContext {
        vars: HashMap<String, VarId>,
        names: Vec<String>,
        scope: usize,
        ty_scope: usize,
    }
    pub fn resolve_names(ast: Expr<String>) -> (Expr<VarId>, Vec<String>) {
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
        fn resolve_ident_names(&mut self, ast: Expr<String>) -> Expr<VarId> {
            match ast {
                Expr::Variable(var) => Expr::Variable(self.lookup_var(&var)),
                Expr::Unit => Expr::Unit,
                // \x. \y. (\z. y z ) x
                // Fun(x, Fun(y, Call(Fun(z, Call(y, z)), x)))
                // Fun(2, Fun(1, Call(Fun(0, Call(1, 0)), 2)))
                Expr::Abstraction(name, e) => {
                    let index = self.get_index();
                    let e = self.resolve_names_shadowing(*e, name);
                    self.incr_index();
                    Expr::Abstraction(index, Box::new(e))
                }
                Expr::Application(e1, e2) => Expr::Application(
                    self.resolve_ident_names(*e1).into(),
                    self.resolve_ident_names(*e2).into(),
                ),
                Expr::Annotation(e, t) => Expr::Annotation(
                    self.resolve_ident_names(*e).into(),
                    Box::new(self.resolve_type(*t)),
                ),
                Expr::Functor(n, ast) => (Expr::Functor(n, self.resolve_ident_names(*ast).into())),
                Expr::Let(name, e1, e2) => {
                    self.incr_index();
                    let e1 = self.resolve_ident_names(*e1);
                    let e2 = self.resolve_names_shadowing(*e2, name);
                    Expr::Let(self.get_index(), e1.into(), e2.into())
                }
                Expr::Tuple(asts) => Expr::Tuple(
                    asts.into_iter()
                        .map(|e| {
                            self.new_scope();
                            self.resolve_ident_names(e)
                        })
                        .collect(),
                ),
                Expr::LitInt(i) => (Expr::LitInt(i)),
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
        fn resolve_names_shadowing(&mut self, ast: Expr<String>, name: String) -> Expr<VarId> {
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
