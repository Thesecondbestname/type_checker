use crate::{VarId, types::Ast};
use std::collections::{HashMap, HashSet};

pub fn idents_to_ids(ast: Ast<String>) -> (Ast<VarId>, Vec<String>) {
    let mut ctx = VarContext {
        vars: HashMap::new(),
        next_id: 0,
        names: vec![],
    };
    (ctx.names_to_vars(ast), ctx.names)
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
            .map_or_else(|| panic!("Use of undeclared Variable"), |var| *var)
    }
    fn fresh_id(&mut self) -> VarId {
        self.next_id += 1;
        self.names.push(String::new());
        VarId(self.next_id)
    }
    fn strs_to_ids_shadowed_name(&mut self, ast: Ast<String>, name: String) -> (Ast<VarId>, VarId) {
        let id = self.fresh_id();
        let n = self.vars.insert(name.clone(), id);
        let e = self.names_to_vars(ast);
        if let Some(v) = n {
            self.vars.get_mut(&name).map(|_| v);
        }
        self.names[id.0] = name;
        (e, id)
    }
    fn names_to_vars(&mut self, ast: Ast<String>) -> Ast<VarId> {
        match ast {
            Ast::Variable(var) => Ast::Variable(self.lookup_var(&var)),
            Ast::Unit => Ast::Unit,
            Ast::Abstraction(name, e) => {
                let (e, id) = self.strs_to_ids_shadowed_name(*e, name);
                Ast::Abstraction(id, e.into())
            }
            Ast::Application(e1, e2) => Ast::Application(
                self.names_to_vars(*e1).into(),
                self.names_to_vars(*e2).into(),
            ),
            Ast::Annotation(e, t) => Ast::Annotation(self.names_to_vars(*e).into(), t),
            Ast::Functor(_, ast) => todo!(),
            Ast::Let(name, e1, e2) => {
                let e1 = self.names_to_vars(*e1);
                let (e2, id) = self.strs_to_ids_shadowed_name(*e2, name);
                Ast::Let(id, e1.into(), e2.into())
            }
            Ast::Tuple(asts) => {
                Ast::Tuple(asts.into_iter().map(|e| self.names_to_vars(e)).collect())
            }
            Ast::LitInt(i) => Ast::LitInt(i),
        }
    }
}
