use crate::Constraint;
use crate::Type;
use crate::TypeId;

#[derive(Clone, Debug)]
struct State {
    types: Vec<(Type, Constraint, String)>,
    existentials: usize,
}
impl State {
    /// Returns a fresh exitential
    fn fresh_existential(&mut self) -> TypeId {
        let result = self.existentials;
        self.existentials += 1;
        self.types
            .push((Type::Exists, Constraint::Unsolved, result.to_string()));
        TypeId(result)
    }
    /// Returns a named exitential
    fn named_existential(&mut self, name: String) -> TypeId {
        let result = self.existentials;
        self.existentials += 1;
        self.types.push((Constraint::Unsolved, name));
        TypeId(result)
    }
    fn eq_constraint(&mut self, t1: TypeId, t2: TypeId) {
        let x = self.types[t1.0];
        let y = Constraint::Eq(t2);
    }
}
