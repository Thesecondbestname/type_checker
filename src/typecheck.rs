#[derive(Clone, Debug, Default)]
pub(crate) enum Constraint {
    #[default]
    Empty,
    // Conjunction(Box<Self>, Box<Self>),
    Eq(TypeId, TypeId),
    TypeClass(String, Vec<Type>),
    // Implication
}
impl Constraint {
    pub fn apply(self, types: &mut [(Type, String)]) -> Option<()> {
        match self {
            Constraint::Empty => Some(()),
            Constraint::Eq(a, b) => {
                let (t0, t1) = (&types[a.0], &types[b.0]);
                println!(
                    "Applying Equality on {}: {:?} and {}: {:?}",
                    t0.1, t0.0, t1.1, t1.0
                );
                if t0.0 == t1.0 {
                } else if t0.0.is_more_concrete(&t1.0) {
                    println!("After applying Eq: {:?}", &types);
                    types[b.0] = t1.clone();
                } else {
                    println!("After applying Eq: {:?}", &types);
                    types[a.0] = t0.clone();
                };
                Some(())
            }
            Constraint::TypeClass(_, _) => todo!(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum LitType {
    Unit,
    String,
    Int,
    Float,
    Bool,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Type {
    /// Literal type
    Lit(LitType),
    /// Signifies that the variable is unknown
    Variable,
    /// Forall quantifier
    Forall(TypeId),
}
impl Type {
    const fn is_more_concrete(&self, rhs: &Self) -> bool {
        match (self, rhs) {
            (Type::Lit(_), Type::Lit(_)) => {
                panic!("We should never get here due to the equality check")
            }
            (Type::Lit(_), _) | (Type::Forall(_), Type::Variable) => true,
            (Type::Variable, _) | (Type::Forall(_), Type::Lit(_)) => false,
            (Type::Forall(_), Type::Forall(_)) => panic!("I'm unsure as to what to do here"),
        }
    }
}

#[derive(Clone, Debug, Copy, PartialEq, Eq)]
pub(super) struct TypeId(pub usize);
impl TypeId {
    pub const BOOL: Self = Self(0);
    pub const INT: Self = Self(1);
    pub const FLOAT: Self = Self(2);
    pub const STRING: Self = Self(3);
}
impl Into<usize> for TypeId {
    fn into(self) -> usize {
        self.0
    }
}
