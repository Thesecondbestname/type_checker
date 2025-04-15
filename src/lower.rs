#[derive(Debug, PartialEq, Eq)]
struct Var(VarId, Type);
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct VarId(usize);
impl VarId {
    const INCOMPARABLE: Self = Self(usize::MAX);
}
#[derive(Debug, Clone, PartialEq, Eq)]
enum Kind {
    Type,
    Fun(Box<Kind>, Box<Kind>),
}
#[derive(Debug, PartialEq, Eq)]
enum Type {
    /// int | bool
    Base(isize),
    /// a
    Var(Box<Var>),
    /// c -> c
    Fun(Box<Self>, Box<Self>),
    /// \(a: k). c
    TyFun(Kind, Box<Self>),
    /// c c
    TyApp(Box<Self>, Box<Self>),
    /// forall (a: k). c
    Forall(Kind, Box<Self>),
    Prod(Vec<Self>),
    Sum(Vec<Self>),
    Kind(Kind),
}
#[derive(Debug)]
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
}
// fmap :: F a -> (a -> b) -> F b
// fmap Option a f = Option $ f a
//
// \F. \a. \x.
