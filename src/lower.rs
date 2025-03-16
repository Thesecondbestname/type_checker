use std::hash::DefaultHasher;

use crate::{
    apply_context,
    types::{Ast, Context},
};

struct VarId(usize);

struct Var<'a> {
    id: VarId,
    ty: &'a Type<'a>,
}
enum Kind {
    Type,
}
enum Type<'a> {
    Base(isize),
    Var(Var<'a>),
    Fun(Box<Self>, Box<Self>),
    TyFun(Kind, Box<Self>),
}

enum SystemF<'a> {
    Var(Var<'a>),
    Int(isize),
    Fun(Var<'a>, Box<Self>),
    App(Box<Self>, Box<Self>),
    TyFun(Kind, Box<Self>),
    TyApp(Box<Self>, Type<'a>),
    Local(Var<'a>, Box<Self>, Box<Self>),
}
struct LowerTypes {
    type_env: Vec<(crate::types::TypedVar, VarId)>,
}

// fn lower<'a>(ast: Ast<String>, ctx: Context) -> (SystemF<'a>, Type<'a>) {
//     assert!(ctx.is_complete());
//     let type_env: Vec<(crate::types::TypedVar, VarId)> = ctx
//         .elements
//         .into_iter()
//         .map(|a| a.to_type())
//         .rev()
//         .enumerate()
//         .map(|(i, tyvar)| (tyvar, VarId(i)))
//         .collect::<Vec<_>>();
//     let lower_types = LowerTypes { type_env };
// }
