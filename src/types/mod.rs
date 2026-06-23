pub(crate) mod effects;
pub(crate) mod ty;

pub use crate::tc::{
    check, infer_expr, infer_expr_dicts, infer_expr_env, Checked, ClassInfo, CtorInfo, DataInfo,
    DeclInfo, Dict, DictTable, EffOpInfo, Env, HeadKey, InstInfo, InstKeys, PathRes,
};
pub use ty::{show_effects, Effects, Type, CONS, EQ_CLASS, LIST, NIL, ORD_CLASS, SHOW_CLASS};
