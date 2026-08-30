use std::collections::BTreeSet;

use prism_common::sym::Sym;
use prism_syntax::ast::Grade;
use prism_syntax::kind::Kind;
use ty::EffRow;

pub use prism_syntax::coeffect;
pub mod deps;
pub mod repr;
pub mod sig;
pub mod ty;

pub use repr::{
    is_or_null_element, is_or_null_element_in, layout_of_type, layout_of_type_in, repr_of_type,
    scalar_plan, AbiLayout, LiteralCell, RcBehavior, Repr, ScalarPlan, TypeLayout, ZeroPossibility,
};
pub use ty::{
    show_effects, show_type_with_effects, Effects, Type, ARBITRARY_CLASS, BUF, CANONICAL, CONS,
    DIV_CLASS, EQ_CLASS, F32X4, F64X2, FLOAT_BUF, FROM_JSON_CLASS, HASH_CLASS, I32X4, I64X2,
    IDENTIFIABLE, IDENTIFIABLE_BUNDLE, INT_BUF, LENS, LIST, NIL, NONE, NUM_CLASS, OPTION,
    ORD_CLASS, PLATE_CLASS, SERIALIZE_CLASS, SHOW_CLASS, SOME, STABLE_CLASS, TO_JSON_CLASS,
};

/// One constructor's checked shape: its datatype, parameters and their kinds,
/// argument types, runtime tag, and field names.
///
/// Produced by the checker and consumed by elaboration and code generation, so
/// it lives in the shared type vocabulary rather than inside either.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CtorInfo {
    pub type_name: Sym,
    pub params: Vec<Sym>,
    // Kind of each parameter, parallel to `params`. Lets pattern matching open a
    // `Row`-kinded parameter with a fresh row existential (substituted into the
    // field types with `subst_row_var`) rather than a type existential.
    pub param_kinds: Vec<Kind>,
    pub args: Vec<Type>,
    pub tag: usize,
    pub fields: Vec<Sym>,
}

impl CtorInfo {
    /// A stable content encoding for cache keys, not the `Debug` rendering.
    ///
    /// Fields use canonical renderings and length prefixes to avoid ambiguity.
    #[must_use]
    pub fn identity_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        let put = |out: &mut Vec<u8>, bytes: &[u8]| {
            out.extend_from_slice(&(bytes.len() as u64).to_le_bytes());
            out.extend_from_slice(bytes);
        };
        put(&mut out, self.type_name.as_str().as_bytes());
        out.extend_from_slice(&(self.params.len() as u64).to_le_bytes());
        for p in &self.params {
            put(&mut out, p.as_str().as_bytes());
        }
        out.extend_from_slice(&(self.param_kinds.len() as u64).to_le_bytes());
        for k in &self.param_kinds {
            put(&mut out, k.show().as_bytes());
        }
        out.extend_from_slice(&(self.args.len() as u64).to_le_bytes());
        for a in &self.args {
            put(&mut out, a.show().as_bytes());
        }
        out.extend_from_slice(&(self.tag as u64).to_le_bytes());
        out.extend_from_slice(&(self.fields.len() as u64).to_le_bytes());
        for f in &self.fields {
            put(&mut out, f.as_str().as_bytes());
        }
        out
    }
}

/// One top-level declaration's checked facts as elaboration and the FBIP
/// checker consume them.
#[derive(Clone, Debug)]
pub struct DeclInfo {
    pub name: String,
    pub params: Vec<String>,
    pub ty: Type,
    pub effects: Effects,
    /// Provably pure: the body's principal effect row solved empty and closed,
    /// recorded from the pre-generalization witness (generalization re-opens a
    /// pure row for context fit, so this fact cannot be read off `ty`). This is
    /// the precondition the `borrow` calling convention requires; borrow
    /// inference consumes it, and a rehydrated interface conservatively reports
    /// `false` because the witness is not serialized.
    pub pure: bool,
}

/// One effect operation's checked signature facts.
#[derive(Clone, Debug)]
pub struct EffOpInfo {
    pub effect_name: Sym,
    pub eff_params: Vec<Sym>,
    pub params: Vec<Type>,
    pub ret: Type,
    // Declared resumption multiplicity of the op (see `ast::Grade`). Consumed by
    // effect lowering to decide which handlers may disable var-erasure; a
    // handler clause more general than this grade is rejected at desugar.
    pub grade: Grade,
}

impl EffOpInfo {
    // True when the op signature carries a free effect-row variable (a thunk
    // parameter whose row has an open tail, e.g. `() -> a ! {Eff | e}`). Such an
    // op must tie that variable to the ambient row at each perform site so the
    // thunk's extra effects flow out; see `Tc::bind_op_rows_to_ambient`.
    #[must_use]
    pub fn has_free_row_vars(&self) -> bool {
        let mut rows = BTreeSet::new();
        for p in &self.params {
            collect_row_vars(p, &mut rows);
        }
        collect_row_vars(&self.ret, &mut rows);
        !rows.is_empty()
    }

    // Instantiate the op's param/return types with the effect's type arguments,
    // substituting each declared effect parameter for the supplied argument.
    #[must_use]
    pub fn instantiate(&self, args: &[Type]) -> (Vec<Type>, Type) {
        let mut params = self.params.clone();
        let mut ret = self.ret.clone();
        for (p, t) in self.eff_params.iter().zip(args) {
            for q in &mut params {
                *q = q.subst_var(*p, t);
            }
            ret = ret.subst_var(*p, t);
        }
        (params, ret)
    }
}

// Visit the tail of every effect row reachable in a type (function rows and
// row-kinded arguments, through every type former), recursing into row label
// arguments. The one traversal behind every "which rows flow through this
// interface" question; callers filter the tails they care about.
pub fn for_each_row_tail(t: &Type, f: &mut impl FnMut(&EffRow)) {
    match t {
        Type::Fun(ps, row, r) => {
            for p in ps {
                for_each_row_tail(p, f);
            }
            f(row.tail());
            row.for_each_arg(&mut |a| for_each_row_tail(a, f));
            for_each_row_tail(r, f);
        }
        Type::Con(_, ps) | Type::Tuple(ps) | Type::UnboxedTuple(ps) => {
            for p in ps {
                for_each_row_tail(p, f);
            }
        }
        Type::UnboxedRecord(fs) => {
            for (_, t) in fs {
                for_each_row_tail(t, f);
            }
        }
        Type::App(h, a) => {
            for_each_row_tail(h, f);
            for_each_row_tail(a, f);
        }
        Type::OrNull(a) => for_each_row_tail(a, f),
        Type::Forall(_, b) | Type::RowForall(_, b) => for_each_row_tail(b, f),
        Type::Row(r) => {
            f(r.tail());
            r.for_each_arg(&mut |a| for_each_row_tail(a, f));
        }
        _ => {}
    }
}

// Free effect-row variables in a type, so a class method's signature can be
// generalized over its row variables (an effect-polymorphic method like `fmap`).
pub fn collect_row_vars(t: &Type, out: &mut BTreeSet<Sym>) {
    for_each_row_tail(t, &mut |tail| {
        if let EffRow::Var(v) = tail {
            out.insert(*v);
        }
    });
}
