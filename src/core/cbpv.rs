use std::collections::{BTreeMap, BTreeSet};
use std::ops::Deref;

use serde::de::Error as _;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use super::builtins::{Builtin, FloatOp};
use super::effect_lower::resume_use::{self, ResumeUse};
use super::traverse::Visit;
use crate::names::ENTRY_POINT;
use crate::sym::Sym;
use crate::syntax::ast::BinOp;

// Primitive operators that survive elaboration. Short-circuit `&&`/`||` lower to
// `If` and never reach a `Prim`, so they have no variant here: a downstream pass
// cannot observe one.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum CoreOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    Addf,
    Subf,
    Mulf,
    Divf,
    Eqf,
    Nef,
    Ltf,
    Lef,
    Gtf,
    Gef,
}

impl CoreOp {
    // `None` for `&&`/`||`, which elaboration lowers to `If` rather than a `Prim`.
    #[must_use]
    pub const fn from_binop(op: BinOp) -> Option<Self> {
        Some(match op {
            BinOp::Add => Self::Add,
            BinOp::Sub => Self::Sub,
            BinOp::Mul => Self::Mul,
            BinOp::Div => Self::Div,
            BinOp::Rem => Self::Rem,
            BinOp::Eq => Self::Eq,
            BinOp::Ne => Self::Ne,
            BinOp::Lt => Self::Lt,
            BinOp::Le => Self::Le,
            BinOp::Gt => Self::Gt,
            BinOp::Ge => Self::Ge,
            // `And`/`Or` short-circuit and `Pow` lowers to a class method call;
            // none is a primitive core op.
            BinOp::And | BinOp::Or | BinOp::Pow => return None,
        })
    }

    // Stable content-hash tag. Keep these spellings byte-identical to the old
    // `Debug` rendering, but independent of enum variant names.
    #[must_use]
    pub const fn hash_tag(self) -> &'static str {
        match self {
            Self::Add => "Add",
            Self::Sub => "Sub",
            Self::Mul => "Mul",
            Self::Div => "Div",
            Self::Rem => "Rem",
            Self::Eq => "Eq",
            Self::Ne => "Ne",
            Self::Lt => "Lt",
            Self::Le => "Le",
            Self::Gt => "Gt",
            Self::Ge => "Ge",
            Self::Addf => "Addf",
            Self::Subf => "Subf",
            Self::Mulf => "Mulf",
            Self::Divf => "Divf",
            Self::Eqf => "Eqf",
            Self::Nef => "Nef",
            Self::Ltf => "Ltf",
            Self::Lef => "Lef",
            Self::Gtf => "Gtf",
            Self::Gef => "Gef",
        }
    }
}

// Pattern shapes that survive match compilation. Literals, booleans, and record
// patterns are compiled away into `If`/`Prim` tests and ctor patterns upstream,
// so a `Case` arm can only test a ctor or tuple (or bind/ignore the whole
// scrutinee). Field positions are plain binders (`Some` names it, `None` ignores
// it); nested sub-patterns are always flattened out, so they cannot appear here.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CorePat {
    Wild,
    Var(Sym),
    Ctor(Sym, Vec<Option<Sym>>),
    Tuple(Vec<Option<Sym>>),
}

mod f64_bits {
    use serde::{Deserialize, Deserializer, Serializer};

    // Serde's `with` hook requires the value by reference.
    #[allow(clippy::trivially_copy_pass_by_ref)]
    pub(super) fn serialize<S>(value: &f64, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_u64(value.to_bits())
    }

    pub(super) fn deserialize<'de, D>(deserializer: D) -> Result<f64, D::Error>
    where
        D: Deserializer<'de>,
    {
        u64::deserialize(deserializer).map(f64::from_bits)
    }
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum Value {
    Var(Sym),
    Int(i64),
    I64(i64),
    U64(u64),
    Float(#[serde(with = "f64_bits")] f64),
    Bool(bool),
    Unit,
    Str(String),
    Thunk(Box<Comp>),
    Ctor(Sym, usize, Vec<Self>),
    Tuple(Vec<Self>),
    // Unboxed products: the same value semantics as `Tuple`/a record, but a
    // representation that carries no heap cell (flattened into fields at the ABI).
    // Their observable behavior is identical to the boxed forms, so the choice is
    // invisible; only the runtime layout differs. `UnboxedRecord` (and the
    // `UnboxedProject` computation) are reserved for a future named-field ABI;
    // elaboration currently lowers a record positionally to `UnboxedTuple` and its
    // projection to a product `Case`, so those two nodes are not yet constructed.
    UnboxedTuple(Vec<Self>),
    UnboxedRecord(Vec<(Sym, Self)>),
}

// The numeric lane a unary negation runs in. Unary minus elaborates to a
// genuine `Comp::Neg` node, never a `0 - x` desugar, for two reasons: float
// negation must flip the sign bit and preserve signed zero (a real `fneg`, not
// `0.0 -. x` which would map `-0.0` to `+0.0`), and the numeric operator classes
// re-elaborate `-x` as the `Num` negate method, which must produce
// byte-identical Core to this node so the swap is invisible. `U64` has no lane:
// negating an unsigned value is rejected in the typechecker.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum NegLane {
    Int,
    I64,
    Float,
}

impl NegLane {
    // Stable content-hash tag, byte-identical to the old `Debug` rendering.
    #[must_use]
    pub const fn hash_tag(self) -> &'static str {
        match self {
            Self::Int => "Int",
            Self::I64 => "I64",
            Self::Float => "Float",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct HandleOp {
    pub name: Sym,
    pub params: Vec<Sym>,
    pub resume: Sym,
    pub body: Comp,
}

/// A handler's operation clauses, with the by-construction guarantee that no two
/// clauses name the same operation.
///
/// The surface allows an arbitrary clause list, so a duplicate `op` arm is
/// representable there; the type checker rejects it (`E5008`). This newtype makes
/// the invariant structural in Core: the only constructor from raw clauses,
/// [`new`](Self::new), rejects a duplicate, so no consumer can be handed a
/// handler with two clauses for one operation. That matters because the
/// interpreter resolves clauses through a map (last wins) while the free-monad
/// lowering builds a left-to-right cascade (first wins); with duplicates
/// unrepresentable, the two can never diverge, and the effect-lowering tier stays
/// unobservable. Clause order is preserved (the arms are a slice, not a map) so
/// the content hash of an unchanged handler does not move.
#[derive(Clone, Debug, PartialEq)]
pub struct CheckedHandler {
    arms: Vec<HandleOp>,
    // Parallel to `arms`: each clause's resume-usage classification, computed by
    // the constructor (the sole writer) so it can never go stale against the
    // clause body. A derived cost fact: deliberately absent from the content
    // hash, Core JSON, and store codec, which all rebuild handlers through
    // [`new`](Self::new) and so re-derive it on decode.
    uses: Vec<ResumeUse>,
}

impl Serialize for CheckedHandler {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.arms.serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for CheckedHandler {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let arms = Vec::<HandleOp>::deserialize(deserializer)?;
        Self::new(arms)
            .map_err(|name| D::Error::custom(format!("duplicate handler operation {name}")))
    }
}

impl CheckedHandler {
    /// Build from raw clauses, rejecting a duplicate operation (returning the
    /// offending op name). The single validating entry point; elaboration uses it
    /// once, after the type checker has already rejected duplicates, so a failure
    /// here is a compiler-invariant violation rather than a user error.
    ///
    /// Also classifies each clause's resume usage ([`ResumeUse`]), the stored
    /// fact every effect-lowering tier consumes instead of re-scanning bodies.
    ///
    /// # Errors
    /// Returns the duplicated operation name if two clauses share it.
    pub fn new(arms: Vec<HandleOp>) -> Result<Self, Sym> {
        let mut seen = BTreeSet::new();
        for arm in &arms {
            if !seen.insert(arm.name) {
                return Err(arm.name);
            }
        }
        let uses = arms.iter().map(resume_use::classify).collect();
        Ok(Self { arms, uses })
    }

    /// The clauses, in source order. `Deref` also exposes the slice API directly.
    #[must_use]
    pub fn arms(&self) -> &[HandleOp] {
        &self.arms
    }

    /// The stored resume-usage classification of the clause at `i` (parallel to
    /// [`arms`](Self::arms)).
    #[must_use]
    pub fn resume_use(&self, i: usize) -> ResumeUse {
        self.uses[i]
    }

    /// The clauses paired with their stored resume-usage facts.
    pub fn iter_with_use(&self) -> impl Iterator<Item = (&HandleOp, ResumeUse)> {
        self.arms.iter().zip(self.uses.iter().copied())
    }

    /// Rebuild each clause, for Core-to-Core passes that transform bodies without
    /// changing which operations are handled. The mapping preserves operation
    /// names, so the uniqueness invariant carries over from `self`; the resume
    /// classification is recomputed against the new bodies.
    #[must_use]
    pub fn rebuild(&self, f: impl FnMut(&HandleOp) -> HandleOp) -> Self {
        let arms: Vec<HandleOp> = self.arms.iter().map(f).collect();
        let uses = arms.iter().map(resume_use::classify).collect();
        Self { arms, uses }
    }
}

impl std::ops::Deref for CheckedHandler {
    type Target = [HandleOp];
    fn deref(&self) -> &Self::Target {
        &self.arms
    }
}

impl<'a> IntoIterator for &'a CheckedHandler {
    type Item = &'a HandleOp;
    type IntoIter = std::slice::Iter<'a, HandleOp>;
    fn into_iter(self) -> Self::IntoIter {
        self.arms.iter()
    }
}

// A builtin IO operation that survives elaboration as a `Comp::Io`. The output
// ops (`Print`/`PrintF`/`PrintS`/`PrintNl`) perform the `Output`/`IO` effect, the
// input ops (`ReadInt`/`ReadLine`/`Rand`) read the world, and `Srand` seeds the
// RNG. Folding the family under one `Comp` node keeps the structural Core passes
// (traversal, hashing, reuse, lint) to a single arm; the interpreter, codegen,
// and JSON serializer still switch on the op where the behavior differs.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum IoOp {
    Print,
    PrintF,
    PrintS,
    PrintNl,
    ReadInt,
    ReadLine,
    Rand,
    Srand,
}

impl IoOp {
    // Whether the op takes a single value operand (the output/seed ops) rather
    // than none (the nullary input ops). The operand count `Comp::Io` carries.
    #[must_use]
    pub const fn arity(self) -> usize {
        match self {
            Self::Print | Self::PrintF | Self::PrintS | Self::Srand => 1,
            Self::PrintNl | Self::ReadInt | Self::ReadLine | Self::Rand => 0,
        }
    }

    // The node tag, kept identical to the old per-variant `Comp::kind()` strings
    // because the content hash commits to it.
    #[must_use]
    pub const fn kind(self) -> &'static str {
        match self {
            Self::Print => "Print",
            Self::PrintF => "PrintF",
            Self::PrintS => "PrintS",
            Self::PrintNl => "PrintNl",
            Self::ReadInt => "ReadInt",
            Self::ReadLine => "ReadLine",
            Self::Rand => "Rand",
            Self::Srand => "Srand",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum Comp {
    Return(Value),
    Bind(Box<Self>, Sym, Box<Self>),
    Force(Value),
    Lam(Vec<Sym>, Box<Self>),
    App(Box<Self>, Vec<Value>),
    If(Value, Box<Self>, Box<Self>),
    Prim(CoreOp, Value, Value),
    Call(Sym, Vec<Value>),
    // A builtin IO operation and its operands: one value for the output/seed ops,
    // none for the nullary input ops (`IoOp::arity`). One node for the whole
    // family so a structural pass needs only one arm.
    Io(IoOp, Vec<Value>),
    Error(Value),
    Case(Value, Vec<(CorePat, Self)>),
    FloatBuiltin(FloatOp, Value),
    // Genuine unary negation in a numeric lane (`NegLane`); the operand is always
    // a value. Kept a distinct node rather than a `0 - x` subtract so float
    // negation lowers to a real sign-bit flip and the `Num` negate method can
    // reproduce it byte-for-byte.
    Neg(NegLane, Value),
    // Project a named field out of an unboxed record value, returning it. The
    // unboxed analogue of the single-constructor `Case` a boxed record field
    // access lowers to; the field name selects the component.
    UnboxedProject(Value, Sym),
    Do(Sym, Vec<Value>),
    Handle {
        body: Box<Self>,
        return_var: Option<Sym>,
        return_body: Option<Box<Self>>,
        ops: CheckedHandler,
    },
    Mask(Vec<Sym>, Box<Self>),
    StrBuiltin(Builtin, Vec<Value>),
    Dup(Value),
    Drop(Value),
    // Free `freed` (a cell the matched scrutinee owned and that is now dead) and
    // bind its shell as a reuse `token` scoped over `body`. The token is a binder,
    // so the cell is freed at exactly one point; only `Reuse` can name the token,
    // and it spends it building a constructor in place. Freed-once and
    // spent-at-an-allocation are thus structural properties of the term, not a
    // post-hoc check. Built by the reuse pass from a `drop` paired with a later
    // allocation; lowers to the same `prism_reuse_token` call the threaded form
    // did (it is just the `drop`+`bind` fused into one scoped node).
    WithReuse {
        token: Sym,
        freed: Value,
        body: Box<Self>,
    },
    // Build `ctor` in place over the cell held by reuse `token` (a binder of an
    // enclosing `WithReuse`). Allocation-free: it overwrites the freed shell
    // instead of calling the allocator. The token is the only operand position
    // that may name a reuse token.
    Reuse(Sym, Value),
    // A local mutable cell, the runtime form of an escape-checked `var`. The
    // effect-lowering pass `erase_local_vars` rewrites a closed var/State handler
    // into these, so a `var` loop runs as a real loop (constant stack, no
    // per-operation reification) instead of the free monad.
    //   RefNew(v)      allocate a one-field cell holding v; result owns the cell
    //   RefGet(c)      read the cell's field (an owned snapshot; c is borrowed)
    //   RefSet(c, v)   overwrite the cell's field with v in place (c borrowed, v
    //                  moved in); yields Unit
    RefNew(Value),
    RefGet(Value),
    RefSet(Value, Value),
}

impl Comp {
    #[must_use]
    pub const fn kind(&self) -> &'static str {
        match self {
            Self::Return(_) => "Return",
            Self::Bind(..) => "Bind",
            Self::Force(_) => "Force",
            Self::Lam(..) => "Lam",
            Self::App(..) => "App",
            Self::If(..) => "If",
            Self::Prim(..) => "Prim",
            Self::Call(..) => "Call",
            Self::Io(op, _) => op.kind(),
            Self::Error(_) => "Error",
            Self::Case(..) => "Case",
            Self::FloatBuiltin(..) => "FloatBuiltin",
            Self::Neg(..) => "Neg",
            Self::UnboxedProject(..) => "UnboxedProject",
            Self::Do(..) => "Do",
            Self::Handle { .. } => "Handle",
            Self::Mask(..) => "Mask",
            Self::StrBuiltin(..) => "StrBuiltin",
            Self::Dup(_) => "Dup",
            Self::Drop(_) => "Drop",
            Self::WithReuse { .. } => "WithReuse",
            Self::Reuse(..) => "Reuse",
            Self::RefNew(_) => "RefNew",
            Self::RefGet(_) => "RefGet",
            Self::RefSet(..) => "RefSet",
        }
    }

    /// A pre-lowering effect node (`Do`, `Handle`, `Mask`). Effect lowering
    /// eliminates every one of these, so their presence in post-lowering Core is
    /// a compiler bug. The single canonical membership test for this family; the
    /// stage lint reads it rather than re-listing the variants.
    #[must_use]
    pub const fn is_effect_node(&self) -> bool {
        matches!(self, Self::Do(..) | Self::Handle { .. } | Self::Mask(..))
    }

    /// A post-lowering runtime node: the reference-counting forms (`Dup`,
    /// `Drop`), the in-place reuse forms (`WithReuse`, `Reuse`), and the local
    /// mutable cell forms (`RefNew`, `RefGet`, `RefSet`). Effect lowering (and the
    /// rc/reuse passes that run after it) introduce these, so their presence in
    /// pre-lowering Core is a compiler bug. The single canonical membership test
    /// for this family; the stage lint reads it rather than re-listing the
    /// variants.
    #[must_use]
    pub const fn is_runtime_node(&self) -> bool {
        matches!(
            self,
            Self::Dup(_)
                | Self::Drop(_)
                | Self::WithReuse { .. }
                | Self::Reuse(..)
                | Self::RefNew(_)
                | Self::RefGet(_)
                | Self::RefSet(..)
        )
    }
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct CoreFn {
    pub name: Sym,
    pub params: Vec<Sym>,
    pub body: Comp,
    /// How many of the leading `params` are dictionary parameters prepended by
    /// class-constraint elaboration. Carried as data on the binder rather than
    /// recovered by sniffing the `_c{i}` param names downstream, so a renaming of
    /// the convention cannot silently break dictionary specialization. Zero for
    /// every function without a constraint context.
    pub dict_arity: usize,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Core {
    pub fns: Vec<CoreFn>,
}

// Whole-program Core, tagged by its position across the effect-lowering seam so
// the pipeline cannot route a program to the wrong consumer. Both wrappers are
// thin newtypes over the same `Core`; they carry no extra data and `Deref` to
// `&Core`, so a pass inside a stage unwraps for free. Their only job is to make
// wrong-stage *routing* a type error at the handful of seam signatures that name
// them: effect lowering consumes an `ElaboratedCore` and yields a `LoweredCore`,
// native codegen accepts only `LoweredCore`, and the store commit / content
// hasher accept only `ElaboratedCore`. A wrong-stage *node* inside a tree stays
// the stage lint's job (`Comp::is_effect_node` / `is_runtime_node`).

/// Post-elaboration, pre-effect-lowering whole-program Core.
///
/// Still carries the effect nodes (`Do`, `Handle`, `Mask`) and no runtime nodes.
/// The interpreter evaluates it directly and the store / content hasher observe
/// it (identity is a property of the elaborated term, independent of the
/// optimizer level).
#[derive(Clone, Debug)]
pub struct ElaboratedCore(pub Core);

/// Post-effect-lowering whole-program Core. The effect nodes are gone; the
/// runtime nodes (`Dup`, `Drop`, `WithReuse`, `Reuse`, `RefNew`/`RefGet`/
/// `RefSet`) may appear. Only native codegen consumes it.
#[derive(Clone, Debug)]
pub struct LoweredCore(pub Core);

impl Deref for ElaboratedCore {
    type Target = Core;
    fn deref(&self) -> &Core {
        &self.0
    }
}

impl Deref for LoweredCore {
    type Target = Core;
    fn deref(&self) -> &Core {
        &self.0
    }
}

// Functions reachable from main. Dead code must not steer whole-program
// decisions (effect lowering inspects every body for ops), so lowering and
// emission both restrict themselves to this set. Free variables are unioned in
// because a function can flow first-class as a bare name (a dictionary field)
// without appearing as a call head.
#[must_use]
pub fn reachable_fns(core: &Core) -> BTreeSet<Sym> {
    let fn_map: BTreeMap<Sym, &CoreFn> = core.fns.iter().map(|f| (f.name, f)).collect();
    let mut visited: BTreeSet<Sym> = BTreeSet::new();
    let mut queue = vec![Sym::new(ENTRY_POINT)];
    while let Some(name) = queue.pop() {
        if visited.contains(&name) {
            continue;
        }
        visited.insert(name);
        if let Some(f) = fn_map.get(&name) {
            calls_in(&f.body, &mut queue);
            queue.extend(
                super::fv::comp(&f.body)
                    .into_iter()
                    .filter(|n| fn_map.contains_key(n)),
            );
        }
    }
    visited
}

// Every direct call head anywhere in `c` (including inside thunks, lambdas, and
// handler clauses), in occurrence order. A bare function name flowing
// first-class (a dictionary field) is not a call head; `reachable_fns` unions
// those in via `fv`.
pub(crate) fn calls_in(c: &Comp, out: &mut Vec<Sym>) {
    struct Calls<'a>(&'a mut Vec<Sym>);
    impl Visit for Calls<'_> {
        fn visit_comp(&mut self, c: &Comp) {
            if let Comp::Call(name, args) = c {
                self.0.push(*name);
                for a in args {
                    self.visit_value(a);
                }
            } else {
                self.descend_comp(c);
            }
        }
    }
    Visit::visit_comp(&mut Calls(out), c);
}

#[cfg(test)]
mod reachability_tests {
    use super::{reachable_fns, Comp, Core, CoreFn, Value};
    use crate::names::ENTRY_POINT;
    use crate::sym::Sym;

    fn function(name: &str, body: Comp) -> CoreFn {
        CoreFn {
            name: Sym::new(name),
            params: Vec::new(),
            body,
            dict_arity: 0,
        }
    }

    #[test]
    fn a_local_binder_does_not_reach_a_same_named_function() {
        let local = Sym::new("arg");
        let core = Core {
            fns: vec![
                function(
                    ENTRY_POINT,
                    Comp::Bind(
                        Box::new(Comp::Return(Value::Int(1))),
                        local,
                        Box::new(Comp::Return(Value::Var(local))),
                    ),
                ),
                function("arg", Comp::Return(Value::Int(2))),
            ],
        };
        assert_eq!(
            reachable_fns(&core),
            std::iter::once(Sym::new(ENTRY_POINT)).collect()
        );
    }

    #[test]
    fn a_free_function_value_is_reachable() {
        let helper = Sym::new("helper");
        let core = Core {
            fns: vec![
                function(ENTRY_POINT, Comp::Return(Value::Var(helper))),
                function("helper", Comp::Return(Value::Int(2))),
            ],
        };
        assert_eq!(
            reachable_fns(&core),
            [Sym::new(ENTRY_POINT), helper].into_iter().collect()
        );
    }
}

#[cfg(test)]
mod tag_tests {
    use super::{CoreOp, IoOp, NegLane};
    use std::collections::BTreeSet;

    // Assert a frozen `variant -> tag` table: every entry's `tag` reproduces its
    // frozen spelling and no two variants share one. The content hash commits to
    // these strings, so a variant rename that also touched the tag method would
    // silently move every affected definition's hash; freezing the spelling here
    // turns that into a test failure instead. The method's own `match` is
    // exhaustive, so a new variant cannot ship without a tag; this checks that tag.
    fn frozen<T: Copy>(table: &[(T, &str)], tag: impl Fn(T) -> &'static str) {
        let mut seen = BTreeSet::new();
        for &(variant, spelling) in table {
            assert_eq!(
                tag(variant),
                spelling,
                "hash tag drifted from frozen spelling"
            );
            assert!(
                seen.insert(spelling),
                "two variants share the hash tag {spelling}"
            );
        }
    }

    #[test]
    fn core_op_hash_tags_are_frozen() {
        frozen(
            &[
                (CoreOp::Add, "Add"),
                (CoreOp::Sub, "Sub"),
                (CoreOp::Mul, "Mul"),
                (CoreOp::Div, "Div"),
                (CoreOp::Rem, "Rem"),
                (CoreOp::Eq, "Eq"),
                (CoreOp::Ne, "Ne"),
                (CoreOp::Lt, "Lt"),
                (CoreOp::Le, "Le"),
                (CoreOp::Gt, "Gt"),
                (CoreOp::Ge, "Ge"),
                (CoreOp::Addf, "Addf"),
                (CoreOp::Subf, "Subf"),
                (CoreOp::Mulf, "Mulf"),
                (CoreOp::Divf, "Divf"),
                (CoreOp::Eqf, "Eqf"),
                (CoreOp::Nef, "Nef"),
                (CoreOp::Ltf, "Ltf"),
                (CoreOp::Lef, "Lef"),
                (CoreOp::Gtf, "Gtf"),
                (CoreOp::Gef, "Gef"),
            ],
            CoreOp::hash_tag,
        );
    }

    #[test]
    fn neg_lane_hash_tags_are_frozen() {
        frozen(
            &[
                (NegLane::Int, "Int"),
                (NegLane::I64, "I64"),
                (NegLane::Float, "Float"),
            ],
            NegLane::hash_tag,
        );
    }

    #[test]
    fn io_op_kinds_are_frozen() {
        frozen(
            &[
                (IoOp::Print, "Print"),
                (IoOp::PrintF, "PrintF"),
                (IoOp::PrintS, "PrintS"),
                (IoOp::PrintNl, "PrintNl"),
                (IoOp::ReadInt, "ReadInt"),
                (IoOp::ReadLine, "ReadLine"),
                (IoOp::Rand, "Rand"),
                (IoOp::Srand, "Srand"),
            ],
            IoOp::kind,
        );
    }
}

#[cfg(test)]
mod checked_handler_tests {
    use super::{CheckedHandler, Comp, HandleOp, Value};
    use crate::sym::Sym;

    fn arm(op: &str) -> HandleOp {
        HandleOp {
            name: Sym::new(op),
            params: vec![],
            resume: Sym::new("k"),
            body: Comp::Return(Value::Unit),
        }
    }

    // The invariant the newtype exists to enforce: a duplicate operation clause
    // is unconstructable. This is what makes the effect-lowering tier
    // unobservable for handlers, since no consumer can be handed two clauses for
    // one operation to resolve differently.
    #[test]
    fn new_rejects_a_duplicate_operation() {
        assert_eq!(
            CheckedHandler::new(vec![arm("get"), arm("put"), arm("get")]),
            Err(Sym::new("get"))
        );
        let ok = CheckedHandler::new(vec![arm("get"), arm("put")]).expect("distinct ops");
        assert_eq!(ok.arms().len(), 2);
    }
}
