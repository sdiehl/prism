use std::{
    collections::{BTreeMap, BTreeSet},
    fmt,
    mem::swap,
};

use prism_common::sym::Sym;
use prism_syntax::ast::{Core as CorePhase, Fip, Program};
use prism_syntax::coeffect::CoeffectFact;
use prism_syntax::kw::{AT, FBIP, FIP};
use prism_syntax::names;

use crate::core::builtins::{builtin, BuiltinKind};
use crate::core::cbpv::{Comp, Core, CoreFn, CorePat, HandleOp, Value};
use crate::core::fv::rebound;
use crate::core::tailrec::{recursive_calls, scc_of, scc_of_calls, TailClass};
use crate::core::traverse::Visit;
use crate::types::{CtorInfo, DeclInfo, Type};

use super::Sigs;

// Usage-claim checking, factored as one claim vector. The `fip` keyword is not
// its own discipline but a bundle of three independent facts, each also
// claimable standalone as a row fact and each proven by its own drive at the
// phase it is a property of. Every drive iterates keyword-annotated and
// row-claimed functions together, so the two spellings cannot drift apart:
// `fip` accepts and rejects exactly like `@ {bounded_stack, linear, noalloc}`,
// and `fbip` exactly like `@ noalloc`, differing only in the diagnostic
// vocabulary.
//
// - Allocation budget (`@ noalloc`, `fbip`, and the budget half of `fip`),
//   over the reuse-lowered core (`check_alloc` below). A bare
//   `Value::Ctor`/`Value::Tuple` is a fresh heap cell here (`prism_alloc(0)`
//   mallocs and bumps the live count even for a nullary constructor), so the
//   only allocation-free way to build is `Comp::Reuse` over a dropped cell.
//   The walk infers the budget a body needs: each fresh cell costs one,
//   sequencing adds, branching takes the worst path, and every call site
//   charges the callee's full declared budget, recursive calls included, so a
//   path that continues the recursion must itself allocate nothing and the
//   per-call claim holds over the whole dynamic extent. The inferred budget
//   must not exceed the declared one (a bare keyword declares zero, which
//   keeps the historical fully-in-place meaning). An annotated function may
//   only call functions carrying a zero-allocation certificate at some budget
//   (`fip` or `fbip` at any grade) or allocation-free prims, else an
//   unannotated callee's allocation would silently break the guarantee. The
//   callee rule is budget-only: a `fip` caller's linearity and stack closure
//   are enforced by their own drives below, not smuggled into this one.
// - Linearity (`@ linear`, and one of `fip`'s facts), over the RAW pre-RC core
//   (`check_linear`): each owned, non-immediate binder is consumed at most
//   once per path, closed through direct calls. Linearity is a property of the
//   source program; the dup/drop the RC pass later inserts to realize linear
//   consumption over a unique cell are an implementation detail and are not
//   counted against it. A scalar binder is exempt (a `dup` on an immediate is
//   a runtime no-op).
// - Bounded stack (`@ bounded_stack`, and one of `fip`'s facts), over the
//   reuse-lowered core (`check_bounded_stack`): every recursive call within
//   the call-graph SCC must be a tail call or a TRMC-eligible tail (modulo one
//   constructor field or one addition), classified by the shared
//   `core::tailrec` so acceptance never outruns what codegen loops, with the
//   fact closed over SCC members and direct callees.
//
// `fbip` is the weaker keyword: the allocation fact alone, so it may
// duplicate, recurse non-tail, and run in unbounded stack.

pub type Fips = BTreeMap<Sym, Fip>;

/// Which spelling family fired a drive's rule.
///
/// Selects how the driver seam renders the user-facing claim: the keyword
/// bundle (`fip`/`fbip`, whose exact rendering lives on the declaration) or
/// the standalone row fact, which the user wrote verbatim.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ClaimOrigin {
    Keyword,
    RowClaim,
}

// A checked spelling and its diagnostic family travel together. Keeping the
// row as a fact avoids retyping the canonical coeffect vocabulary here.
#[derive(Clone, Copy)]
enum ClaimSpelling {
    Keyword(&'static str),
    Row(CoeffectFact),
}

impl ClaimSpelling {
    fn render(self) -> String {
        match self {
            Self::Keyword(keyword) => keyword.to_string(),
            Self::Row(fact) => format!("{AT} {fact}"),
        }
    }

    const fn origin(self) -> ClaimOrigin {
        match self {
            Self::Keyword(_) => ClaimOrigin::Keyword,
            Self::Row(_) => ClaimOrigin::RowClaim,
        }
    }

    fn stack_weakening(self) -> String {
        match self {
            Self::Keyword(_) => format!("annotate it `{FBIP}`"),
            Self::Row(fact) => format!("drop the `{AT} {fact}` claim"),
        }
    }
}

/// Why a drive rejected a usage claim, as data.
///
/// Each variant is one failing rule and maps to its own stable diagnostic
/// code at the driver seam; the fields carry exactly what the message needs,
/// and [`ClaimErrorKind::detail`] renders them once, here, so the text has a
/// single home.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ClaimErrorKind {
    /// The inferred allocation budget exceeds the declared one; `detail` is
    /// the pre-rendered witness report (the budgets plus the sites that make
    /// up the difference, which name allocation-walk internals private to the
    /// drive).
    AllocBudgetExceeded { detail: String },
    /// A claimed-linear function declares a `borrow` parameter.
    BorrowedParam,
    /// An owned, non-immediate binder is consumed more than once on a path.
    DuplicatesValue,
    /// An owned value flows into a call carrying no linearity certificate.
    LinearityNotClosed { reason: String },
    /// A recursive call in non-tail position grows the stack per element.
    /// `note` explains a recursion group enlarged by a first-class function
    /// value rather than a direct-call cycle, when that is what happened.
    NonTailRecursion {
        weaken: String,
        note: Option<String>,
    },
    /// The body mixes cons- and add-TRMC; codegen loops one shape per function.
    TrmcShapesMixed { weaken: String },
    /// TRMC paired with a mutual call; codegen loops only direct self-TRMC.
    TrmcWithMutualCall { weaken: String },
    /// A mutually recursive SCC member carries no bounded-stack certificate.
    SccMemberUncertified { member: Sym },
    /// A call in the body leaves the bounded-stack-certified tree.
    StackNotClosed { reason: String },
    /// A named callable flowing into a parameter demanding the allocation
    /// certificate carries no zero-allocation proof over its call tree.
    CallableUncertified {
        supplied: Sym,
        callee: Sym,
        slot: Sym,
    },
    /// A callable flowing into a parameter demanding the allocation
    /// certificate cannot be traced to a named function or a certified
    /// parameter, so no proof is available.
    CallableOpaque { callee: Sym, slot: Sym },
}

impl ClaimErrorKind {
    /// The reason clause: everything after ``marked `claim` but`` in the
    /// drive's own words, shared verbatim by the seam's reframed diagnostic.
    #[must_use]
    pub fn detail(&self) -> String {
        match self {
            Self::AllocBudgetExceeded { detail } => detail.clone(),
            Self::BorrowedParam => "is not linear (has a borrowed parameter)".to_string(),
            Self::DuplicatesValue => "is not linear (duplicates a value)".to_string(),
            Self::LinearityNotClosed { reason } => {
                format!("linearity is not closed over its call tree: {reason}")
            }
            Self::NonTailRecursion { weaken, .. } => format!(
                "recurses in non-tail position (one stack frame per element); make the \
                 recursive call a tail call or a tail under a single constructor / addition, \
                 or {weaken}"
            ),
            Self::TrmcShapesMixed { weaken } => format!(
                "mixes tail-modulo-constructor and tail-modulo-addition recursion; codegen \
                 loops only one shape per function, so split it or {weaken}"
            ),
            Self::TrmcWithMutualCall { weaken } => format!(
                "pairs tail-modulo-constructor/addition recursion with a mutually recursive \
                 call; codegen loops only direct self-TRMC, so make the mutual call a plain \
                 tail call or {weaken}"
            ),
            Self::SccMemberUncertified { member } => format!(
                "is mutually recursive with `{member}`, which carries no bounded-stack \
                 certificate; every member of the recursion must be certified \
                 (`@ bounded_stack` or `fip`)"
            ),
            Self::StackNotClosed { reason } => {
                format!("its call tree is not certified: {reason}")
            }
            Self::CallableUncertified {
                supplied,
                callee,
                slot,
            } => format!(
                "passes `{supplied}` into parameter `{slot}` of `{callee}`, whose function type \
                 demands `@ noalloc`, but the call tree of `{supplied}` is not proven \
                 allocation-free; certify `{supplied}` (`@ noalloc`, `fip`, or `fbip`) or make \
                 its body allocation-free"
            ),
            Self::CallableOpaque { callee, slot } => format!(
                "supplies a value for parameter `{slot}` of `{callee}`, whose function type \
                 demands `@ noalloc`, but the value cannot be traced to a named function or a \
                 certified parameter; name the callable as a top-level function so its \
                 certificate can be checked"
            ),
        }
    }

    /// The explanatory note accompanying the failure, if the rule recorded one.
    #[must_use]
    pub fn note(&self) -> Option<&str> {
        match self {
            Self::NonTailRecursion { note, .. } => note.as_deref(),
            _ => None,
        }
    }
}

/// A rejected usage claim: the claiming function, the spelling the rule fired
/// under, and the failing rule with its facts.
#[derive(Clone, Debug)]
pub struct ClaimError {
    pub fname: Sym,
    pub spelled: String,
    pub origin: ClaimOrigin,
    pub kind: Box<ClaimErrorKind>,
}

impl fmt::Display for ClaimError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "function `{}` is marked `{}` but {}",
            self.fname,
            self.spelled,
            self.kind.detail()
        )?;
        if let Some(note) = self.kind.note() {
            write!(f, "\nnote: {note}")?;
        }
        Ok(())
    }
}

#[must_use]
pub fn fip_annots(prog: &Program<CorePhase>) -> Fips {
    prog.fns
        .iter()
        .filter_map(|d| {
            // `@ noalloc` is the allocation-certificate spelling of the `fbip`
            // usage check: same zero-allocation check, no linearity or
            // bounded-stack requirement.
            // An explicit `fip`/`fbip` keyword (the stronger discipline) wins.
            let want = match d.fip {
                Fip::No if d.no_alloc => Fip::Fbip(0),
                other => other,
            };
            (want != Fip::No).then(|| (d.name.clone().into(), want))
        })
        .collect()
}

/// The set of functions claiming standalone `@ bounded_stack`.
///
/// Each must run, with its whole certified direct call tree, in bounded
/// stack. Allocation and linearity are unconstrained; a `fip` keyword already
/// proves the fact through its own check, so the claim adds nothing there.
#[must_use]
pub fn bounded_stack_annots(prog: &Program<CorePhase>) -> BTreeSet<Sym> {
    prog.fns
        .iter()
        .filter(|d| d.bounded_stack)
        .map(|d| d.name.clone().into())
        .collect()
}

/// The set of functions claiming standalone `@ linear`.
///
/// Each must consume every owned non-immediate binder at most once per path,
/// with the fact closed through direct calls; allocation and stack growth are
/// unconstrained. A `fip` keyword already proves the fact through its own
/// check, so the claim adds nothing there.
#[must_use]
pub fn linear_annots(prog: &Program<CorePhase>) -> BTreeSet<Sym> {
    prog.fns
        .iter()
        .filter(|d| d.linear)
        .map(|d| d.name.clone().into())
        .collect()
}

/// The set of `replayable`-annotated functions: each must infer a row within the
/// recordable capabilities plus the deterministic builtin effects, checked in the
/// driver against the inferred effects.
#[must_use]
pub fn replayable_annots(prog: &Program<CorePhase>) -> BTreeSet<Sym> {
    prog.fns
        .iter()
        .filter(|d| d.replayable)
        .map(|d| d.name.clone().into())
        .collect()
}

// Prims and builtins that allocate no heap cell, so an annotated body may call
// them. Conservative: only arithmetic/comparison/IO primitives that the backend
// lowers to immediates or a runtime call returning an immediate. Anything that
// builds a constructor (e.g. string ops returning a boxed Str) is excluded.
fn alloc_free_prim(name: &str) -> bool {
    matches!(
        builtin(name),
        Some((
            _,
            BuiltinKind::Print | BuiltinKind::Println | BuiltinKind::Error | BuiltinKind::Srand
        ))
    )
}

// The number of concrete allocation witnesses reported per rejected function. A
// body with many allocation sites yields a readable diagnostic listing the first
// few in evaluation order; the remainder is summarized as a trailing count.
const ALLOC_WITNESS_LIMIT: usize = 3;

/// One point of the allocation-grade lattice.
///
/// `Bounded(n)` is an at-most-`n` budget of fresh heap cells per call;
/// `Finite` claims each call allocates finitely with no uniform bound;
/// `Unlimited` claims nothing. Every `Bounded` sits below `Finite`, which sits
/// below `Unlimited`. Sequencing adds (saturating into the tops), branching
/// joins to the worst path.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Alloc {
    Bounded(u64),
    Finite,
    Unlimited,
}

impl Alloc {
    const ZERO: Self = Self::Bounded(0);

    // Sequential composition: budgets add; a top absorbs everything at or
    // below it. Saturating, so a pathological chain cannot wrap into a small
    // (falsely acceptable) budget.
    #[must_use]
    pub const fn add(self, other: Self) -> Self {
        match (self, other) {
            (Self::Unlimited, _) | (_, Self::Unlimited) => Self::Unlimited,
            (Self::Finite, _) | (_, Self::Finite) => Self::Finite,
            (Self::Bounded(a), Self::Bounded(b)) => Self::Bounded(a.saturating_add(b)),
        }
    }

    // Branch join: the worst path bounds them all.
    #[must_use]
    pub const fn join(self, other: Self) -> Self {
        match (self, other) {
            (Self::Unlimited, _) | (_, Self::Unlimited) => Self::Unlimited,
            (Self::Finite, _) | (_, Self::Finite) => Self::Finite,
            (Self::Bounded(a), Self::Bounded(b)) => {
                if a >= b {
                    Self::Bounded(a)
                } else {
                    Self::Bounded(b)
                }
            }
        }
    }

    // The lattice order: `a.le(b)` when a body graded `a` satisfies a claim
    // graded `b`.
    #[must_use]
    pub const fn le(self, other: Self) -> bool {
        match (self, other) {
            (_, Self::Unlimited) => true,
            (Self::Unlimited, _) => false,
            (_, Self::Finite) => true,
            (Self::Finite, _) => false,
            (Self::Bounded(a), Self::Bounded(b)) => a <= b,
        }
    }

    const fn cells(n: u64) -> Self {
        Self::Bounded(n)
    }
}

/// Whether discipline `a` may stand wherever discipline `b` is demanded.
///
/// That holds when `a` allocates no more than `b` allows and claims every
/// structural property (`fip`'s linearity and bounded stack) that `b` claims.
/// The order is genuinely partial, not total: `fip(1)` and `fbip` are
/// incomparable, since one allocates more while the other claims less
/// structure.
#[must_use]
pub const fn subsumes(a: Fip, b: Fip) -> bool {
    match (a, b) {
        // An undemanding position accepts anything; an undisciplined function
        // satisfies nothing but that, and `fbip` never claims `fip`'s
        // structure at any budget.
        (_, Fip::No) => true,
        (Fip::No, _) | (Fip::Fbip(_), Fip::Fip(_)) => false,
        (Fip::Fbip(m), Fip::Fbip(n)) | (Fip::Fip(m), Fip::Fip(n) | Fip::Fbip(n)) => m <= n,
    }
}

// A concrete reason an annotated body is not allocation-free, recorded in
// evaluation order. Every rejection the allocation walk can raise maps to one of
// these; the driver renders them into the user diagnostic. The set is exactly the
// nodes that materialize a heap cell (`Ctor`/`Tuple`/`Closure`) or admit an
// uncertified callee (`UncertifiedCall`/`IndirectCall`/`Builtin`); no other Core
// node allocates under this check.
enum AllocWitness {
    // A fresh constructor cell built outside a `reuse` token.
    Ctor(Sym),
    // A fresh tuple cell.
    Tuple,
    // A closure cell for a materialized lambda/thunk value.
    Closure,
    // A call to a user function carrying no zero-allocation certificate at any
    // budget: the callee may allocate inside the caller's call tree.
    UncertifiedCall(Sym),
    // A call to a certified callee with a nonzero declared budget: the site
    // charges that budget in full (recursive calls included), so it is an
    // allocation site of the caller's inferred budget.
    BudgetedCallee(Sym, u32),
    // An indirect call through a first-class function value: no callee
    // certificate is available at the call site.
    IndirectCall,
    // A primitive/builtin outside the allocation-free allow-list.
    Builtin(Sym),
    // A performed `alloc` (the arena allocation effect). Serviced by a
    // `with_arena` handler out of a bump region, but still a fresh cell: arena
    // allocation is cheap, not absent, so `@ noalloc` must reject it too.
    AllocOp,
}

// Collects up to `ALLOC_WITNESS_LIMIT` witnesses while counting the total, so the
// diagnostic shows the first few in evaluation order and summarizes the rest.
struct Witnesses {
    seen: Vec<AllocWitness>,
    total: usize,
}

impl Witnesses {
    const fn new() -> Self {
        Self {
            seen: Vec::new(),
            total: 0,
        }
    }

    fn push(&mut self, w: AllocWitness) {
        if self.seen.len() < ALLOC_WITNESS_LIMIT {
            self.seen.push(w);
        }
        self.total += 1;
    }

    // Witnesses beyond the reported prefix, summarized as "and N more".
    const fn extra(&self) -> usize {
        self.total - self.seen.len()
    }
}

#[derive(Clone, Copy)]
enum ValueHead {
    Fresh,
    Reused,
}

enum AllocFrame<'a> {
    Comp(&'a Comp),
    Value(&'a Value, ValueHead),
    Reduce(AllocReduce),
}

enum AllocReduce {
    Add {
        children: usize,
        base: Alloc,
    },
    Join {
        children: usize,
    },
    Indirect {
        children: usize,
        certified: bool,
    },
    Handler {
        base_children: usize,
        clauses: usize,
    },
}

fn reduce_alloc(results: &mut Vec<Alloc>, children: usize, base: Alloc) -> Alloc {
    (0..children).fold(base, |grade, _| {
        grade.add(
            results
                .pop()
                .expect("allocation worklist reducer has one result per child"),
        )
    })
}

fn push_alloc_values<'a, I>(work: &mut Vec<AllocFrame<'a>>, values: I, base: Alloc)
where
    I: DoubleEndedIterator<Item = &'a Value> + ExactSizeIterator,
{
    work.push(AllocFrame::Reduce(AllocReduce::Add {
        children: values.len(),
        base,
    }));
    work.extend(
        values
            .rev()
            .map(|value| AllocFrame::Value(value, ValueHead::Fresh)),
    );
}

// Walk an annotated body in evaluation order, recording every allocation
// witness (bounded by the sink) and returning the inferred allocation grade:
// each fresh cell costs one, sequencing adds, branching joins to the worst
// path, and every call charges the callee's full declared budget (recursive
// calls included, so a path that continues the recursion must itself allocate
// nothing for the per-call claim to hold over the whole dynamic extent).
// The callee rule is budget-only: any zero-allocation certificate (`fip` or
// `fbip` at any grade) is acceptable, since the caller's other facts are
// enforced by their own drives, never by this walk. The walk records a witness
// exactly when it contributes a nonzero grade, so a body is rejected iff at
// least one witness is recorded beyond the declared budget.
fn comp_alloc(
    c: &Comp,
    fips: &Fips,
    users: &BTreeSet<Sym>,
    newtypes: &BTreeSet<Sym>,
    certified: &BTreeSet<Sym>,
    out: &mut Witnesses,
) -> Alloc {
    let mut work = vec![AllocFrame::Comp(c)];
    let mut results = Vec::new();
    while let Some(frame) = work.pop() {
        match frame {
            AllocFrame::Value(value, head) => match value {
                Value::Ctor(name, _, fields) => {
                    let base = if matches!(head, ValueHead::Fresh) && !newtypes.contains(name) {
                        out.push(AllocWitness::Ctor(*name));
                        Alloc::cells(1)
                    } else {
                        Alloc::ZERO
                    };
                    push_alloc_values(&mut work, fields.iter(), base);
                }
                Value::Tuple(fields) => {
                    let base = if matches!(head, ValueHead::Fresh) {
                        out.push(AllocWitness::Tuple);
                        Alloc::cells(1)
                    } else {
                        Alloc::ZERO
                    };
                    push_alloc_values(&mut work, fields.iter(), base);
                }
                Value::Thunk(_) => {
                    out.push(AllocWitness::Closure);
                    results.push(Alloc::cells(1));
                }
                Value::UnboxedTuple(fields) => {
                    push_alloc_values(&mut work, fields.iter(), Alloc::ZERO);
                }
                Value::UnboxedRecord(fields) => {
                    push_alloc_values(
                        &mut work,
                        fields.iter().map(|(_, field)| field),
                        Alloc::ZERO,
                    );
                }
                _ => results.push(Alloc::ZERO),
            },
            AllocFrame::Comp(comp) => match comp {
                Comp::Reuse(_, value) => {
                    work.push(AllocFrame::Value(value, ValueHead::Reused));
                }
                Comp::WithReuse { freed, body, .. } => {
                    work.push(AllocFrame::Reduce(AllocReduce::Add {
                        children: 2,
                        base: Alloc::ZERO,
                    }));
                    work.push(AllocFrame::Comp(body));
                    work.push(AllocFrame::Value(freed, ValueHead::Fresh));
                }
                Comp::Call(callee, args) => {
                    let base = if users.contains(callee) {
                        match fips.get(callee) {
                            Some(Fip::Fip(0) | Fip::Fbip(0)) => Alloc::ZERO,
                            Some(Fip::Fip(budget) | Fip::Fbip(budget)) => {
                                out.push(AllocWitness::BudgetedCallee(*callee, *budget));
                                Alloc::Bounded((*budget).into())
                            }
                            _ => {
                                out.push(AllocWitness::UncertifiedCall(*callee));
                                Alloc::Unlimited
                            }
                        }
                    } else if alloc_free_prim(callee.as_str()) {
                        Alloc::ZERO
                    } else {
                        out.push(AllocWitness::Builtin(*callee));
                        Alloc::Unlimited
                    };
                    push_alloc_values(&mut work, args.iter(), base);
                }
                Comp::Bind(first, _, rest) => {
                    work.push(AllocFrame::Reduce(AllocReduce::Add {
                        children: 2,
                        base: Alloc::ZERO,
                    }));
                    work.push(AllocFrame::Comp(rest));
                    work.push(AllocFrame::Comp(first));
                }
                Comp::If(_, yes, no) => {
                    work.push(AllocFrame::Reduce(AllocReduce::Join { children: 2 }));
                    work.push(AllocFrame::Comp(no));
                    work.push(AllocFrame::Comp(yes));
                }
                Comp::Case(_, arms) => {
                    work.push(AllocFrame::Reduce(AllocReduce::Join {
                        children: arms.len(),
                    }));
                    work.extend(arms.iter().rev().map(|(_, body)| AllocFrame::Comp(body)));
                }
                Comp::Lam(_, body) | Comp::Mask(_, body) => {
                    work.push(AllocFrame::Comp(body));
                }
                Comp::App(callee, args) => {
                    // Only a parameter carrying `@ noalloc` certifies an
                    // indirect call; every other callee is unbounded.
                    let is_certified =
                        matches!(&**callee, Comp::Force(Value::Var(v)) if certified.contains(v));
                    work.push(AllocFrame::Reduce(AllocReduce::Indirect {
                        children: args.len() + 1,
                        certified: is_certified,
                    }));
                    work.extend(
                        args.iter()
                            .rev()
                            .map(|arg| AllocFrame::Value(arg, ValueHead::Fresh)),
                    );
                    work.push(AllocFrame::Comp(callee));
                }
                Comp::Prim(_, lhs, rhs) | Comp::RefSet(lhs, rhs) | Comp::InitAt(lhs, rhs) => {
                    push_alloc_values(&mut work, [lhs, rhs].into_iter(), Alloc::ZERO);
                }
                Comp::Return(value)
                | Comp::Force(value)
                | Comp::Error(value)
                | Comp::FloatBuiltin(_, value)
                | Comp::Neg(_, value)
                | Comp::UnboxedProject(value, _)
                | Comp::Drop(value)
                | Comp::RefNew(value)
                | Comp::RefGet(value) => {
                    work.push(AllocFrame::Value(value, ValueHead::Fresh));
                }
                Comp::Do(op, args) => {
                    let base = if op.as_str() == names::ALLOC_OP {
                        out.push(AllocWitness::AllocOp);
                        Alloc::cells(1)
                    } else {
                        Alloc::ZERO
                    };
                    push_alloc_values(&mut work, args.iter(), base);
                }
                Comp::StrBuiltin(_, args) | Comp::Io(_, args) => {
                    push_alloc_values(&mut work, args.iter(), Alloc::ZERO);
                }
                Comp::Handle {
                    body,
                    return_body,
                    ops,
                    ..
                } => {
                    work.push(AllocFrame::Reduce(AllocReduce::Handler {
                        base_children: 1 + usize::from(return_body.is_some()),
                        clauses: ops.len(),
                    }));
                    work.extend(ops.iter().rev().map(|op| AllocFrame::Comp(&op.body)));
                    if let Some(return_body) = return_body {
                        work.push(AllocFrame::Comp(return_body));
                    }
                    work.push(AllocFrame::Comp(body));
                }
                Comp::Dup(_) => results.push(Alloc::ZERO),
            },
            AllocFrame::Reduce(reduce) => {
                let grade =
                    match reduce {
                        AllocReduce::Add { children, base } => {
                            reduce_alloc(&mut results, children, base)
                        }
                        AllocReduce::Join { children } => {
                            (0..children).fold(Alloc::ZERO, |grade, _| {
                                grade.join(results.pop().expect(
                                    "allocation worklist reducer has one result per branch",
                                ))
                            })
                        }
                        AllocReduce::Indirect {
                            children,
                            certified,
                        } => {
                            let grade = reduce_alloc(&mut results, children, Alloc::ZERO);
                            if certified {
                                grade
                            } else {
                                out.push(AllocWitness::IndirectCall);
                                grade.add(Alloc::Unlimited)
                            }
                        }
                        AllocReduce::Handler {
                            base_children,
                            clauses,
                        } => {
                            // Clause invocation multiplicity is unknown, so any
                            // allocating clause makes the budget unbounded.
                            let clause_grade = (0..clauses).fold(Alloc::ZERO, |grade, _| {
                                if results
                                    .pop()
                                    .expect("allocation worklist handler has one result per clause")
                                    == Alloc::ZERO
                                {
                                    grade
                                } else {
                                    Alloc::Unlimited
                                }
                            });
                            reduce_alloc(&mut results, base_children, Alloc::ZERO).add(clause_grade)
                        }
                    };
                results.push(grade);
            }
        }
    }

    debug_assert_eq!(results.len(), 1);
    results
        .pop()
        .expect("allocation worklist produces one result for its root")
}

// Render the recorded witnesses into the drive's structured rejection. A
// zero-budget declaration keeps the historical fully-in-place phrasing; a
// graded one reports the inferred budget against the declared one, with the
// sites that make up the difference. The spelling here is the keyword
// vocabulary the shared check runs under; the driver seam renders the claim
// the user actually wrote (`@ noalloc` keeps its allocation-certificate
// framing) from the declaration.
fn render_alloc(want: Fip, fname: Sym, w: &Witnesses, inferred: Alloc) -> ClaimError {
    let mut parts: Vec<String> = w.seen.iter().map(witness_clause).collect();
    let extra = w.extra();
    if extra > 0 {
        parts.push(format!("and {extra} more"));
    }
    let clauses = parts.join("; ");
    let (spelled, detail) = if want.budget() == 0 {
        (kw(want).to_string(), format!("in `{fname}`, {clauses}"))
    } else {
        let need = match inferred {
            Alloc::Bounded(n) => format!(
                "needs an allocation budget of at least {n}, declared at most {}",
                want.budget()
            ),
            Alloc::Finite | Alloc::Unlimited => "has no bounded allocation budget".to_string(),
        };
        (
            want.render().unwrap_or_default(),
            format!("{need}: {clauses}"),
        )
    };
    ClaimError {
        fname,
        spelled,
        origin: ClaimOrigin::Keyword,
        kind: Box::new(ClaimErrorKind::AllocBudgetExceeded { detail }),
    }
}

fn witness_clause(w: &AllocWitness) -> String {
    match w {
        AllocWitness::Ctor(name) => format!("constructor `{name}` is built fresh outside `reuse`"),
        AllocWitness::Tuple => "a tuple is built fresh outside `reuse`".to_string(),
        AllocWitness::Closure => "a lambda is materialized as a fresh closure cell".to_string(),
        AllocWitness::UncertifiedCall(callee) => {
            format!(
                "call to `{callee}` may allocate (`{callee}` has no zero-allocation certificate)"
            )
        }
        AllocWitness::BudgetedCallee(callee, budget) => {
            format!("call to `{callee}` charges its declared allocation budget of {budget}")
        }
        AllocWitness::IndirectCall => {
            "an indirect call through a first-class function value has no callee certificate"
                .to_string()
        }
        AllocWitness::Builtin(name) => {
            format!("primitive `{name}` is not on the allocation-free allow-list")
        }
        AllocWitness::AllocOp => {
            "`alloc` carves a fresh cell from an arena, which is cheaper but not free".to_string()
        }
    }
}

/// Verify the allocation budget of every `fip`/`fbip`-annotated function
/// (including the `@ noalloc` claim, which expands to a zero-budget `fbip`)
/// over the reuse-lowered core.
///
/// `fips` maps a function name to its annotation, `users` is the set of
/// user-defined function names (to tell a user call from a prim/builtin), and
/// `newtypes` is the authoritative set of constructors erased by the mandatory
/// newtype representation pass. `callable_certified` maps a function name to
/// its parameters whose function type carries the callable allocation
/// certificate (`@ noalloc`): an indirect call through such a parameter is
/// allocation-free here, because the certificate's producer check proved the
/// whole call tree of every value that can flow into the slot. This drive
/// proves the allocation fact alone; a `fip` function's linearity and bounded
/// stack are proven by `check_linear` and `check_bounded_stack`.
///
/// # Errors
/// Fails with the recorded allocation witnesses when an annotated function
/// exceeds its declared budget.
pub fn check_alloc(
    core: &Core,
    fips: &Fips,
    users: &BTreeSet<Sym>,
    newtypes: &BTreeSet<Sym>,
    callable_certified: &BTreeMap<Sym, BTreeSet<Sym>>,
) -> Result<(), ClaimError> {
    for f in &core.fns {
        let Some(&want) = fips.get(&f.name) else {
            continue;
        };
        // A certified parameter's fact holds at an occurrence only when the
        // occurrence refers to the parameter. Rather than track scope through
        // the walk, keep only certified names that are among this function's
        // core binders and are never rebound in the body: such a name refers
        // to the parameter at every occurrence, while a rebound one
        // conservatively loses its certificate (the shadowing binder carries
        // no proof).
        let certified: BTreeSet<Sym> = match callable_certified.get(&f.name) {
            Some(base) if !base.is_empty() => {
                let shadowed = rebound(&f.body);
                f.params
                    .iter()
                    .filter(|p| base.contains(*p) && !shadowed.contains(*p))
                    .copied()
                    .collect()
            }
            _ => BTreeSet::new(),
        };
        let mut witnesses = Witnesses::new();
        let inferred = comp_alloc(&f.body, fips, users, newtypes, &certified, &mut witnesses);
        if !inferred.le(Alloc::Bounded(want.budget().into())) {
            return Err(render_alloc(want, f.name, &witnesses, inferred));
        }
    }
    Ok(())
}

// The spelling under which the bounded-stack rules run and the fix that
// weakens the demand, selecting the diagnostic vocabulary: the `fip` keyword
// proves bounded stack as one of its three properties (weakened by `fbip`),
// while the standalone claim demands the fact alone (weakened by dropping it).
// One rule set, two vocabularies, so the shared checker never acquires a fork.
struct StackClaimWords {
    spelling: ClaimSpelling,
}

impl StackClaimWords {
    fn err(&self, fname: Sym, kind: ClaimErrorKind) -> ClaimError {
        ClaimError {
            fname,
            spelled: self.spelling.render(),
            origin: self.spelling.origin(),
            kind: Box::new(kind),
        }
    }
}

const FIP_STACK_WORDS: StackClaimWords = StackClaimWords {
    spelling: ClaimSpelling::Keyword(FIP),
};

const BOUNDED_STACK_WORDS: StackClaimWords = StackClaimWords {
    spelling: ClaimSpelling::Row(CoeffectFact::BoundedStack),
};

// Bounded-stack rule (the third FP^2 property, and the whole standalone
// `@ bounded_stack` recursion rule): a function runs in O(1) stack iff every
// recursive call inside its own frame is a loop, not a frame. Compute the SCC
// (mutual recursion counts) and classify each in-group call with the shared
// `tailrec`: a `NonTail` recursive call grows the stack one frame per element
// and is rejected. Codegen lowers at most one TRMC shape per function and only
// for direct self-recursion, so a body mixing cons- and add-TRMC, or one that
// pairs TRMC with a mutual call, is rejected too: those are exactly the shapes
// the backend would leave as real recursion.
fn bounded_stack(
    f: &CoreFn,
    core: &Core,
    users: &BTreeSet<Sym>,
    words: &StackClaimWords,
) -> Result<(), ClaimError> {
    let group = scc_of(core, users, f.name);
    // The direct-call SCC is a subset used only to explain a rejection: a member
    // missing from it sits in the group because a function flows as a value, not
    // because of a real call cycle.
    let call_group = scc_of_calls(core, users, f.name);
    let (mut cons, mut add, mut mutual) = (false, false, false);
    for (g, cls) in recursive_calls(&f.body, f.name, f.params.len(), &group) {
        match cls {
            TailClass::NonTail => return Err(nontail_err(f.name, g, &call_group, words)),
            TailClass::TrmcCons => cons = true,
            TailClass::TrmcAdd => add = true,
            TailClass::Tail => {}
        }
        mutual |= g != f.name;
    }
    if cons && add {
        return Err(words.err(
            f.name,
            ClaimErrorKind::TrmcShapesMixed {
                weaken: words.spelling.stack_weakening(),
            },
        ));
    }
    if (cons || add) && mutual {
        return Err(words.err(
            f.name,
            ClaimErrorKind::TrmcWithMutualCall {
                weaken: words.spelling.stack_weakening(),
            },
        ));
    }
    Ok(())
}

fn nontail_err(
    fname: Sym,
    callee: Sym,
    call_group: &BTreeSet<Sym>,
    words: &StackClaimWords,
) -> ClaimError {
    // When the non-tail callee is in the recursion group only via a first-class
    // reference (not a direct-call cycle), the discipline can feel surprising:
    // capturing a function as a value, not calling it back, is what enlarged the
    // group. Name that so the fix (drop the capture, or weaken the claim) is clear.
    let weaken = words.spelling.stack_weakening();
    let note = (callee != fname && !call_group.contains(&callee)).then(|| {
        format!(
            "`{callee}` is in `{fname}`'s tail-recursion group only because a function flows \
             as a first-class value somewhere in the cycle, not through direct calls; if they \
             do not actually recurse through each other, avoid capturing the function as a \
             value (call it directly) or {weaken}"
        )
    });
    words.err(fname, ClaimErrorKind::NonTailRecursion { weaken, note })
}

// Whether `g` carries a stack certificate a `@ bounded_stack` caller may rely
// on: the standalone claim itself, or the `fip` keyword (whose own check
// proves bounded stack at every budget). `fbip` and `@ noalloc` are explicitly
// not certificates: both permit unbounded recursion depth.
fn stack_certified(g: Sym, claims: &BTreeSet<Sym>, fips: &Fips) -> bool {
    claims.contains(&g) || matches!(fips.get(&g), Some(Fip::Fip(_)))
}

// Scan a claimed body for the first call that leaves the certified tree: a
// direct call to an uncertified user function, or an indirect call through a
// first-class function value (no callee certificate exists at the site until
// callable types carry the corresponding contract). Thunk and handler bodies
// are scanned too: a closure built here may be forced within this frame's
// dynamic extent, so the conservative walk covers every nested body. Non-user
// callees (prims and builtins) are constant-stack by assumption: the runtime
// implements them without recursion proportional to the input structure.
struct CalleeScan<'a> {
    claims: &'a BTreeSet<Sym>,
    fips: &'a Fips,
    users: &'a BTreeSet<Sym>,
    first: Option<String>,
}

impl Visit for CalleeScan<'_> {
    fn comp(&mut self, c: &Comp) -> bool {
        if self.first.is_some() {
            return false;
        }
        match c {
            Comp::Call(g, _)
                if self.users.contains(g) && !stack_certified(*g, self.claims, self.fips) =>
            {
                self.first = Some(format!(
                    "call to `{g}`, which carries no bounded-stack certificate; \
                     certify `{g}` (`@ bounded_stack` or `fip`)"
                ));
            }
            Comp::App(..) => {
                self.first = Some(
                    "an indirect call through a first-class function value, \
                     which has no callee certificate"
                        .to_string(),
                );
            }
            _ => {}
        }
        self.first.is_none()
    }
}

/// Verify the bounded-stack fact of every claiming function (the standalone
/// `@ bounded_stack` claim, and one of the `fip` keyword's facts) over the
/// reuse-lowered core.
///
/// The function's own recursion must lower as real tail or supported TRMC
/// loops, every member of its mutually recursive SCC must carry a stack
/// certificate, and every direct call in the body must reach a certified
/// callee (`@ bounded_stack` or `fip`); an indirect call is a conservative
/// failure until callable types carry the corresponding contract.
///
/// # Errors
/// Fails with the first uncertified callee, non-tail recursive edge, mixed
/// TRMC mode, or mutual-TRMC/partially annotated SCC obstruction.
pub fn check_bounded_stack(
    core: &Core,
    claims: &BTreeSet<Sym>,
    fips: &Fips,
    users: &BTreeSet<Sym>,
) -> Result<(), ClaimError> {
    for f in &core.fns {
        let claimed = claims.contains(&f.name);
        if !claimed && !matches!(fips.get(&f.name), Some(Fip::Fip(_))) {
            continue;
        }
        // An explicit row claim takes the claim's vocabulary even beside the
        // keyword: the message then names exactly what the user wrote.
        let words = if claimed {
            &BOUNDED_STACK_WORDS
        } else {
            &FIP_STACK_WORDS
        };
        bounded_stack(f, core, users, words)?;
        let group = scc_of(core, users, f.name);
        if let Some(g) = group
            .iter()
            .find(|g| **g != f.name && !stack_certified(**g, claims, fips))
        {
            return Err(words.err(f.name, ClaimErrorKind::SccMemberUncertified { member: *g }));
        }
        let mut scan = CalleeScan {
            claims,
            fips,
            users,
            first: None,
        };
        scan.walk_comp(&f.body);
        if let Some(reason) = scan.first {
            return Err(words.err(f.name, ClaimErrorKind::StackNotClosed { reason }));
        }
    }
    Ok(())
}

// The spelling under which the linearity rules run, selecting the diagnostic
// vocabulary: the `fip` keyword proves linearity as one of its three
// properties, while the standalone claim demands the fact alone. One rule
// set, two vocabularies, so the shared walk never acquires a fork.
struct LinearClaimWords {
    spelling: ClaimSpelling,
}

impl LinearClaimWords {
    fn err(&self, fname: Sym, kind: ClaimErrorKind) -> ClaimError {
        ClaimError {
            fname,
            spelled: self.spelling.render(),
            origin: self.spelling.origin(),
            kind: Box::new(kind),
        }
    }
}

const FIP_LINEAR_WORDS: LinearClaimWords = LinearClaimWords {
    spelling: ClaimSpelling::Keyword(FIP),
};

const LINEAR_CLAIM_WORDS: LinearClaimWords = LinearClaimWords {
    spelling: ClaimSpelling::Row(CoeffectFact::Linear),
};

// The checker only distinguishes an affine use from duplication, so counts
// saturate instead of risking overflow on deep Core.
#[derive(Clone, Copy, PartialEq, Eq)]
enum UseCount {
    Once,
    Many,
}

type Uses = BTreeMap<Sym, UseCount>;

enum UseFrame<'a> {
    Comp(&'a Comp),
    Value(&'a Value),
    Reduce(UseReduce<'a>),
}

enum UseReduce<'a> {
    Add(usize),
    If,
    Bind {
        binder: Sym,
        immediate: bool,
    },
    Case(&'a [(CorePat, Comp)]),
    Lam(&'a [Sym]),
    WithReuse(Sym),
    Reuse(Sym),
    Thunk,
    Handle {
        return_var: Option<Sym>,
        has_return: bool,
        ops: &'a [HandleOp],
    },
}

fn one_use(name: Sym) -> Uses {
    BTreeMap::from([(name, UseCount::Once)])
}

fn add_uses(mut left: Uses, mut right: Uses) -> Uses {
    if left.len() < right.len() {
        swap(&mut left, &mut right);
    }
    for (name, count) in right {
        left.entry(name)
            .and_modify(|current| *current = UseCount::Many)
            .or_insert(count);
    }
    left
}

fn join_uses(mut left: Uses, mut right: Uses) -> Uses {
    if left.len() < right.len() {
        swap(&mut left, &mut right);
    }
    for (name, count) in right {
        left.entry(name)
            .and_modify(|current| {
                if count == UseCount::Many {
                    *current = UseCount::Many;
                }
            })
            .or_insert(count);
    }
    left
}

fn reduce_uses(results: &mut Vec<Uses>, children: usize) -> Uses {
    (0..children).fold(Uses::new(), |uses, _| {
        add_uses(
            uses,
            results
                .pop()
                .expect("linearity worklist reducer has one result per child"),
        )
    })
}

fn push_use_values<'a, I>(work: &mut Vec<UseFrame<'a>>, values: I)
where
    I: DoubleEndedIterator<Item = &'a Value> + ExactSizeIterator,
{
    work.push(UseFrame::Reduce(UseReduce::Add(values.len())));
    work.extend(values.rev().map(UseFrame::Value));
}

fn remove_pattern_uses(
    pattern: &CorePat,
    uses: &mut Uses,
    ctors: &BTreeMap<String, CtorInfo>,
) -> bool {
    match pattern {
        CorePat::Var(name) => {
            uses.remove(name);
            false
        }
        CorePat::Ctor(name, fields) => {
            let types = ctors.get(name.as_str()).map(|ctor| ctor.args.as_slice());
            let duplicate = fields.iter().enumerate().any(|(index, field)| {
                let Some(field) = field else { return false };
                let immediate = types
                    .and_then(|types| types.get(index))
                    .is_some_and(is_immediate);
                !immediate && uses.get(field) == Some(&UseCount::Many)
            });
            for field in fields.iter().flatten() {
                uses.remove(field);
            }
            duplicate
        }
        CorePat::Tuple(fields) => {
            let duplicate = fields
                .iter()
                .flatten()
                .any(|field| uses.get(field) == Some(&UseCount::Many));
            for field in fields.iter().flatten() {
                uses.remove(field);
            }
            duplicate
        }
        CorePat::Wild => false,
    }
}

struct LinearAnalysis<'a> {
    claims: &'a BTreeSet<Sym>,
    fips: &'a Fips,
    decls: &'a [DeclInfo],
    ctors: &'a BTreeMap<String, CtorInfo>,
    users: &'a BTreeSet<Sym>,
    duplicate: bool,
    first_call: Option<String>,
}

impl LinearAnalysis<'_> {
    fn observe_call(&mut self, comp: &Comp) {
        if self.first_call.is_some() {
            return;
        }
        match comp {
            Comp::Call(callee, args)
                if self.users.contains(callee)
                    && !linear_certified(*callee, self.claims, self.fips)
                    && passes_owned(*callee, args, self.decls) =>
            {
                self.first_call = Some(format!(
                    "call to `{callee}` receives an owned value but `{callee}` carries no \
                     linearity certificate; certify `{callee}` (`@ linear` or `fip`)"
                ));
            }
            Comp::App(..) => {
                self.first_call = Some(
                    "an indirect call through a first-class function value, \
                     which has no callee certificate"
                        .to_string(),
                );
            }
            _ => {}
        }
    }

    fn analyze(&mut self, root: &Comp) -> Uses {
        let mut work = vec![UseFrame::Comp(root)];
        let mut results = Vec::new();
        while let Some(frame) = work.pop() {
            match frame {
                UseFrame::Value(value) => match value {
                    Value::Var(name) => results.push(one_use(*name)),
                    Value::Ctor(_, _, fields)
                    | Value::Tuple(fields)
                    | Value::UnboxedTuple(fields) => {
                        push_use_values(&mut work, fields.iter());
                    }
                    Value::UnboxedRecord(fields) => {
                        push_use_values(&mut work, fields.iter().map(|(_, field)| field));
                    }
                    Value::Thunk(body) => {
                        work.push(UseFrame::Reduce(UseReduce::Thunk));
                        work.push(UseFrame::Comp(body));
                    }
                    _ => results.push(Uses::new()),
                },
                UseFrame::Comp(comp) => {
                    self.observe_call(comp);
                    match comp {
                        Comp::Return(value)
                        | Comp::Force(value)
                        | Comp::Error(value)
                        | Comp::FloatBuiltin(_, value)
                        | Comp::Neg(_, value)
                        | Comp::UnboxedProject(value, _)
                        | Comp::Dup(value)
                        | Comp::Drop(value)
                        | Comp::RefNew(value)
                        | Comp::RefGet(value) => work.push(UseFrame::Value(value)),
                        Comp::RefSet(left, right)
                        | Comp::InitAt(left, right)
                        | Comp::Prim(_, left, right) => {
                            push_use_values(&mut work, [left, right].into_iter());
                        }
                        Comp::Call(_, args)
                        | Comp::Do(_, args)
                        | Comp::StrBuiltin(_, args)
                        | Comp::Io(_, args) => push_use_values(&mut work, args.iter()),
                        Comp::Bind(first, binder, rest) => {
                            work.push(UseFrame::Reduce(UseReduce::Bind {
                                binder: *binder,
                                immediate: binds_immediate(first),
                            }));
                            work.push(UseFrame::Comp(rest));
                            work.push(UseFrame::Comp(first));
                        }
                        Comp::If(condition, yes, no) => {
                            work.push(UseFrame::Reduce(UseReduce::If));
                            work.push(UseFrame::Comp(no));
                            work.push(UseFrame::Comp(yes));
                            work.push(UseFrame::Value(condition));
                        }
                        Comp::Case(scrutinee, arms) => {
                            work.push(UseFrame::Reduce(UseReduce::Case(arms)));
                            work.extend(arms.iter().rev().map(|(_, body)| UseFrame::Comp(body)));
                            work.push(UseFrame::Value(scrutinee));
                        }
                        Comp::Lam(params, body) => {
                            work.push(UseFrame::Reduce(UseReduce::Lam(params)));
                            work.push(UseFrame::Comp(body));
                        }
                        Comp::App(callee, args) => {
                            work.push(UseFrame::Reduce(UseReduce::Add(args.len() + 1)));
                            work.extend(args.iter().rev().map(UseFrame::Value));
                            work.push(UseFrame::Comp(callee));
                        }
                        Comp::Mask(_, body) => work.push(UseFrame::Comp(body)),
                        Comp::WithReuse { token, freed, body } => {
                            work.push(UseFrame::Reduce(UseReduce::WithReuse(*token)));
                            work.push(UseFrame::Comp(body));
                            work.push(UseFrame::Value(freed));
                        }
                        Comp::Reuse(token, value) => {
                            work.push(UseFrame::Reduce(UseReduce::Reuse(*token)));
                            work.push(UseFrame::Value(value));
                        }
                        Comp::Handle {
                            body,
                            return_var,
                            return_body,
                            ops,
                        } => {
                            work.push(UseFrame::Reduce(UseReduce::Handle {
                                return_var: *return_var,
                                has_return: return_body.is_some(),
                                ops: ops.arms(),
                            }));
                            work.extend(ops.iter().rev().map(|op| UseFrame::Comp(&op.body)));
                            if let Some(return_body) = return_body {
                                work.push(UseFrame::Comp(return_body));
                            }
                            work.push(UseFrame::Comp(body));
                        }
                    }
                }
                UseFrame::Reduce(reduce) => {
                    let uses = match reduce {
                        UseReduce::Add(children) => reduce_uses(&mut results, children),
                        UseReduce::If => {
                            let no = results
                                .pop()
                                .expect("linearity worklist has a result for the no branch");
                            let yes = results
                                .pop()
                                .expect("linearity worklist has a result for the yes branch");
                            let condition = results
                                .pop()
                                .expect("linearity worklist has a result for the condition");
                            add_uses(condition, join_uses(yes, no))
                        }
                        UseReduce::Bind { binder, immediate } => {
                            let mut rest = results
                                .pop()
                                .expect("linearity worklist has a result for the bind body");
                            if !immediate && rest.get(&binder) == Some(&UseCount::Many) {
                                self.duplicate = true;
                            }
                            rest.remove(&binder);
                            let first = results.pop().expect(
                                "linearity worklist has a result for the bound computation",
                            );
                            add_uses(first, rest)
                        }
                        UseReduce::Case(arms) => {
                            let mut joined = Uses::new();
                            for (pattern, _) in arms.iter().rev() {
                                let mut arm = results
                                    .pop()
                                    .expect("linearity worklist has a result for each case arm");
                                self.duplicate |=
                                    remove_pattern_uses(pattern, &mut arm, self.ctors);
                                joined = join_uses(joined, arm);
                            }
                            let scrutinee = results
                                .pop()
                                .expect("linearity worklist has a result for the scrutinee");
                            add_uses(scrutinee, joined)
                        }
                        UseReduce::Lam(params) => {
                            let mut body = results
                                .pop()
                                .expect("linearity worklist has a result for the lambda body");
                            for param in params {
                                if body.remove(param) == Some(UseCount::Many) {
                                    self.duplicate = true;
                                }
                            }
                            body
                        }
                        UseReduce::WithReuse(token) => {
                            let mut body = results
                                .pop()
                                .expect("linearity worklist has a result for the reuse body");
                            body.remove(&token);
                            let freed = results
                                .pop()
                                .expect("linearity worklist has a result for the freed value");
                            add_uses(freed, body)
                        }
                        UseReduce::Reuse(token) => {
                            let value = results
                                .pop()
                                .expect("linearity worklist has a result for the reused value");
                            add_uses(one_use(token), value)
                        }
                        UseReduce::Thunk => {
                            let mut body = results
                                .pop()
                                .expect("linearity worklist has a result for the thunk body");
                            if body.values().any(|count| *count == UseCount::Many) {
                                self.duplicate = true;
                            }
                            for count in body.values_mut() {
                                *count = UseCount::Once;
                            }
                            body
                        }
                        UseReduce::Handle {
                            return_var,
                            has_return,
                            ops,
                        } => {
                            // Handler regions conservatively compose as one path.
                            let mut uses = Uses::new();
                            for op in ops.iter().rev() {
                                let mut clause = results.pop().expect(
                                    "linearity worklist has a result for each handler clause",
                                );
                                clause.remove(&op.resume);
                                for param in &op.params {
                                    clause.remove(param);
                                }
                                uses = add_uses(uses, clause);
                            }
                            if has_return {
                                let mut returned = results.pop().expect(
                                    "linearity worklist has a result for the handler return body",
                                );
                                if let Some(return_var) = return_var {
                                    returned.remove(&return_var);
                                }
                                uses = add_uses(uses, returned);
                            }
                            let body = results
                                .pop()
                                .expect("linearity worklist has a result for the handled body");
                            add_uses(body, uses)
                        }
                    };
                    results.push(uses);
                }
            }
        }
        debug_assert_eq!(results.len(), 1);
        results
            .pop()
            .expect("linearity worklist produces one result for its root")
    }
}

fn lin_fn(
    f: &CoreFn,
    claims: &BTreeSet<Sym>,
    fips: &Fips,
    decls: &[DeclInfo],
    ctors: &BTreeMap<String, CtorInfo>,
    users: &BTreeSet<Sym>,
    words: &LinearClaimWords,
) -> Result<(), ClaimError> {
    let arrow = decls
        .iter()
        .find(|decl| decl.name == f.name.as_str())
        .and_then(|decl| arrow_args(&decl.ty))
        .filter(|args| args.len() == f.params.len());
    let mut analysis = LinearAnalysis {
        claims,
        fips,
        decls,
        ctors,
        users,
        duplicate: false,
        first_call: None,
    };
    let mut body_uses = analysis.analyze(&f.body);
    for (index, param) in f.params.iter().enumerate() {
        let immediate = arrow
            .and_then(|args| args.get(index))
            .is_some_and(is_immediate);
        if !immediate && body_uses.get(param) == Some(&UseCount::Many) {
            analysis.duplicate = true;
        }
        body_uses.remove(param);
    }
    if analysis.duplicate {
        Err(dup_err(f.name, words))
    } else if let Some(reason) = analysis.first_call {
        Err(words.err(f.name, ClaimErrorKind::LinearityNotClosed { reason }))
    } else {
        Ok(())
    }
}

/// Verify the linearity fact of every claiming function (the standalone
/// `@ linear` claim, and one of the `fip` keyword's facts) over the raw
/// (pre-RC) core.
///
/// Linearity is a property of the source term: each owned, non-immediate
/// binder (parameter, pattern field, let result) is consumed at most once on
/// any control path, match fields and captured thunk bodies included, and no
/// parameter may be borrowed. `dup`/`drop` on an immediate (`Int`, `Bool`,
/// ...) is a runtime no-op under pointer tagging, so scalars are unrestricted
/// (linearity constrains heap, not machine words). The RC pass later inserts
/// the dup/drop that REALIZE this linear consumption over a unique cell;
/// those are an implementation detail of a linear program and are not
/// re-counted against it, which is why this runs pre-RC, not on the
/// reuse-lowered core the allocation and stack drives check. Linearity is
/// closed through direct calls: a callee receiving an owned value must itself
/// be certified (`@ linear` or `fip`); an indirect call is a conservative
/// failure until callable types carry the corresponding contract. Allocation
/// and stack growth are unconstrained by this drive.
///
/// # Errors
/// Fails with the first borrowed parameter, duplicated owned value, or
/// uncertified call obstruction.
pub fn check_linear(
    core: &Core,
    claims: &BTreeSet<Sym>,
    fips: &Fips,
    sigs: &Sigs,
    decls: &[DeclInfo],
    ctors: &BTreeMap<String, CtorInfo>,
    users: &BTreeSet<Sym>,
) -> Result<(), ClaimError> {
    for f in &core.fns {
        let claimed = claims.contains(&f.name);
        if !claimed && !matches!(fips.get(&f.name), Some(Fip::Fip(_))) {
            continue;
        }
        // An explicit row claim takes the claim's vocabulary even beside the
        // keyword: the message then names exactly what the user wrote.
        let words = if claimed {
            &LINEAR_CLAIM_WORDS
        } else {
            &FIP_LINEAR_WORDS
        };
        if sigs.get(&f.name).is_some_and(|m| m.iter().any(|b| *b)) {
            return Err(words.err(f.name, ClaimErrorKind::BorrowedParam));
        }
        lin_fn(f, claims, fips, decls, ctors, users, words)?;
    }
    Ok(())
}

// Whether `g` carries a linearity certificate a `@ linear` caller may rely
// on: the standalone claim itself, or the `fip` keyword (whose own check
// proves linearity at every budget). `fbip` and `@ noalloc` are explicitly
// not certificates: both permit duplication.
fn linear_certified(g: Sym, claims: &BTreeSet<Sym>, fips: &Fips) -> bool {
    claims.contains(&g) || matches!(fips.get(&g), Some(Fip::Fip(_)))
}

// Whether the value at an argument position may carry an owned heap cell. A
// scalar literal never does, and a position whose declared parameter type is
// immediate never receives one; everything else is conservatively owned.
fn arg_owned(v: &Value, callee_param: Option<&Type>) -> bool {
    let scalar = matches!(
        v,
        Value::Int(_)
            | Value::I64(_)
            | Value::U64(_)
            | Value::Bool(_)
            | Value::Float(_)
            | Value::Unit
    );
    !(scalar || callee_param.is_some_and(is_immediate))
}

fn passes_owned(callee: Sym, args: &[Value], decls: &[DeclInfo]) -> bool {
    // Trust per-position callee types only when the counts match; otherwise
    // every argument is conservatively owned.
    let arrow = decls
        .iter()
        .find(|decl| decl.name == callee.as_str())
        .and_then(|decl| arrow_args(&decl.ty))
        .filter(|params| params.len() == args.len());
    args.iter()
        .enumerate()
        .any(|(index, value)| arg_owned(value, arrow.and_then(|params| params.get(index))))
}

const fn is_immediate(t: &Type) -> bool {
    matches!(
        t,
        Type::Unit | Type::Int | Type::I64 | Type::U64 | Type::Bool | Type::Float | Type::Char
    )
}

fn arrow_args(mut ty: &Type) -> Option<&[Type]> {
    loop {
        match ty {
            Type::Forall(_, body) | Type::RowForall(_, body) => ty = body,
            Type::Fun(args, _, _) => return Some(args.as_slice()),
            _ => return None,
        }
    }
}

fn dup_err(fname: Sym, words: &LinearClaimWords) -> ClaimError {
    words.err(fname, ClaimErrorKind::DuplicatesValue)
}

// A let/match binder is immediate when its RHS provably yields a scalar: a
// primitive (arithmetic/comparison) or a scalar literal. Anything else (a call,
// a constructor, an unknown variable) is treated as heap and must be linear.
const fn binds_immediate(m: &Comp) -> bool {
    match m {
        Comp::Prim(..) => true,
        Comp::Return(v) => matches!(
            v,
            Value::Int(_)
                | Value::I64(_)
                | Value::U64(_)
                | Value::Bool(_)
                | Value::Float(_)
                | Value::Unit
        ),
        _ => false,
    }
}

const fn kw(f: Fip) -> &'static str {
    match f {
        Fip::Fip(_) => FIP,
        Fip::Fbip(_) | Fip::No => FBIP,
    }
}

// Direct coverage of `bounded_stack`'s rules. The strict no-`Dup` linearity pass
// rejects every recursive heap function before this check is reached end-to-end,
// so the mixed-mode and mutual-plus-TRMC paths can only be exercised on
// hand-built core (the linearity and allocation passes are bypassed here, which
// is exactly what isolates the stack rule).
#[cfg(test)]
mod tests {
    use std::{iter, mem, thread};

    use super::Alloc::{Bounded, Finite, Unlimited};
    use super::*;
    use crate::core::cbpv::{CheckedHandler, CoreOp};

    const DEEP_ALLOC_COMP_COUNT: usize = 20_000;
    const DEEP_ALLOC_VALUE_COUNT: usize = 20_000;
    const DEEP_LINEAR_COMP_COUNT: usize = 20_000;
    const DEEP_LINEAR_VALUE_COUNT: usize = 20_000;
    const ORDINARY_TEST_STACK: usize = 2 * 1024 * 1024;

    fn users(names: &[&str]) -> BTreeSet<Sym> {
        names.iter().map(|n| Sym::from(*n)).collect()
    }

    fn one(name: &str, arity: usize, body: Comp) -> CoreFn {
        CoreFn {
            name: name.into(),
            dict_arity: 0,
            params: (0..arity)
                .map(|i| Sym::from(format!("p{i}").as_str()))
                .collect(),
            body,
        }
    }

    #[test]
    fn allocation_check_handles_deep_core_on_an_ordinary_stack() {
        thread::Builder::new()
            .name("deep-allocation-check".into())
            .stack_size(ORDINARY_TEST_STACK)
            .spawn(|| {
                let name = Sym::new("deep");
                let mut value = Value::Unit;
                for _ in 0..DEEP_ALLOC_VALUE_COUNT {
                    value = Value::UnboxedTuple(vec![value]);
                }
                let mut body = Comp::Return(value);
                for _ in 0..DEEP_ALLOC_COMP_COUNT {
                    body = Comp::Mask(Vec::new(), Box::new(body));
                }
                let program = Core {
                    fns: vec![one("deep", 1, body)],
                };
                let fips = Fips::from([(name, Fip::Fbip(0))]);
                // A nonempty certificate forces `rebound` across the same deep tree.
                let callable_certified = BTreeMap::from([(name, BTreeSet::from([Sym::new("p0")]))]);

                assert!(check_alloc(
                    &program,
                    &fips,
                    &BTreeSet::from([name]),
                    &BTreeSet::new(),
                    &callable_certified,
                )
                .is_ok());
                mem::forget(program);
            })
            .expect("spawn deep allocation-check test")
            .join()
            .expect("deep allocation-check test panicked");
    }

    #[test]
    fn linearity_check_handles_deep_computations_on_an_ordinary_stack() {
        thread::Builder::new()
            .name("deep-linearity-check".into())
            .stack_size(ORDINARY_TEST_STACK)
            .spawn(|| {
                let name = Sym::new("deep");
                let mut value = Value::Var(Sym::new("p0"));
                for _ in 0..DEEP_LINEAR_VALUE_COUNT {
                    value = Value::UnboxedTuple(vec![value]);
                }
                let mut body = Comp::Return(value);
                let mut add_bind = true;
                for index in 0..DEEP_LINEAR_COMP_COUNT {
                    body = if add_bind {
                        Comp::Bind(
                            Box::new(Comp::Return(Value::Unit)),
                            Sym::new(format!("unused{index}").as_str()),
                            Box::new(body),
                        )
                    } else {
                        Comp::If(
                            Value::Bool(true),
                            Box::new(body),
                            Box::new(Comp::Return(Value::Unit)),
                        )
                    };
                    add_bind = !add_bind;
                }
                let program = Core {
                    fns: vec![one("deep", 1, body)],
                };

                assert!(check_linear(
                    &program,
                    &BTreeSet::from([name]),
                    &BTreeMap::new(),
                    &BTreeMap::new(),
                    &[],
                    &BTreeMap::new(),
                    &BTreeSet::from([name]),
                )
                .is_ok());
                mem::forget(program);
            })
            .expect("spawn deep linearity-check test")
            .join()
            .expect("deep linearity-check test panicked");
    }

    // `f(x) to t; <k>`, the recursive-call-feeding-continuation shape.
    fn rec(k: Comp) -> Comp {
        Comp::Bind(
            Box::new(Comp::Call("f".into(), vec![Value::Var("x".into())])),
            "t".into(),
            Box::new(k),
        )
    }

    fn cons_tail() -> Comp {
        rec(Comp::Return(Value::Ctor(
            "Cons".into(),
            1,
            vec![Value::Var("h".into()), Value::Var("t".into())],
        )))
    }

    fn add_tail() -> Comp {
        rec(Comp::Prim(
            CoreOp::Add,
            Value::Int(1),
            Value::Var("t".into()),
        ))
    }

    #[test]
    fn nontail_self_call_is_rejected() {
        let f = one(
            "f",
            1,
            rec(Comp::Prim(
                CoreOp::Mul,
                Value::Var("t".into()),
                Value::Var("x".into()),
            )),
        );
        let core = Core {
            fns: vec![f.clone()],
        };
        let err = bounded_stack(&f, &core, &users(&["f"]), &FIP_STACK_WORDS)
            .unwrap_err()
            .to_string();
        assert!(err.contains("non-tail position"), "{err}");
    }

    #[test]
    fn plain_tail_and_one_trmc_mode_is_accepted() {
        // A cons-TRMC tail beside a plain self tail-call: codegen loops both.
        let body = Comp::If(
            Value::Bool(true),
            Box::new(cons_tail()),
            Box::new(Comp::Call("f".into(), vec![Value::Var("x".into())])),
        );
        let f = one("f", 1, body);
        let core = Core {
            fns: vec![f.clone()],
        };
        assert!(bounded_stack(&f, &core, &users(&["f"]), &FIP_STACK_WORDS).is_ok());
    }

    #[test]
    fn mixed_cons_and_add_is_rejected() {
        let body = Comp::If(
            Value::Bool(true),
            Box::new(cons_tail()),
            Box::new(add_tail()),
        );
        let f = one("f", 1, body);
        let core = Core {
            fns: vec![f.clone()],
        };
        let err = bounded_stack(&f, &core, &users(&["f"]), &FIP_STACK_WORDS)
            .unwrap_err()
            .to_string();
        assert!(err.contains("mixes"), "{err}");
    }

    #[test]
    fn trmc_paired_with_mutual_call_is_rejected() {
        // f cons-TRMCs itself but also tail-calls g (its SCC partner); codegen
        // loops only direct self-TRMC, so the mutual call would grow the stack.
        let body = Comp::If(
            Value::Bool(true),
            Box::new(cons_tail()),
            Box::new(Comp::Call("g".into(), vec![Value::Var("x".into())])),
        );
        let f = one("f", 1, body);
        let g = one("g", 1, Comp::Call("f".into(), vec![Value::Var("x".into())]));
        let core = Core {
            fns: vec![f.clone(), g],
        };
        let err = bounded_stack(&f, &core, &users(&["f", "g"]), &FIP_STACK_WORDS)
            .unwrap_err()
            .to_string();
        assert!(err.contains("mutually recursive"), "{err}");
    }

    #[test]
    fn nonrecursive_is_trivially_bounded() {
        let f = one(
            "f",
            2,
            Comp::Prim(
                CoreOp::Add,
                Value::Var("p0".into()),
                Value::Var("p1".into()),
            ),
        );
        let core = Core {
            fns: vec![f.clone()],
        };
        assert!(bounded_stack(&f, &core, &users(&["f"]), &FIP_STACK_WORDS).is_ok());
    }

    // --- standalone `@ bounded_stack` claims (`check_bounded_stack`) ---

    fn tail_call(g: &str) -> Comp {
        Comp::Call(g.into(), vec![Value::Var("x".into())])
    }

    #[test]
    fn claim_admits_allocating_tail_loop() {
        // The claim constrains stack alone: a cons-TRMC loop allocates freely.
        let core = Core {
            fns: vec![one("f", 1, cons_tail())],
        };
        let claims = users(&["f"]);
        assert!(check_bounded_stack(&core, &claims, &Fips::new(), &users(&["f"])).is_ok());
    }

    #[test]
    fn claim_rejects_nontail_recursion_in_its_own_words() {
        let f = one(
            "f",
            1,
            rec(Comp::Prim(
                CoreOp::Mul,
                Value::Var("t".into()),
                Value::Var("x".into()),
            )),
        );
        let core = Core { fns: vec![f] };
        let claims = users(&["f"]);
        let err = check_bounded_stack(&core, &claims, &Fips::new(), &users(&["f"]))
            .unwrap_err()
            .to_string();
        assert!(err.contains("`@ bounded_stack`"), "{err}");
        assert!(err.contains("non-tail position"), "{err}");
        assert!(err.contains("drop the `@ bounded_stack` claim"), "{err}");
    }

    #[test]
    fn claim_rejects_uncertified_direct_callee() {
        let f = one("f", 1, tail_call("g"));
        let g = one("g", 1, Comp::Return(Value::Var("p0".into())));
        let core = Core { fns: vec![f, g] };
        let claims = users(&["f"]);
        let err = check_bounded_stack(&core, &claims, &Fips::new(), &users(&["f", "g"]))
            .unwrap_err()
            .to_string();
        assert!(err.contains("call to `g`"), "{err}");
        assert!(err.contains("no bounded-stack certificate"), "{err}");
    }

    #[test]
    fn fip_callee_is_a_certificate_but_fbip_is_not() {
        let f = one("f", 1, tail_call("g"));
        let g = one("g", 1, Comp::Return(Value::Var("p0".into())));
        let certificate = fip_of(&g);
        let weaker = fbip_of(&g);
        let core = Core { fns: vec![f, g] };
        let claims = users(&["f"]);
        let all = users(&["f", "g"]);
        assert!(check_bounded_stack(&core, &claims, &certificate, &all).is_ok());
        let err = check_bounded_stack(&core, &claims, &weaker, &all)
            .unwrap_err()
            .to_string();
        assert!(err.contains("call to `g`"), "{err}");
    }

    #[test]
    fn partially_claimed_mutual_recursion_is_rejected() {
        let f = one("f", 1, tail_call("g"));
        let g = one("g", 1, tail_call("f"));
        let core = Core { fns: vec![f, g] };
        let all = users(&["f", "g"]);
        let err = check_bounded_stack(&core, &users(&["f"]), &Fips::new(), &all)
            .unwrap_err()
            .to_string();
        assert!(err.contains("mutually recursive with `g`"), "{err}");
        assert!(check_bounded_stack(&core, &all, &Fips::new(), &all).is_ok());
    }

    #[test]
    fn claim_rejects_indirect_call() {
        let body = Comp::App(
            Box::new(Comp::Force(Value::Var("p0".into()))),
            vec![Value::Var("x".into())],
        );
        let core = Core {
            fns: vec![one("f", 1, body)],
        };
        let claims = users(&["f"]);
        let err = check_bounded_stack(&core, &claims, &Fips::new(), &users(&["f"]))
            .unwrap_err()
            .to_string();
        assert!(err.contains("indirect call"), "{err}");
    }

    #[test]
    fn claim_scans_thunk_bodies() {
        // A closure built in the claimed frame may be forced within it, so an
        // uncertified call inside a thunk body is still a conservative failure.
        let f = one("f", 1, Comp::Return(Value::Thunk(Box::new(tail_call("g")))));
        let g = one("g", 1, Comp::Return(Value::Var("p0".into())));
        let core = Core { fns: vec![f, g] };
        let claims = users(&["f"]);
        let err = check_bounded_stack(&core, &claims, &Fips::new(), &users(&["f", "g"]))
            .unwrap_err()
            .to_string();
        assert!(err.contains("call to `g`"), "{err}");
    }

    #[test]
    fn fip_functions_run_the_stack_drive_in_keyword_words() {
        // The keyword's bounded-stack fact goes through the same drive as the
        // row claim, with the keyword's own vocabulary.
        let f = one(
            "f",
            1,
            rec(Comp::Prim(
                CoreOp::Mul,
                Value::Var("t".into()),
                Value::Var("x".into()),
            )),
        );
        let core = Core { fns: vec![f] };
        let fips: Fips = iter::once((Sym::from("f"), Fip::Fip(0))).collect();
        let err = check_bounded_stack(&core, &BTreeSet::new(), &fips, &users(&["f"]))
            .unwrap_err()
            .to_string();
        assert!(err.contains("marked `fip`"), "{err}");
        assert!(err.contains("annotate it `fbip`"), "{err}");
    }

    #[test]
    fn fip_caller_of_fbip_callee_fails_stack_closure_not_the_alloc_walk() {
        // The allocation walk's callee rule is budget-only, so an `fbip` callee
        // satisfies it; what an `fbip` callee cannot supply is the stack
        // certificate, and exactly that drive rejects the composition.
        let f = one("f", 1, tail_call("g"));
        let g = one("g", 1, Comp::Return(Value::Int(0)));
        let fips: Fips = [(f.name, Fip::Fip(0)), (g.name, Fip::Fbip(0))]
            .into_iter()
            .collect();
        let core = Core { fns: vec![f, g] };
        let all = users(&["f", "g"]);
        assert!(check_alloc(&core, &fips, &all, &BTreeSet::new(), &BTreeMap::new(),).is_ok());
        let err = check_bounded_stack(&core, &BTreeSet::new(), &fips, &all)
            .unwrap_err()
            .to_string();
        assert!(err.contains("marked `fip`"), "{err}");
        assert!(err.contains("no bounded-stack certificate"), "{err}");
    }

    #[test]
    fn row_claims_certify_a_callee_for_a_fip_caller() {
        // `@ {bounded_stack, linear, noalloc}` on the callee supplies every
        // fact a zero-budget `fip` caller needs: claims in the two closure
        // drives, a zero-budget `fbip` expansion in the allocation walk.
        let f = one("f", 1, tail_call("g"));
        let g = one("g", 1, Comp::Return(Value::Int(0)));
        let fips: Fips = [(f.name, Fip::Fip(0)), (g.name, Fip::Fbip(0))]
            .into_iter()
            .collect();
        let core = Core { fns: vec![f, g] };
        let all = users(&["f", "g"]);
        let claims = users(&["g"]);
        assert!(check_alloc(&core, &fips, &all, &BTreeSet::new(), &BTreeMap::new(),).is_ok());
        assert!(check_bounded_stack(&core, &claims, &fips, &all).is_ok());
        assert!(check_linear(
            &core,
            &claims,
            &fips,
            &BTreeMap::new(),
            &[],
            &BTreeMap::new(),
            &all,
        )
        .is_ok());
    }

    // --- type-aware linearity (the `fip` fns of `check_linear`) ---

    fn decl(name: &str, params: Vec<Type>) -> DeclInfo {
        DeclInfo {
            name: name.into(),
            params: (0..params.len()).map(|i| format!("p{i}")).collect(),
            ty: Type::fun(params, Type::Int),
            effects: BTreeSet::new(),
            pure: true,
        }
    }

    fn linfn(name: &str, params: &[&str], body: Comp) -> CoreFn {
        CoreFn {
            name: name.into(),
            params: params.iter().map(|p| Sym::from(*p)).collect(),
            dict_arity: 0,
            body,
        }
    }

    fn fip_of(f: &CoreFn) -> Fips {
        iter::once((f.name, Fip::Fip(0))).collect()
    }

    fn fbip_of(f: &CoreFn) -> Fips {
        iter::once((f.name, Fip::Fbip(0))).collect()
    }

    // Drive the unified linearity check over keyword-annotated functions only,
    // as the deleted fip-specific entry point did.
    fn fip_linear(
        core: &Core,
        fips: &Fips,
        decls: &[DeclInfo],
        ctors: &BTreeMap<String, CtorInfo>,
    ) -> Result<(), String> {
        let all: BTreeSet<Sym> = core.fns.iter().map(|f| f.name).collect();
        check_linear(
            core,
            &BTreeSet::new(),
            fips,
            &BTreeMap::new(),
            decls,
            ctors,
            &all,
        )
        .map_err(|e| e.to_string())
    }

    fn use_var_twice(x: &str) -> Comp {
        Comp::Prim(CoreOp::Add, Value::Var(x.into()), Value::Var(x.into()))
    }

    #[test]
    fn zero_alloc_rejects_fresh_closure_value() {
        let f = one(
            "make",
            1,
            Comp::Return(Value::Thunk(Box::new(Comp::Prim(
                CoreOp::Add,
                Value::Var("p0".into()),
                Value::Var("y".into()),
            )))),
        );
        let core = Core {
            fns: vec![f.clone()],
        };
        let err = check_alloc(
            &core,
            &fbip_of(&f),
            &users(&["make"]),
            &BTreeSet::new(),
            &BTreeMap::new(),
        )
        .expect_err("fbip/without-alloc must reject closure allocation");
        assert!(
            err.to_string()
                .contains("a lambda is materialized as a fresh closure cell"),
            "{err}"
        );
    }

    #[test]
    fn allocation_witnesses_follow_evaluation_order() {
        let body = Comp::Bind(
            Box::new(Comp::Return(Value::Ctor("First".into(), 0, Vec::new()))),
            "ignored".into(),
            Box::new(Comp::App(
                Box::new(Comp::Return(Value::Tuple(Vec::new()))),
                vec![Value::Ctor("Third".into(), 0, Vec::new())],
            )),
        );
        let function = one("ordered", 0, body);
        let core = Core {
            fns: vec![function.clone()],
        };
        let message = check_alloc(
            &core,
            &fbip_of(&function),
            &users(&["ordered"]),
            &BTreeSet::new(),
            &BTreeMap::new(),
        )
        .expect_err("the fixture materializes three cells and makes an indirect call")
        .to_string();
        let first = message
            .find("constructor `First`")
            .expect("first witness is present");
        let second = message
            .find("a tuple is built fresh")
            .expect("second witness is present");
        let third = message
            .find("constructor `Third`")
            .expect("third witness is present");

        assert!(first < second && second < third, "{message}");
        assert!(message.contains("and 1 more"), "{message}");
    }

    #[test]
    fn zero_alloc_accepts_erased_newtype_constructor() {
        let f = one(
            "wrap",
            1,
            Comp::Return(Value::Ctor("Id".into(), 0, vec![Value::Var("p0".into())])),
        );
        let core = Core {
            fns: vec![f.clone()],
        };
        let newtypes = users(&["Id"]);
        assert!(check_alloc(
            &core,
            &fbip_of(&f),
            &users(&["wrap"]),
            &newtypes,
            &BTreeMap::new(),
        )
        .is_ok());
    }

    #[test]
    fn zero_alloc_still_rejects_ordinary_one_field_constructor() {
        let f = one(
            "wrap",
            1,
            Comp::Return(Value::Ctor("Box".into(), 0, vec![Value::Var("p0".into())])),
        );
        let core = Core {
            fns: vec![f.clone()],
        };
        let err = check_alloc(
            &core,
            &fbip_of(&f),
            &users(&["wrap"]),
            &BTreeSet::new(),
            &BTreeMap::new(),
        )
        .expect_err("ordinary one-field data must still allocate");
        assert!(
            err.to_string().contains("constructor `Box` is built fresh"),
            "{err}"
        );
    }

    #[test]
    fn zero_alloc_checks_allocations_inside_newtype_payload() {
        let f = one(
            "wrap",
            1,
            Comp::Return(Value::Ctor(
                "Id".into(),
                0,
                vec![Value::Tuple(vec![Value::Var("p0".into())])],
            )),
        );
        let core = Core {
            fns: vec![f.clone()],
        };
        let err = check_alloc(
            &core,
            &fbip_of(&f),
            &users(&["wrap"]),
            &users(&["Id"]),
            &BTreeMap::new(),
        )
        .expect_err("allocation in an erased wrapper payload must remain visible");
        assert!(err.to_string().contains("a tuple is built fresh"), "{err}");
    }

    #[test]
    fn heap_param_used_twice_is_rejected() {
        // `Str` is a boxed value, so two uses need a real dup.
        let f = linfn("f", &["s"], use_var_twice("s"));
        let core = Core {
            fns: vec![f.clone()],
        };
        let decls = [decl("f", vec![Type::Str])];
        let err = fip_linear(&core, &fip_of(&f), &decls, &BTreeMap::new()).unwrap_err();
        assert!(err.contains("not linear"), "{err}");
    }

    #[test]
    fn immediate_param_used_twice_is_allowed() {
        // `Int` is an immediate; `dup` is a runtime no-op, so `x + x` is linear.
        let f = linfn("f", &["x"], use_var_twice("x"));
        let core = Core {
            fns: vec![f.clone()],
        };
        let decls = [decl("f", vec![Type::Int])];
        assert!(fip_linear(&core, &fip_of(&f), &decls, &BTreeMap::new()).is_ok());
    }

    fn pair_ctors(field0: Type, field1: Type) -> BTreeMap<String, CtorInfo> {
        iter::once((
            "Pair".to_string(),
            CtorInfo {
                type_name: "P".into(),
                params: vec![],
                param_kinds: vec![],
                args: vec![field0, field1],
                tag: 0,
                fields: vec!["a".into(), "b".into()],
            },
        ))
        .collect()
    }

    fn match_pair(field_used_twice: &str) -> Comp {
        Comp::Case(
            Value::Var("p".into()),
            vec![(
                CorePat::Ctor("Pair".into(), vec![Some("a".into()), Some("b".into())]),
                use_var_twice(field_used_twice),
            )],
        )
    }

    #[test]
    fn immediate_ctor_field_used_twice_is_allowed() {
        // Field `a` is a concrete `Int`, so reusing it is fine.
        let f = linfn("f", &["p"], match_pair("a"));
        let core = Core {
            fns: vec![f.clone()],
        };
        let decls = [decl("f", vec![Type::Con("P".into(), vec![])])];
        let ctors = pair_ctors(Type::Int, Type::Str);
        assert!(fip_linear(&core, &fip_of(&f), &decls, &ctors).is_ok());
    }

    #[test]
    fn heap_ctor_field_used_twice_is_rejected() {
        // Field `b` is a boxed `Str`, so two uses need a dup.
        let f = linfn("f", &["p"], match_pair("b"));
        let core = Core {
            fns: vec![f.clone()],
        };
        let decls = [decl("f", vec![Type::Con("P".into(), vec![])])];
        let ctors = pair_ctors(Type::Int, Type::Str);
        let err = fip_linear(&core, &fip_of(&f), &decls, &ctors).unwrap_err();
        assert!(err.contains("not linear"), "{err}");
    }

    #[test]
    fn branches_are_distinct_paths() {
        // `s` used once per arm is once per path: linear despite two textual uses.
        let body = Comp::If(
            Value::Bool(true),
            Box::new(Comp::Return(Value::Var("s".into()))),
            Box::new(Comp::Return(Value::Var("s".into()))),
        );
        let f = linfn("f", &["s"], body);
        let core = Core {
            fns: vec![f.clone()],
        };
        let decls = [decl("f", vec![Type::Str])];
        assert!(fip_linear(&core, &fip_of(&f), &decls, &BTreeMap::new()).is_ok());
    }

    #[test]
    fn handler_regions_are_conservative_sequential_paths() {
        let ops = CheckedHandler::new(vec![HandleOp {
            name: "emit".into(),
            params: Vec::new(),
            resume: "resume".into(),
            body: Comp::Return(Value::Var("s".into())),
        }])
        .expect("one handler clause is unique");
        let body = Comp::Handle {
            body: Box::new(Comp::Return(Value::Var("s".into()))),
            return_var: None,
            return_body: None,
            ops,
        };
        let function = linfn("f", &["s"], body);
        let core = Core {
            fns: vec![function.clone()],
        };
        let decls = [decl("f", vec![Type::Str])];

        let error = fip_linear(&core, &fip_of(&function), &decls, &BTreeMap::new())
            .expect_err("handler regions are conservatively summed");
        assert!(error.contains("not linear"), "{error}");
    }

    // --- standalone `@ linear` claims (`check_linear`) ---

    fn claimed_linear(
        core: &Core,
        claims: &BTreeSet<Sym>,
        fips: &Fips,
        decls: &[DeclInfo],
    ) -> Result<(), String> {
        let all: BTreeSet<Sym> = core.fns.iter().map(|f| f.name).collect();
        check_linear(
            core,
            claims,
            fips,
            &BTreeMap::new(),
            decls,
            &BTreeMap::new(),
            &all,
        )
        .map_err(|e| e.to_string())
    }

    #[test]
    fn claim_rejects_duplication_in_its_own_words() {
        let f = linfn("f", &["s"], use_var_twice("s"));
        let core = Core { fns: vec![f] };
        let decls = [decl("f", vec![Type::Str])];
        let err = claimed_linear(&core, &users(&["f"]), &BTreeMap::new(), &decls).unwrap_err();
        assert!(err.contains("marked `@ linear` but is not linear"), "{err}");
    }

    #[test]
    fn claim_rejects_duplicated_capture_in_thunk_body() {
        // The closure frame owns its capture `s` exactly once; a body using it
        // twice would duplicate the cell when forced, so counting the capture
        // as one consumption in the outer frame is not enough on its own.
        let body = Comp::Return(Value::Thunk(Box::new(use_var_twice("s"))));
        let f = linfn("f", &["s"], body);
        let core = Core { fns: vec![f] };
        let decls = [decl("f", vec![Type::Str])];
        let err = claimed_linear(&core, &users(&["f"]), &BTreeMap::new(), &decls).unwrap_err();
        assert!(err.contains("marked `@ linear` but is not linear"), "{err}");
    }

    #[test]
    fn claim_rejects_borrowed_parameter() {
        let f = linfn("f", &["s"], Comp::Return(Value::Var("s".into())));
        let sigs: Sigs = iter::once((f.name, vec![true])).collect();
        let core = Core { fns: vec![f] };
        let err = check_linear(
            &core,
            &users(&["f"]),
            &BTreeMap::new(),
            &sigs,
            &[],
            &BTreeMap::new(),
            &users(&["f"]),
        )
        .unwrap_err()
        .to_string();
        assert!(err.contains("has a borrowed parameter"), "{err}");
    }

    #[test]
    fn claim_admits_allocation_and_unbounded_recursion() {
        // `f(x) to t; Cons(h, t)`: a fresh cell and a non-tail self call, both
        // outside the claim's scope; every owned binder is consumed once.
        let f = one("f", 1, cons_tail());
        let core = Core { fns: vec![f] };
        assert!(claimed_linear(&core, &users(&["f"]), &BTreeMap::new(), &[]).is_ok());
    }

    #[test]
    fn claim_rejects_owned_value_into_uncertified_callee() {
        let f = one("f", 1, tail_call("g"));
        let g = one("g", 1, Comp::Return(Value::Int(0)));
        let core = Core { fns: vec![f, g] };
        let decls = [decl("g", vec![Type::Str])];
        let err = claimed_linear(&core, &users(&["f"]), &BTreeMap::new(), &decls).unwrap_err();
        assert!(err.contains("carries no linearity certificate"), "{err}");
    }

    #[test]
    fn duplication_precedes_call_closure_diagnostics() {
        let body = Comp::Bind(
            Box::new(use_var_twice("s")),
            "ignored".into(),
            Box::new(Comp::Call("g".into(), vec![Value::Var("s".into())])),
        );
        let function = linfn("f", &["s"], body);
        let callee = one("g", 1, Comp::Return(Value::Unit));
        let core = Core {
            fns: vec![function, callee],
        };
        let decls = [decl("f", vec![Type::Str]), decl("g", vec![Type::Str])];

        let error = claimed_linear(&core, &users(&["f"]), &BTreeMap::new(), &decls)
            .expect_err("the duplicate failure takes precedence");
        assert!(error.contains("not linear"), "{error}");
        assert!(!error.contains("call tree"), "{error}");
    }

    #[test]
    fn claim_admits_immediate_arguments_to_uncertified_callee() {
        // `g` takes an `Int`: nothing owned crosses the call, so `g` needs no
        // certificate for the caller's linearity to hold.
        let f = one("f", 1, tail_call("g"));
        let g = one("g", 1, Comp::Return(Value::Int(0)));
        let core = Core { fns: vec![f, g] };
        let decls = [decl("g", vec![Type::Int])];
        assert!(claimed_linear(&core, &users(&["f"]), &BTreeMap::new(), &decls).is_ok());
    }

    #[test]
    fn fip_callee_is_a_linearity_certificate_but_fbip_is_not() {
        let g = one("g", 1, Comp::Return(Value::Var("p0".into())));
        let certificate = fip_of(&g);
        let weaker = fbip_of(&g);
        let f = one("f", 1, tail_call("g"));
        let core = Core { fns: vec![f, g] };
        assert!(claimed_linear(&core, &users(&["f"]), &certificate, &[]).is_ok());
        let err = claimed_linear(&core, &users(&["f"]), &weaker, &[]).unwrap_err();
        assert!(err.contains("carries no linearity certificate"), "{err}");
    }

    #[test]
    fn fip_functions_run_the_linear_closure_in_keyword_words() {
        // The keyword's linearity fact is closed through direct calls by the
        // same drive as the row claim, phrased in the keyword's vocabulary.
        let f = one("f", 1, tail_call("g"));
        let g = one("g", 1, Comp::Return(Value::Int(0)));
        let fips: Fips = iter::once((Sym::from("f"), Fip::Fip(0))).collect();
        let core = Core { fns: vec![f, g] };
        let err = claimed_linear(&core, &BTreeSet::new(), &fips, &[]).unwrap_err();
        assert!(
            err.contains("marked `fip` but linearity is not closed"),
            "{err}"
        );
    }

    #[test]
    fn linear_claim_rejects_indirect_call() {
        let f = one(
            "f",
            1,
            Comp::App(
                Box::new(Comp::Force(Value::Var("p0".into()))),
                vec![Value::Int(1)],
            ),
        );
        let core = Core { fns: vec![f] };
        let err = claimed_linear(&core, &users(&["f"]), &BTreeMap::new(), &[]).unwrap_err();
        assert!(err.contains("indirect call"), "{err}");
    }

    #[test]
    fn claim_scans_thunk_bodies_for_uncertified_callees() {
        let inner = tail_call("g");
        let f = one("f", 1, Comp::Return(Value::Thunk(Box::new(inner))));
        let g = one("g", 1, Comp::Return(Value::Int(0)));
        let core = Core { fns: vec![f, g] };
        let err = claimed_linear(&core, &users(&["f"]), &BTreeMap::new(), &[]).unwrap_err();
        assert!(err.contains("carries no linearity certificate"), "{err}");
    }

    // --- allocation budgets (the graded lattice and its checking rules) ---

    #[test]
    fn alloc_lattice_add_join_le() {
        // Sequencing adds and saturates instead of wrapping into a small budget.
        assert_eq!(Bounded(2).add(Bounded(3)), Bounded(5));
        assert_eq!(Bounded(u64::MAX).add(Bounded(1)), Bounded(u64::MAX));
        // The tops absorb through both operations.
        assert_eq!(Bounded(7).add(Finite), Finite);
        assert_eq!(Finite.add(Unlimited), Unlimited);
        assert_eq!(Bounded(7).join(Finite), Finite);
        assert_eq!(Finite.join(Unlimited), Unlimited);
        // Branching joins to the worst path, not the sum.
        assert_eq!(Bounded(2).join(Bounded(3)), Bounded(3));
        // The order is Bounded(0) <= ... <= Finite <= Unlimited.
        assert!(Bounded(3).le(Finite) && Finite.le(Unlimited));
        assert!(!Finite.le(Bounded(u64::MAX)) && !Unlimited.le(Finite));
        assert!(Bounded(2).le(Bounded(2)) && !Bounded(3).le(Bounded(2)));
    }

    #[test]
    fn subsumption_is_a_genuine_partial_order() {
        // fip(1) allocates more than fbip allows; fbip claims less structure
        // than fip demands. Incomparable in both directions.
        assert!(!subsumes(Fip::Fip(1), Fip::Fbip(0)));
        assert!(!subsumes(Fip::Fbip(0), Fip::Fip(1)));
        // A tighter budget stands wherever a looser one is demanded.
        assert!(subsumes(Fip::Fip(0), Fip::Fip(2)));
        assert!(subsumes(Fip::Fip(1), Fip::Fbip(1)));
        assert!(!subsumes(Fip::Fip(2), Fip::Fip(1)));
        assert!(!subsumes(Fip::Fbip(0), Fip::Fip(0)));
        // Everything satisfies no demand; no discipline satisfies any.
        assert!(subsumes(Fip::No, Fip::No) && subsumes(Fip::Fbip(2), Fip::No));
        assert!(!subsumes(Fip::No, Fip::Fbip(2)));
    }

    fn fresh_pair(a: &str, b: &str) -> Comp {
        Comp::Return(Value::Ctor(
            "Pair".into(),
            0,
            vec![Value::Var(a.into()), Value::Var(b.into())],
        ))
    }

    fn check(core: &Core, fips: &Fips, user_names: &[&str]) -> Result<(), String> {
        check_alloc(
            core,
            fips,
            &users(user_names),
            &BTreeSet::new(),
            &BTreeMap::new(),
        )
        .map_err(|e| e.to_string())
    }

    #[test]
    fn budget_admits_exactly_the_declared_cells() {
        let f = one("f", 2, fresh_pair("p0", "p1"));
        let core = Core {
            fns: vec![f.clone()],
        };
        let zero = check(&core, &fip_of(&f), &["f"])
            .expect_err("a fresh cell must still fail the zero budget");
        // The zero-budget message keeps the historical fully-in-place phrasing.
        assert!(zero.contains("is marked `fip` but in `f`,"), "{zero}");
        let budgeted: Fips = iter::once((f.name, Fip::Fip(1))).collect();
        assert!(check(&core, &budgeted, &["f"]).is_ok());
    }

    #[test]
    fn budget_counts_nested_aggregate_cells() {
        let f = one(
            "f",
            1,
            Comp::Return(Value::Ctor(
                "Outer".into(),
                0,
                vec![Value::Tuple(vec![Value::Var("p0".into())])],
            )),
        );
        let core = Core {
            fns: vec![f.clone()],
        };
        let grades = |budget| iter::once((f.name, Fip::Fip(budget))).collect();
        let err = check(&core, &grades(1), &["f"]).unwrap_err();
        assert!(
            err.contains("needs an allocation budget of at least 2, declared at most 1"),
            "{err}"
        );
        assert!(check(&core, &grades(2), &["f"]).is_ok());
    }

    #[test]
    fn allocating_handler_clause_has_no_finite_budget() {
        let ops = CheckedHandler::new(vec![HandleOp {
            name: "emit".into(),
            params: Vec::new(),
            resume: "resume".into(),
            body: Comp::Return(Value::Ctor("Cell".into(), 0, Vec::new())),
        }])
        .expect("one operation is unique");
        let f = one(
            "f",
            0,
            Comp::Handle {
                body: Box::new(Comp::Do("emit".into(), Vec::new())),
                return_var: None,
                return_body: None,
                ops,
            },
        );
        let core = Core {
            fns: vec![f.clone()],
        };
        let grades: Fips = iter::once((f.name, Fip::Fip(u32::MAX))).collect();
        let err = check(&core, &grades, &["f"]).unwrap_err();
        assert!(err.contains("has no bounded allocation budget"), "{err}");
        assert!(err.contains("constructor `Cell` is built fresh"), "{err}");
    }

    #[test]
    fn call_sites_charge_the_callee_budget_additively() {
        // f builds one cell and calls g (declared fip(1)) twice in sequence:
        // inferred budget 3.
        let g = one("g", 1, fresh_pair("p0", "p0"));
        let call_g = || Comp::Call("g".into(), vec![Value::Var("p0".into())]);
        let body = Comp::Bind(
            Box::new(call_g()),
            "a".into(),
            Box::new(Comp::Bind(
                Box::new(call_g()),
                "b".into(),
                Box::new(fresh_pair("a", "b")),
            )),
        );
        let f = one("f", 1, body);
        let core = Core {
            fns: vec![f.clone(), g.clone()],
        };
        let grades = |fb: u32| -> Fips {
            [(f.name, Fip::Fip(fb)), (g.name, Fip::Fip(1))]
                .into_iter()
                .collect()
        };
        let err = check(&core, &grades(2), &["f", "g"]).unwrap_err();
        assert!(
            err.contains("needs an allocation budget of at least 3, declared at most 2"),
            "{err}"
        );
        assert!(
            err.contains("call to `g` charges its declared allocation budget of 1"),
            "{err}"
        );
        assert!(check(&core, &grades(3), &["f", "g"]).is_ok());
    }

    #[test]
    fn recursive_call_charges_the_full_declared_budget() {
        // Credit accounting: a recursive call charges f's own declared budget,
        // so a path that both allocates and recurses needs budget 2 while the
        // base path needs 1. Declared fip(1), the worst path wins: rejected.
        let cell = || Comp::Return(Value::Ctor("Leaf".into(), 0, vec![Value::Var("p0".into())]));
        let alloc_then_recurse = Comp::Bind(
            Box::new(cell()),
            "l".into(),
            Box::new(Comp::Call("f".into(), vec![Value::Var("l".into())])),
        );
        let f = one(
            "f",
            1,
            Comp::If(
                Value::Bool(true),
                Box::new(cell()),
                Box::new(alloc_then_recurse),
            ),
        );
        let core = Core {
            fns: vec![f.clone()],
        };
        let grades: Fips = iter::once((f.name, Fip::Fip(1))).collect();
        let err = check(&core, &grades, &["f"]).unwrap_err();
        assert!(
            err.contains("needs an allocation budget of at least 2, declared at most 1"),
            "{err}"
        );
        // With the allocation confined to the base path the recursion is pure
        // credit transfer: each frame spends the one cell the claim grants.
        let base_only = one(
            "f",
            1,
            Comp::If(
                Value::Bool(true),
                Box::new(cell()),
                Box::new(Comp::Call("f".into(), vec![Value::Var("p0".into())])),
            ),
        );
        let core = Core {
            fns: vec![base_only.clone()],
        };
        let grades: Fips = iter::once((base_only.name, Fip::Fip(1))).collect();
        assert!(check(&core, &grades, &["f"]).is_ok());
    }
}
