//! Compiler-work counters: how much structural work a phase actually did.
//!
//! Wall time answers "how long", which a loaded machine can answer wrongly. These
//! counters answer "how much", which it cannot: they are sums and maxima over the
//! nodes a pass touched, so they are a property of the compilation and not of the
//! box it ran on. That is what makes them usable as evidence rather than as a
//! reading, and it is why a receipt quotes them.
//!
//! Descents charge in two disciplines:
//!
//! - a read-only walk enters a node and reconstructs nothing;
//! - a rewrite reconstructs every node it descends.
//!
//! So `visits` counts every node either discipline entered, and `rebuilt` counts
//! only the nodes a rewrite rebuilt. The pair separates analysis from
//! transformation without comparing input to output, which would cost more than
//! the pass being measured.
//!
//! **What is counted, exactly.** Three shared descents, and only those: the
//! untyped [`Rewrite`](super::traverse::Rewrite) and
//! [`Visit`](super::traverse::Visit), plus the typed-Core rewrite the optimizer
//! and effect lowering are built on. That leaves real work uncounted, and the
//! omissions are not a rounding error:
//!
//! - a pass that overrides a variant and handles it without recursing charges
//!   nothing for that node;
//! - a hand-rolled walk charges nothing at all, which covers the typed analyses
//!   (there is no shared typed read-only discipline to instrument) and the
//!   frame-local `tailrec` recursion;
//! - the front end works on the AST, which has no instrumented descent, so
//!   parsing, resolution, and typechecking charge nothing however hard they
//!   worked.
//!
//! Elaboration is the awkward case and worth naming: it charges, but only for
//! the free-variable scans that classify each handler's resume shape. That is a
//! count of handlers, not of the program, so a one-line program still reports a
//! few hundred visits for the prelude's handlers. The number is real and it is
//! not a measure of elaboration.
//!
//! A zero is therefore "no instrumented descent happened", never "no work
//! happened", and a non-zero is "this much instrumented descent happened",
//! never "this is what the phase cost". These counters are a lower bound on
//! structural work: sound to compare between two runs of the same compiler,
//! unsound to read as a share of a phase's total cost.
//!
//! **Determinism.** `visits` and `rebuilt` are sums and `max_depth` is a maximum,
//! all over the same set of nodes regardless of the order threads reach them, so
//! a parallel compilation reports the same counts as a serial one. That is the
//! property that lets a receipt commit to them. Wall time and peak memory do not
//! have it and are therefore not recorded here.
//!
//! Counting is off unless [`enable`] is called, and off is the default: with the
//! flag clear every entry point is one relaxed load and a predicted branch.

use std::cell::Cell;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};

// Counting is opt-in, so the hot descent pays one relaxed load when it is off.
static ENABLED: AtomicBool = AtomicBool::new(false);

// Every Core node entered by either descent discipline.
static VISITS: AtomicU64 = AtomicU64::new(0);
// Every Core node reconstructed by a rewrite descent.
static REBUILT: AtomicU64 = AtomicU64::new(0);
// The deepest descent any thread reached, as a maximum over per-thread depths.
static MAX_DEPTH: AtomicU64 = AtomicU64::new(0);

thread_local! {
    // Descent depth is per-stack, so it is per-thread; the global above keeps the
    // maximum across threads.
    static DEPTH: Cell<u64> = const { Cell::new(0) };
}

/// One phase's structural work.
///
/// Every field is order-independent, so the same compilation reports the same
/// counts whether it ran on one thread or many.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct WorkCounts {
    /// Core nodes entered by either descent discipline.
    pub visits: u64,
    /// Core nodes reconstructed by a rewrite descent.
    pub rebuilt: u64,
    /// The deepest descent observed.
    pub max_depth: u64,
}

impl WorkCounts {
    /// Whether any structural work was recorded at all.
    ///
    /// This is a fact about the counters, not a verdict. Only a phase built on
    /// an instrumented descent owes a non-zero count: the front end works on the
    /// AST and legitimately records nothing here, so reading this as vacuity for
    /// every phase would condemn `parse` for doing its job. The caller that knows
    /// which descent a phase uses is the one that may draw the conclusion.
    #[must_use]
    pub const fn is_silent(self) -> bool {
        self.visits == 0
    }
}

/// Start counting. Idempotent, and never called from a hot path.
pub fn enable() {
    ENABLED.store(true, Ordering::Relaxed);
}

/// Whether counting is on.
#[must_use]
pub fn enabled() -> bool {
    ENABLED.load(Ordering::Relaxed)
}

/// Read the counters without disturbing them.
#[must_use]
pub fn snapshot() -> WorkCounts {
    WorkCounts {
        visits: VISITS.load(Ordering::Relaxed),
        rebuilt: REBUILT.load(Ordering::Relaxed),
        max_depth: MAX_DEPTH.load(Ordering::Relaxed),
    }
}

/// Read the counters and clear them, so the next read is attributed to whatever
/// runs next. The driver calls this at a phase boundary.
pub fn take() -> WorkCounts {
    WorkCounts {
        visits: VISITS.swap(0, Ordering::Relaxed),
        rebuilt: REBUILT.swap(0, Ordering::Relaxed),
        max_depth: MAX_DEPTH.swap(0, Ordering::Relaxed),
    }
}

/// Charge one visited node.
pub fn visit() {
    if enabled() {
        VISITS.fetch_add(1, Ordering::Relaxed);
    }
}

/// Charge one visited node that a rewrite also reconstructed.
pub fn rebuild() {
    if enabled() {
        VISITS.fetch_add(1, Ordering::Relaxed);
        REBUILT.fetch_add(1, Ordering::Relaxed);
    }
}

/// Enter one descent level, returning a guard that leaves it on drop.
///
/// The guard is what keeps depth honest under the early returns and `?` inside a
/// descent: the level is left however the frame exits.
#[must_use]
pub fn frame() -> Frame {
    if !enabled() {
        return Frame(false);
    }
    let depth = DEPTH.with(|d| {
        let next = d.get() + 1;
        d.set(next);
        next
    });
    MAX_DEPTH.fetch_max(depth, Ordering::Relaxed);
    Frame(true)
}

/// Holds one descent level open; see [`frame`].
#[derive(Debug)]
pub struct Frame(bool);

impl Drop for Frame {
    fn drop(&mut self) {
        if self.0 {
            DEPTH.with(|d| d.set(d.get().saturating_sub(1)));
        }
    }
}
