// A per-compilation fresh-id supply. Each pass that synthesizes binders owns a
// `Fresh` starting from zero, so its ids are deterministic regardless of how
// many compilations run concurrently. This is the explicit alternative to the
// process-global counter (`Sym::fresh`), whose ids depend on global interning
// order and so would make snapshot output flaky under parallel test threads.
//
// `Fresh` only allocates the number; the spelling lives in `names.rs`, the one
// table for synthesized names. Callers pass the id to a `names::*` helper that
// renders an unforgeable name (containing `@`, which no source identifier can),
// so a fresh binder can never capture a user name.

#[derive(Debug, Default)]
pub struct Fresh(u32);

impl Fresh {
    #[must_use]
    pub const fn new() -> Self {
        Self(0)
    }

    /// Hand out the next id and advance the counter.
    pub const fn bump(&mut self) -> u32 {
        let n = self.0;
        self.0 += 1;
        n
    }
}
