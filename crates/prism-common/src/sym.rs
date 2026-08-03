// Interned identifiers. Names are a bounded set, so the first time a string is
// interned it is leaked to `&'static str` and recorded; thereafter a `Sym` is a
// `Copy` id with O(1) equality and hashing. `as_str`/`Display`/`Debug` resolve
// back to the name. Ordering is by intern id (first-seen order), so callers that
// need name order must sort on `as_str` (see effect-op id assignment).

use std::collections::HashMap;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::sync::{Mutex, OnceLock};

use serde::ser::Error as _;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

#[derive(Copy, Clone)]
pub struct Sym {
    id: u32,
    name: &'static str,
}

// The symbol arena: the `name <-> id` table a compilation interns into.
//
// One process-global table, NOT a per-thread one: the query engine parallelises
// WITHIN one compilation (`QueryScheduler` spawns workers), so a `Sym` crosses
// worker threads and every worker must see the same arena. Interning takes the
// arena's internal lock; resolution stays lock-free via the embedded
// `&'static str` on `Sym`, so `Display` never locks. Moving ownership to a
// compilation would require propagating the same arena to every query worker and
// replacing the leaked spelling stored in `Sym`.
#[derive(Debug)]
struct SymbolArena {
    table: Mutex<ArenaTable>,
}

#[derive(Debug)]
struct ArenaTable {
    ids: HashMap<&'static str, u32>,
    names: Vec<&'static str>,
}

impl SymbolArena {
    fn new() -> Self {
        Self {
            table: Mutex::new(ArenaTable {
                ids: HashMap::new(),
                names: Vec::new(),
            }),
        }
    }

    // Intern a spelling, leaking it to `&'static str` on first sight.
    fn intern(&self, s: &str) -> (u32, &'static str) {
        let mut t = self.table.lock().expect("sym arena poisoned");
        if let Some(&id) = t.ids.get(s) {
            let name = t.names[id as usize];
            drop(t);
            return (id, name);
        }
        let leaked: &'static str = Box::leak(s.to_owned().into_boxed_str());
        let id = u32::try_from(t.names.len()).expect("more than u32::MAX interned symbols");
        t.names.push(leaked);
        t.ids.insert(leaked, id);
        drop(t);
        (id, leaked)
    }

    // Mint a fresh anonymous id displayed as `%n`, recorded in the reverse map
    // too (`%` cannot appear in a source spelling, so it never shadows one).
    fn fresh(&self) -> (u32, &'static str) {
        let mut t = self.table.lock().expect("sym arena poisoned");
        let id = u32::try_from(t.names.len()).expect("more than u32::MAX interned symbols");
        let leaked: &'static str = Box::leak(format!("%{id}").into_boxed_str());
        t.names.push(leaked);
        t.ids.insert(leaked, id);
        drop(t);
        (id, leaked)
    }

    // Record `name` under a fresh id WITHOUT touching the reverse map, so this
    // identity never becomes the canonical resolution of its spelling.
    fn record(&self, name: &'static str) -> u32 {
        let mut t = self.table.lock().expect("sym arena poisoned");
        let id = u32::try_from(t.names.len()).expect("more than u32::MAX interned symbols");
        t.names.push(name);
        drop(t);
        id
    }

    // Whether `id` is the identity the reverse map resolves `name` to, i.e. the
    // canonical symbol for that spelling. False for a `record`ed identity, which
    // deliberately shares a spelling with the canonical one.
    fn is_canonical(&self, id: u32, name: &str) -> bool {
        let t = self.table.lock().expect("sym arena poisoned");
        t.ids.get(name) == Some(&id)
    }
}

// The process-global arena shared across compilations and across the query
// workers of one compilation.
static GLOBAL_ARENA: OnceLock<SymbolArena> = OnceLock::new();

fn arena() -> &'static SymbolArena {
    GLOBAL_ARENA.get_or_init(SymbolArena::new)
}

// A symbol's identity is an interner id, which is meaningless outside the process
// that minted it, so the wire form is the spelling and `Deserialize` re-interns it.
// That round-trip preserves identity only for the canonical symbol of a spelling. A
// `fresh_named` identity is by construction a SECOND symbol with an existing
// spelling, so writing it would emit a document that reads back as the canonical
// one: two distinct binders silently merged into one. Refuse to write it instead of
// encoding a term that decodes to a different term. `fresh` is unaffected -- its
// `%n` spelling is unique and canonical, so distinct gensyms stay distinct.
impl Serialize for Sym {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        if !arena().is_canonical(self.id, self.name) {
            return Err(S::Error::custom(format!(
                "cannot serialize the non-canonical symbol `{}`: its identity is a fresh binder \
                 sharing a spelling with another symbol, so re-interning it on read would merge \
                 the two",
                self.name
            )));
        }
        serializer.serialize_str(self.as_str())
    }
}

impl<'de> Deserialize<'de> for Sym {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        String::deserialize(deserializer).map(|name| Self::new(&name))
    }
}

impl Sym {
    /// Intern a string, returning its `Sym`.
    ///
    /// # Panics
    /// Panics if the arena lock is poisoned or more than `u32::MAX` distinct
    /// symbols are interned.
    #[must_use]
    pub fn new(s: &str) -> Self {
        let (id, name) = arena().intern(s);
        Self { id, name }
    }

    /// Mint a fresh anonymous `Sym`: a unique identity from the interner,
    /// displayed as an unforgeable `%n` (no source identifier can contain `%`).
    /// Use this for synthesized binders instead of `Sym::from(format!(...))`,
    /// which manufactures identity as text and exposes the interner to arbitrary
    /// names. The id is globally unique for the process, not a per-compilation
    /// counter, so do not embed it in snapshot-visible output.
    ///
    /// # Panics
    /// Panics if the arena lock is poisoned or more than `u32::MAX` symbols are
    /// allocated.
    #[must_use]
    pub fn fresh() -> Self {
        let (id, name) = arena().fresh();
        Self { id, name }
    }

    /// Mint a fresh identity that *displays* as an existing symbol's name.
    ///
    /// The result compares unequal to `display` and to every other `fresh_named`
    /// result (identity is the fresh interner id), but resolves to the same text.
    /// This is how a rigid binder (a skolemized `forall` variable) gets a unique
    /// identity while its diagnostics still read as the source spelling: two
    /// nested `forall a` open to two distinct binders that both render `a`. The
    /// name is recorded for `as_str`/`Display` but the `name -> id` reverse map is
    /// left untouched, so `Sym::new("a")` still resolves to the canonical `a` and
    /// this fresh symbol never shadows it. Unlike [`fresh`](Self::fresh), the
    /// rendered text is deterministic (the source name, not a process-global
    /// `%n`), so a skolem in a diagnostic is snapshot-stable.
    ///
    /// Because the identity is exactly what the spelling cannot express, such a
    /// symbol is not serializable: `Serialize` refuses it rather than emit a
    /// document that reads back as the canonical symbol of the same name.
    ///
    /// # Panics
    /// Panics if the arena lock is poisoned or more than `u32::MAX` symbols are
    /// allocated.
    #[must_use]
    pub fn fresh_named(display: Self) -> Self {
        let id = arena().record(display.name);
        Self {
            id,
            name: display.name,
        }
    }

    /// Resolve a `Sym` back to its interned name.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        self.name
    }
}

impl PartialEq for Sym {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Eq for Sym {}

impl PartialOrd for Sym {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Sym {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.id.cmp(&other.id)
    }
}

impl Hash for Sym {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

impl fmt::Display for Sym {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

impl fmt::Debug for Sym {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

impl From<&str> for Sym {
    fn from(s: &str) -> Self {
        Self::new(s)
    }
}

impl From<String> for Sym {
    fn from(s: String) -> Self {
        Self::new(&s)
    }
}

impl From<&String> for Sym {
    fn from(s: &String) -> Self {
        Self::new(s)
    }
}

#[cfg(test)]
mod tests {
    use super::{arena, Sym};

    // The serde guard rests on this discriminator: a `fresh_named` identity is the
    // one kind of symbol whose spelling does not resolve back to it, and a `fresh`
    // gensym is not that kind.
    #[test]
    fn only_fresh_named_is_non_canonical() {
        let a = Sym::new("a");
        let skolem = Sym::fresh_named(a);
        let gensym = Sym::fresh();
        assert_ne!(a, skolem);
        assert!(arena().is_canonical(a.id, a.name));
        assert!(!arena().is_canonical(skolem.id, skolem.name));
        assert!(arena().is_canonical(gensym.id, gensym.name));
    }
}
