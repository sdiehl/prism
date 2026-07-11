// Interned identifiers. Names are a bounded set, so the first time a string is
// interned it is leaked to `&'static str` and recorded; thereafter a `Sym` is a
// `Copy` id with O(1) equality and hashing. `as_str`/`Display`/`Debug` resolve
// back to the name. Ordering is by intern id (first-seen order), so callers that
// need name order must sort on `as_str` (see effect-op id assignment).

use std::collections::HashMap;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::sync::{Mutex, OnceLock};

#[derive(Copy, Clone)]
pub struct Sym {
    id: u32,
    name: &'static str,
}

#[derive(Debug)]
struct Interner {
    ids: HashMap<&'static str, u32>,
    names: Vec<&'static str>,
}

static INTERNER: OnceLock<Mutex<Interner>> = OnceLock::new();

fn interner() -> &'static Mutex<Interner> {
    INTERNER.get_or_init(|| {
        Mutex::new(Interner {
            ids: HashMap::new(),
            names: Vec::new(),
        })
    })
}

impl Sym {
    /// Intern a string, returning its `Sym`.
    ///
    /// # Panics
    /// Panics if the interner mutex is poisoned or more than `u32::MAX`
    /// distinct symbols are interned.
    #[must_use]
    pub fn new(s: &str) -> Self {
        let (id, name) = {
            let mut it = interner().lock().expect("sym interner poisoned");
            let interned = if let Some(&id) = it.ids.get(s) {
                (id, it.names[id as usize])
            } else {
                let leaked: &'static str = Box::leak(s.to_owned().into_boxed_str());
                let id =
                    u32::try_from(it.names.len()).expect("more than u32::MAX interned symbols");
                it.names.push(leaked);
                it.ids.insert(leaked, id);
                (id, leaked)
            };
            drop(it);
            interned
        };
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
    /// Panics if the interner mutex is poisoned or more than `u32::MAX` symbols
    /// are allocated.
    #[must_use]
    pub fn fresh() -> Self {
        let (id, name) = {
            let mut it = interner().lock().expect("sym interner poisoned");
            let id = u32::try_from(it.names.len()).expect("more than u32::MAX interned symbols");
            let leaked: &'static str = Box::leak(format!("%{id}").into_boxed_str());
            it.names.push(leaked);
            it.ids.insert(leaked, id);
            drop(it);
            (id, leaked)
        };
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
    /// # Panics
    /// Panics if the interner mutex is poisoned or more than `u32::MAX` symbols
    /// are allocated.
    #[must_use]
    pub fn fresh_named(display: Self) -> Self {
        let id = {
            let mut it = interner().lock().expect("sym interner poisoned");
            let id = u32::try_from(it.names.len()).expect("more than u32::MAX interned symbols");
            it.names.push(display.name);
            drop(it);
            id
        };
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
