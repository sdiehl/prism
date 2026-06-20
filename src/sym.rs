// Interned identifiers. Names are a bounded set, so the first time a string is
// interned it is leaked to `&'static str` and recorded; thereafter a `Sym` is a
// `Copy` id with O(1) equality and hashing. `as_str`/`Display`/`Debug` resolve
// back to the name. Ordering is by intern id (first-seen order), so callers that
// need name order must sort on `as_str` (see effect-op id assignment).

use std::collections::HashMap;
use std::fmt;
use std::sync::{Mutex, OnceLock};

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Sym(u32);

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
        let id = {
            let mut it = interner().lock().expect("sym interner poisoned");
            if let Some(&id) = it.ids.get(s) {
                id
            } else {
                let leaked: &'static str = Box::leak(s.to_owned().into_boxed_str());
                let id =
                    u32::try_from(it.names.len()).expect("more than u32::MAX interned symbols");
                it.names.push(leaked);
                it.ids.insert(leaked, id);
                id
            }
        };
        Self(id)
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
        let id = {
            let mut it = interner().lock().expect("sym interner poisoned");
            let id = u32::try_from(it.names.len()).expect("more than u32::MAX interned symbols");
            let leaked: &'static str = Box::leak(format!("%{id}").into_boxed_str());
            it.names.push(leaked);
            it.ids.insert(leaked, id);
            id
        };
        Self(id)
    }

    /// Resolve a `Sym` back to its interned name.
    ///
    /// # Panics
    /// Panics if the interner mutex is poisoned.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        let name = interner().lock().expect("sym interner poisoned").names[self.0 as usize];
        name
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

impl PartialEq<str> for Sym {
    fn eq(&self, other: &str) -> bool {
        self.as_str() == other
    }
}

impl PartialEq<&str> for Sym {
    fn eq(&self, other: &&str) -> bool {
        self.as_str() == *other
    }
}

impl PartialEq<String> for Sym {
    fn eq(&self, other: &String) -> bool {
        self.as_str() == other
    }
}

impl PartialEq<&String> for Sym {
    fn eq(&self, other: &&String) -> bool {
        self.as_str() == other.as_str()
    }
}
