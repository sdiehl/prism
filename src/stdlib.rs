//! The embedded standard library.
//!
//! Curated modules shipped inside the compiler binary and resolved like any
//! other import, from the lowest-priority root in the module search path. The
//! small always-on prelude (`lib/prelude.pr`) opens these with glob imports so
//! their names are in unqualified scope everywhere; a project module reaches
//! them explicitly with `import Data.List` and friends.
//!
//! Each entry maps a dotted module path to its source text. A project that
//! defines a module of the same name shadows the stdlib one, since project roots
//! are searched first.

/// Dotted module path to source, in dependency order (leaves first) for
/// readability; resolution order does not depend on it.
pub const STDLIB: &[(&str, &str)] = &[
    ("Data.List", include_str!("../lib/std/Data/List.pr")),
    ("Data.Maybe", include_str!("../lib/std/Data/Maybe.pr")),
    ("Data.Result", include_str!("../lib/std/Data/Result.pr")),
    ("Data.Map", include_str!("../lib/std/Data/Map.pr")),
    ("Data.Set", include_str!("../lib/std/Data/Set.pr")),
    ("Data.Char", include_str!("../lib/std/Data/Char.pr")),
    ("Data.String", include_str!("../lib/std/Data/String.pr")),
    ("Replay", include_str!("../lib/std/Replay.pr")),
    ("Concurrent", include_str!("../lib/std/Concurrent.pr")),
];
