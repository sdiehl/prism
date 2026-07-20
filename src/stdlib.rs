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
    ("Data.Ordered", include_str!("../lib/std/Data/Ordered.pr")),
    ("Data.Char", include_str!("../lib/std/Data/Char.pr")),
    ("Data.String", include_str!("../lib/std/Data/String.pr")),
    ("Data.Pretty", include_str!("../lib/std/Data/Pretty.pr")),
    ("Data.Foldable", include_str!("../lib/std/Data/Foldable.pr")),
    ("Data.Monad", include_str!("../lib/std/Data/Monad.pr")),
    ("Data.Checked", include_str!("../lib/std/Data/Checked.pr")),
    ("Data.Vec", include_str!("../lib/std/Data/Vec.pr")),
    ("Data.Tensor", include_str!("../lib/std/Data/Tensor.pr")),
    (
        "Data.FlatArray",
        include_str!("../lib/std/Data/FlatArray.pr"),
    ),
    ("Teleport", include_str!("../lib/std/Teleport.pr")),
    ("Replay", include_str!("../lib/std/Replay.pr")),
    ("Concurrent", include_str!("../lib/std/Concurrent.pr")),
    ("Quickcheck", include_str!("../lib/std/Quickcheck.pr")),
    ("Wire", include_str!("../lib/std/Wire.pr")),
    ("Data.Bytes", include_str!("../lib/std/Data/Bytes.pr")),
    ("Incr", include_str!("../lib/std/Incr.pr")),
    ("Test", include_str!("../lib/std/Test.pr")),
    ("Blit", include_str!("../lib/std/Blit.pr")),
    ("Time", include_str!("../lib/std/Time.pr")),
    ("Json", include_str!("../lib/std/Json.pr")),
    ("Sequence", include_str!("../lib/std/Sequence.pr")),
    ("Cli", include_str!("../lib/std/Cli.pr")),
    ("Arena", include_str!("../lib/std/Arena.pr")),
    ("Math", include_str!("../lib/std/Math.pr")),
    ("Data.Graph", include_str!("../lib/std/Data/Graph.pr")),
    ("Control.State", include_str!("../lib/std/Control/State.pr")),
    (
        "Control.Reader",
        include_str!("../lib/std/Control/Reader.pr"),
    ),
    (
        "Control.Writer",
        include_str!("../lib/std/Control/Writer.pr"),
    ),
    ("Control.Fresh", include_str!("../lib/std/Control/Fresh.pr")),
    (
        "Data.Validation",
        include_str!("../lib/std/Data/Validation.pr"),
    ),
    (
        "Data.UnionFind",
        include_str!("../lib/std/Data/UnionFind.pr"),
    ),
];
