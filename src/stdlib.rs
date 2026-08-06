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
    ("Data.IntMap", include_str!("../lib/std/Data/IntMap.pr")),
    ("Data.IntSet", include_str!("../lib/std/Data/IntSet.pr")),
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
    ("Data.Frozen", include_str!("../lib/std/Data/Frozen.pr")),
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
    ("Data.Fixpoint", include_str!("../lib/std/Data/Fixpoint.pr")),
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
    ("Control.Layer", include_str!("../lib/std/Control/Layer.pr")),
    (
        "Control.Rewrite",
        include_str!("../lib/std/Control/Rewrite.pr"),
    ),
    ("Syntax.Source", include_str!("../lib/std/Syntax/Source.pr")),
    ("Syntax.Token", include_str!("../lib/std/Syntax/Token.pr")),
    ("Syntax.Lex", include_str!("../lib/std/Syntax/Lex.pr")),
    ("Syntax.Layout", include_str!("../lib/std/Syntax/Layout.pr")),
    ("Syntax.Query", include_str!("../lib/std/Syntax/Query.pr")),
    ("Syntax.Ast", include_str!("../lib/std/Syntax/Ast.pr")),
    ("Syntax.Codec", include_str!("../lib/std/Syntax/Codec.pr")),
    ("Syntax.Walk", include_str!("../lib/std/Syntax/Walk.pr")),
    (
        "Syntax.Analysis",
        include_str!("../lib/std/Syntax/Analysis.pr"),
    ),
    (
        "Syntax.Diagnostic",
        include_str!("../lib/std/Syntax/Diagnostic.pr"),
    ),
    ("Syntax.Report", include_str!("../lib/std/Syntax/Report.pr")),
    ("Syntax.Cursor", include_str!("../lib/std/Syntax/Cursor.pr")),
    (
        "Syntax.Parse.Support",
        include_str!("../lib/std/Syntax/Parse/Support.pr"),
    ),
    (
        "Syntax.Parse.Build",
        include_str!("../lib/std/Syntax/Parse/Build.pr"),
    ),
    (
        "Syntax.Parse.TypeSemantics",
        include_str!("../lib/std/Syntax/Parse/TypeSemantics.pr"),
    ),
    (
        "Syntax.Parse.GeneratedControl",
        include_str!("../lib/std/Syntax/Parse/GeneratedControl.pr"),
    ),
    (
        "Syntax.Parse.GeneratedType",
        include_str!("../lib/std/Syntax/Parse/GeneratedType.pr"),
    ),
    (
        "Syntax.Parse.PatternSemantics",
        include_str!("../lib/std/Syntax/Parse/PatternSemantics.pr"),
    ),
    (
        "Syntax.Parse.GeneratedPattern",
        include_str!("../lib/std/Syntax/Parse/GeneratedPattern.pr"),
    ),
    (
        "Syntax.Parse.Type",
        include_str!("../lib/std/Syntax/Parse/Type.pr"),
    ),
    (
        "Syntax.Parse.Pattern",
        include_str!("../lib/std/Syntax/Parse/Pattern.pr"),
    ),
    (
        "Syntax.Parse.Expr",
        include_str!("../lib/std/Syntax/Parse/Expr.pr"),
    ),
    (
        "Syntax.Parse.DeclClass",
        include_str!("../lib/std/Syntax/Parse/DeclClass.pr"),
    ),
    (
        "Syntax.Parse.DeclStable",
        include_str!("../lib/std/Syntax/Parse/DeclStable.pr"),
    ),
    (
        "Syntax.Parse.Decl",
        include_str!("../lib/std/Syntax/Parse/Decl.pr"),
    ),
    ("Syntax.Parse", include_str!("../lib/std/Syntax/Parse.pr")),
    (
        "Syntax.Resolved",
        include_str!("../lib/std/Syntax/Resolved.pr"),
    ),
    ("Syntax.Edit", include_str!("../lib/std/Syntax/Edit.pr")),
    ("Syntax.Rename", include_str!("../lib/std/Syntax/Rename.pr")),
    ("Syntax.Flow", include_str!("../lib/std/Syntax/Flow.pr")),
    (
        "Syntax.Identity",
        include_str!("../lib/std/Syntax/Identity.pr"),
    ),
    (
        "Data.Validation",
        include_str!("../lib/std/Data/Validation.pr"),
    ),
    (
        "Control.Validate",
        include_str!("../lib/std/Control/Validate.pr"),
    ),
    (
        "Data.UnionFind",
        include_str!("../lib/std/Data/UnionFind.pr"),
    ),
    (
        "Data.UnionFind.Payload",
        include_str!("../lib/std/Data/UnionFind/Payload.pr"),
    ),
    ("Data.Name", include_str!("../lib/std/Data/Name.pr")),
    ("Data.Scope", include_str!("../lib/std/Data/Scope.pr")),
    ("Data.Bind", include_str!("../lib/std/Data/Bind.pr")),
];
