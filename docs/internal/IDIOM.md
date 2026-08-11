# Idiomatic Prism: the bootstrap style guide

How compiler-shaped Prism is written. The audience is anyone, human or tool, writing the self-hosted compiler under `packages/tc` and `lib/std/Syntax`, or any library those lean on. The thesis: Prism beats the Rust it mirrors on size only when it stops being a translation. The wins come from deleting structure the language makes unnecessary (ownership ceremony, context plumbing, hand-written recursion, hand-written instances), never from squeezing syntax. When a Prism pass reads longer than its Rust counterpart, the miss is almost always a missing abstraction, a layer not supplied, an effect not bundled, a derive not used. Fix the library, not the call site.

## The design in one paragraph

The self-hosted compiler is a pure structural core wrapped in a thin effectful spine. Structural operations (normalization, free variables, substitution, zonking, canonical forms, pretty printing) are pure functions over ADTs. Every stateful concern (the union-find forests, the metavariable supply, the diagnostic stream) is one effect, handled once at the pass edge, and the stateful region is kept small so the compiler confines it. Passes are rule sets over generic traversals, not hand-written recursions. Every canonical form has exactly one owner, and everything that claims agreement with the Rust compiler is pinned differentially through the versioned artifact seams, never by eyeball.

## The worked models: read these before writing checker code

The bootstrap libraries were written to be copied from. Each one settles a design question; do not re-litigate it at a new call site.

- `examples/systemf.pr` is the whole pipeline in miniature and the first thing to read. Its lessons, each of which scales up unchanged: a string-spelled surface tree and an identity-carrying resolved tree are two separate types, and one resolution walk (minting `Data.Name` binders over `Control.Fresh`, resolving references through a lexical `Data.Scope`) is the only code that ever sees a spelling. Substitution downstream is a structural walk comparing identities, so capture is impossible and runtime freshening does not exist. Unbound names are refused at resolution, which is what lets every later pass assume every reference is bound. Metavariables are classes in the payload union-find whose root owns the one descriptor, so there is no shadow solution map to keep aligned.
- `packages/tc` is the same shape at scale: the split value/computation type grammar, rows normalized by one owner (`row_normalize`, and every consumer normalizes first), the solver as a `State` cell plus an aborting error confined to the checking region, and pure structural operations everywhere else. New checker code extends this file's discipline; it does not invent a second one.
- `lib/std/Syntax` is the seam layer: `Codec` and `TcInput` decode versioned artifacts fail-closed (duplicate ids and out-of-bounds spans are refusals, never repairs), `Walk` supplies the surface tree's layer, `Diagnostic` carries errors as data. Anything that consumes compiler output goes through these, never through ad-hoc string parsing of a dump.
- `Data.Scope` encodes the binding discipline: scopes are persistent, entering a binding is passing an extended scope down, leaving is just returning. Nothing is ever popped on an exit path, so there is no cleanup to forget.
- `Data.Pretty` is the one rendering engine. Types, rows, and diagnostics render through `Doc` combinators (`group`, `nest`, `join_docs`), never through string concatenation with hand-managed widths.

## Effects: the spine idiom

- One effect per concern, ops bundled by what is handled together. The checker's model: one `State` cell holds both solver forests, one aborting error carries failure, `run_tc` installs both at the edge and everything inside reads as direct style.
- Handlers live at pass edges only. A helper never installs a handler to satisfy itself; it declares its row and lets the caller discharge it. The traversal library is the model: no combinator in `Control.Rewrite` handles, masks, or requires an effect.
- Every higher-order signature carries the open tail `! {| e}`. One function then serves pure and effectful callers alike; the pure case is the same code at the empty row. Never write a `_pure` and `_eff` pair of the same function.
- Aborting failure is a `never` op discharged at the edge, not a `Result` threaded through every return type. `Result` belongs at boundaries (file IO, artifact decoding, the public API of a runner), not inside a pass.
- Prefer tail-resumptive, cell-style handlers (`Control.State`, `Control.Fresh`, `Control.Reader`, `Control.Writer`). They are the cheap tier. Reach for multishot resumption only when the pass genuinely searches.
- Write the pass against the ops, never against a handler. Swapping the handler swapping the policy (solver strategy, scheduler, trace collection) is the property to preserve.
- Environment-like context is `Reader`, not a parameter threaded through fifteen signatures. Accumulation is `Writer` or a `State` cell, not an accumulator argument snaking through the recursion.

## Traversals: never write the recursion

- A sort joins the generic library by supplying a `Layer` (its `kids` and `rebuild` pair), or by deriving `Plate` once the derive exists, and nothing else. Every strategy in `Control.Rewrite` and every query in `Control.Layer` then comes free. If you are writing a recursive match whose arms all rebuild the same shape, stop: that is a layer traversal.
- A pass is a list of local rules. A rule is `(a) -> Option(a) ! {| e}` where `None` means "not here". Compose with `rw_or_else` chains (first match wins, exactly as a hand-written match would), scope with `rw_at` and `rw_where`, make total with `rw_try`, finish with `rw_apply`. A rule list reads as a spec; a monolithic recursion does not.
- Prefer many small named rules over one clever one. Each rule is testable alone, and the composition order is visible at the one place the pass is assembled.
- Fixpoints take explicit fuel and report convergence. A diverging rule set must be a failed assertion, never a hang.
- Collecting is a query, not a fold you write: `expr_universe`, the layer queries, `collect_of` on a `Traversal`. Hand-written folds are for genuinely local, one-off shapes.
- Traversal order is structural: root first, children in `kids` order, which is source order for the surface tree. Nothing may consult a structure with unstable iteration order mid-walk.

## Errors and diagnostics

- Diagnostics are values (`Syntax.Diagnostic`), never strings. A message formats at the edge, not at the raise site.
- Fatal is `refute`, record-and-continue is `dispute`, and a subtree that should fail without killing the pass is fenced with `tolerate` (`Control.Validate`). This replaces both the error-accumulator plumbing and the "collect then check emptiness" pattern from the Rust side.
- Encounter order is the deterministic order. Errors report in the order the walk met them, which is a pure function of the tree.

## Identity, interning, and stores

- Identity is branded: `Data.Name` with a distinct space per namespace (`packages/tc` separates type-variable and row-variable spaces; `systemf.pr` separates term and type spaces), so one kind of identity can never stand where another belongs. Never a string, never an unbranded `Int` for anything unification can confuse.
- Spellings die at resolution. After the one resolution walk, a spelling survives only as a `Binder` hint for presentation; any comparison, lookup, or substitution downstream that touches a spelling instead of a `Name` is a bug even when it happens to work.
- Facts travel as data, never inside name spellings. The Rust-side rule holds identically here: no prefix sniffing, no parsing a fact back out of a generated name.
- Metavariable classes live in the payload union-find (`ufp_find`, `ufp_set`, `ufp_union_with`), so solving a class solves every alias of it. Never a map from meta to type with manual chasing.
- Dense integer keys get `Data.IntMap` and `Data.IntSet`. Solver tables should be benchmarked persistent-versus-cell under the real workload before committing to either.
- Interned terms are matched through `pattern` declarations, so checker code reads as constructor shapes and the dense-id indirection stays invisible at use sites.

## Deriving: never write what the compiler writes

- `Eq, Show` on every ADT by default. `Serialize` and `Stable` at artifact seams. `Lens` on record-heavy state. `Plate` on tree sorts the day it exists. `Arbitrary` on anything a law suite touches.
- If you find yourself writing an equality, a printer, a field accessor chain, a child list, or a generator by hand, check the deriving list first. A hand copy of derivable code is a drift bug waiting for its rename.

## Optics on state

- Nested state updates go through lens composition and the `State`-integrated helpers (`gets_at`, `set_at`, `modify_at`, `modify_all_at`), never through record-update pyramids that rebuild every enclosing record by hand.
- Bulk updates are a `Traversal` (`over_all`, `set_all`), and effectful bulk updates are `traverse_of_eff`. The optic names the focus once; the update site stays one line.

## Concision: why the Prism is shorter, and how to keep it that way

- Where the Rust is long because of ownership (clones, borrows, lifetimes, boxing, interior mutability), the Prism is short by construction: persistent values, free sharing. Do not re-import defensive copying out of habit.
- Where the Rust is long because of plumbing (context parameters, `Result` chains, visitor traits, duplicated mutable/immutable variants), the Prism deletes the plumbing with effects, layers, optics, and deriving. This is the bulk of the ratio.
- Where the Rust is genuinely dense logic (the unification case analysis, the occurs check), the Prism should be about the same length. Do not force point-free tricks to win characters; compression comes from deleting structure, not squeezing syntax.
- Every public function carries a `-- |` doc comment, and the ones with interesting behavior carry a runnable spec block. The example is a test; a spec block that would go stale is a spec block doing its job.
- The size claim is a measured ratio on a committed corpus, never a vibe. When the number is bad, look for the missing abstraction before editing call sites.

## Anti-patterns: translation smells

Each of these is correct Rust idiom faithfully transliterated into the wrong language. Seeing one in review means the translation went word-by-word.

- A record named `ctx` or `env` threaded through every signature. That is a `Reader`, or a `State` cell if it mutates.
- `Result(a, e)` on internal helpers with unwrap-or-propagate at every call. That is a `never` op discharged at the pass edge.
- A recursive function matching every constructor to rebuild the same shape. That is a `Layer` traversal.
- A fifty-arm match where three arms change something and the rest recurse. That is `rw_try` of a three-rule rewrite applied everywhere.
- Boolean or config parameters passed down a call chain unchanged. `Reader`.
- An accumulator list built backwards and reversed at the return. `Writer`, or a local fold if it never crosses a function boundary.
- Pure and effectful variants of the same function. One function, open row.
- String-keyed maps for identities, or a fact encoded in a name and parsed back later. Branded `Name`, or a field.
- A hand-written `show` used by tests as an equality proxy. Derive both.

## Module and naming hygiene

- The top-level namespace is flat and one definition per name wins. Before adding any public helper, sweep the stdlib and prelude for the name; a collision silently rebinds and the checker multiplies name count enough to make this the dominant hazard.
- Families take a short module prefix (`rw_`, `ufp_`, `row_`) so related operations sort and grep together.
- Import lists are explicit. `(..)` is reserved for modules designed as a vocabulary (`Control.State` at a handler edge), never used to save typing.
- House traps that cost a round trip each: it is `Option`, not `Maybe`; constructor patterns do not go in `fn` parameters; `not` needs its parentheses; `char_at` yields an `Int` that needs `chr`.

## Determinism and termination obligations

- Every observable order is a pure function of the tree: `kids` order, error encounter order, emission order. Nothing iterates a hash map.
- Recursion is structural through `kids` wherever the discipline can hold; fuel with a convergence report covers the loops a rewrite creates by feeding its own output back in.
- The pure/effectful split is also the performance story: the smaller and tighter the stateful region, the better the confinement and the faster the native tier. Read what `tier-explain` says about the checker's own regions instead of guessing, and keep the solver loop's allocations inside the region it names.
- Hot read-only paths follow the stdlib's own convention: `borrow` on parameters that are only inspected, and `@ noalloc` on the small accessors that can honor it (`name_id`, `intern_size` are the models). These are claims the compiler checks, so state them where they hold and nowhere else.
