# Changelog

## 0.2.0 (unreleased)

- Fixed-width bitwise and shift builtins on the I64/U64 lanes: `i64_and`/`i64_or`/`i64_xor`/`i64_shl`/`i64_shr` and their `u64_*` counterparts. and/or/xor share one bit pattern across lanes; `i64_shr` is arithmetic, `u64_shr` logical; shift counts are taken modulo 64.
- `system(String) -> Int` runs a shell command and returns its exit code, and `eprint`/`eprintln` write to stderr, so a program can drive external tools and emit diagnostics off the stdout stream.
- Superclasses: a class may declare another as a superclass (`class Ord(a) given Eq(a)`). Each instance carries a resolved superclass dictionary as a leading field of its dict cell, and a `given Ord(a)` constraint discharges an `Eq(a)` obligation by projecting it, found automatically from the instances in scope. The prelude's `Ord` now requires `Eq`.
- Growable mutable `Array(a)` (`array_new`/`array_empty`/`array_len`/`array_get`/`array_set`/`array_push`), an ordinary reference-counted heap cell so drops recurse into its elements. `array_set` and `array_push` write in place when the array is uniquely owned (FBIP) and copy otherwise; `array_push` doubles capacity when full, so appends are amortized O(1). The prelude adds `array_of_list`.
- `string_of_array` and the prelude `concat_all`/`array_of_list` build a string from many chunks in a single allocation, replacing the quadratic right-nested `concat` chain.
- Prelude `HashMap(v)`: a separate-chaining hash table with String keys built on the growable array (`hm_new`/`hm_insert`/`hm_lookup`/`hm_member`/`hm_get_or`/`hm_keys`/`hm_values`/`hm_size`/`hm_to_list`/`hm_delete`/`hm_from_list`/`hm_adjust`), doubling its bucket count past load factor 1. Keys hash by a fixed-width FNV-1a written in the language, so iteration order is a deterministic function of the inserts.
- O(1) byte access: `byte_at`/`byte_len` (UTF-8 unaware) and `string_of_bytes`, so a lexer or hash scans raw bytes in linear time. `array_pop` rounds out the array API, and `array_foldl`/`array_to_list` are added to the prelude.
- Surface fixed-width arithmetic: `i64_*`/`u64_*` `add`/`sub`/`mul`/`div`/`rem`/`cmp` (wrapping, no bignum promotion), enabling a real fixed-width hash in userland.
- Higher-kinded types: a class parameter may range over a type constructor (kind `* -> *`), applied as `f(a)` in method signatures, with instance resolution keyed on the head constructor. The prelude adds the `Functor`/`Applicative`/`Monad`/`Foldable`/`Traversable` tower with `List` and `Option` instances. `fmap`/`traverse` are effect-polymorphic, so the per-element effect row threads through instead of an `Applicative` wrapper (effects, not do-notation).
- String-utility prelude: character classifiers (`is_digit`/`is_alpha`/`is_alnum`/`is_space`/`is_upper`/`is_lower`, `to_upper_c`/`to_lower_c`), `starts_with`/`ends_with`/`contains`/`index_of`, `to_upper`/`to_lower`/`trim`, and `args()`.
- `prism fmt` separates top-level declarations with a blank line and keeps `>>`/`<<` function composition as surface sugar (printing `f >> g` rather than expanding it to a lambda), so formatting round-trips these forms.
- Editor tooling: a dependency-free Neovim highlighter under `scripts/nvim/` (an `ftdetect/` filetype map for `*.pr` plus a `syntax/` highlighter), with its keyword set mirrored from `src/lex/token.rs` so it tracks the lexer.
- A project and module system. A `prism.toml` manifest (`[package] name`, `[bin] entry`) plus a `src/` tree make a multi-file project that `prism run`/`build` compiles, resolving module paths from the project root rather than the entry file's directory (single-file invocation is unchanged). Name resolution now canonicalizes every top-level definition to a module-qualified symbol (`Data.Map.insert` for exports, `Data.Map@helper` for privates), so qualified references (`M.x`) reach disjoint namespaces and two modules may export the same short name and coexist; selective imports (`import M (a, b)`) bring only the listed names into bare scope, and `pub` controls what an importer can reach. Instances record their defining module: an orphan instance (defined apart from both its class and its type) and instances overlapping across modules are reported as warnings, and an ambiguity names each candidate's module.
- Module-system follow-ups: `pub import M (x)` re-exports the named items through the importing module, with chains resolving transitively to the original definition; a module's full dotted path qualifies a reference (`Geo.Util.one`), not only its last component (`Util.one`); and orphan/overlapping-instance warnings render with a source caret when they point into the program being compiled.
- Static `fip`/`fbip` checking of the FP^2 discipline. `fbip` proves zero fresh allocation and that an annotated body calls only annotated, allocation-free functions; `fip` additionally proves linearity (each owned non-immediate binding consumed at most once, checked on the source term with scalars exempt) and bounded stack (every recursive call in the call-graph SCC is a tail call or a single tail-modulo-cons/-add). The tail/TRMC classification is shared with codegen (`src/core/tailrec.rs`), so an accepted `fip` function always lowers to a loop; `fip` may call only `fip`, `fbip` may call either. Recursive accumulator/TRMC functions like `rev_onto` and `bump` now type-check as `fip` and run in constant heap and stack.

## 0.1.0

Initial release.

- Strict, impure functional language with ML-family surface syntax: ADTs, pattern matching, parametric polymorphism, and a prelude of `Option`/`Result`/`List`/`Map` combinators.
- Hindley-Milner type inference with bidirectional, higher-rank (rank-N) checking and subsumption.
- Type classes by dictionary passing, with named instances and `deriving (Eq, Ord, Show)`.
- Algebraic effects and handlers: inferred, extensible effect rows via row polymorphism; multishot `resume`; `final ctl` non-resumable clauses; scoped/masked handlers and forwarding.
- Evidence-passing compilation of handlers, with tail-resumptive clauses lowered to direct calls and a free-monad fallback when effects escape tracking.
- Exhaustiveness and redundancy checking, plus decision-tree pattern-match compilation.
- First-class optics: record-update paths, view patterns, bidirectional pattern synonyms, and `deriving (Lens)`.
- Stream fusion: effectful producer/transformer/consumer pipelines fuse to zero intermediate allocations.
- Verse-inspired failure model (`fail`, `guard`, `??`, `?.`, `transact`) and structured error handling, both built on effect handlers.
- Deterministic memory management via Perceus reference counting with in-place reuse (FBIP), no garbage collector.
- Call-by-push-value core in A-normal form with tail-call optimization and tail recursion modulo cons.
- Three backends kept byte-identical: a tree-walking interpreter, native code via LLVM, and a text-MLIR backend.
- Lean model of the core with a machine-checked determinism theorem.
- Compiles to WebAssembly, so the language runs in the browser.
- Tooling: interactive shell, `run`, `build`, `check`, `fmt`, and phase `dump`.
