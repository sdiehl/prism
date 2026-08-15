# Projects and Content Identity

A tutorial should end with more than isolated snippets. This chapter assembles a small package, splits it into modules, runs its tests, and then inspects the content identities Prism assigns to its definitions.

## Create the project

Run the interactive initializer and choose `rainbow` as the package and directory name. Use `0.1.0` for the version, your own author and maintainer details, and the license you intend to publish under:

```shell
prism pkg init
cd rainbow
```

The project begins with a manifest and one source file:

```text
rainbow/
├── prism.toml
└── src/
    └── main.pr
```

Use this manifest:

```toml
[package]
name = "rainbow"
version = "0.1.0"
authors = ["Your Name <you@example.com>"]
maintainers = ["you@example.com"]
license = "MIT"

[bin]
entry = "src/main.pr"
```

## Put pure domain logic in a module

Create `src/Colour.pr`:

```prism,no_run
pub type Band
  = Violet
  | Blue
  | Green
  | Warm
  deriving (Eq, Show)

pub fn band(wavelength : Int) : Band =
  if wavelength < 450 then
    Violet
  elif wavelength < 495 then
    Blue
  elif wavelength < 570 then
    Green
  else
    Warm

pub fn name(value : Band) : String =
  match value of
    Violet => "violet"
    Blue => "blue"
    Green => "green"
    Warm => "yellow, orange, or red"

test fn green_is_classified() =
  if band(530) == Green then
    ()
  else
    fail()

test fn warm_name_is_readable() =
  if name(Warm) == "yellow, orange, or red" then
    ()
  else
    fail()
```

A file is a module. `pub` exports a declaration. Declarations without `pub` are private to that file. The tests can still use private declarations in their own module.

Now replace `src/main.pr`:

```prism,ignore
import Colour (band, name)

fn main() =
  let wavelength = 530
  let result = band(wavelength)
  println("{wavelength}nm is {name(result)}")
```

The imported names come from `src/Colour.pr`. An unqualified `import Colour` would keep them behind `Colour.band`. `import Colour (band, name)` also brings those two exports into bare scope.

The complete project is checked in with Prism's documentation examples, so the multi-file version is tested even though this individual import block cannot run on its own.

## Check, test, and run

From the project directory:

```shell
prism fmt src
prism check
prism test
prism run .
```

The final command prints:

```output
530nm is green
```

`prism test` discovers `test fn` declarations throughout project-owned modules. A test passes by returning `Unit`. Calling `fail()` or leaving a fault unhandled fails it. Each test receives a fresh interpreter world, so effects and state cannot leak from one test to another.

Tests are deliberately production-neutral. Normal builds remove test declarations before module interfaces, executable Core identities, and native artifacts are computed. Improving a test does not change the program being shipped.

## Read a diagnostic as a workflow

Change `Green` to the misspelling `Gren` in the first test and run `prism test`. A useful diagnostic answers three questions:

1. Where is the problem?
2. What fact did the compiler expect?
3. Is there a mechanical repair it can suggest?

Prism diagnostics include a stable `E`-code. Run `prism explain CODE` with the printed code for a longer explanation and a minimal fixed example. Then restore `Green` and rerun the test.

For an unfinished expression, a named typed hole such as `?result` asks a slightly different question: what type and effects must fit here?

```prism,ignore
fn double(n : Int) : Int = ?result
```

On a local file, `prism check FILE --at-hole` reports the expected type, permitted effects, and matching values in scope. Holes make incomplete code a structured compiler query rather than a comment the compiler cannot see.

## Source text is not semantic identity

Most tools identify a function by a filename and name, or cache it using a hash of its source bytes. That makes comments, formatting, and local variable names look like behavioral changes.

Prism hashes the elaborated, pre-optimization Core instead:

```shell
prism dump core-hash .
```

Try this small experiment:

1. Save the reported hashes.
2. Rename `wavelength` to `nm` inside `band`, or change only a comment.
3. Format the file and dump the hashes again.
4. Change the boundary `450` to `451` and dump them a third time.

Bound variables are normalized by position, while comments, source spans, and formatting are erased. The first edit therefore leaves `band`'s Core identity unchanged. The numerical edit changes what the definition computes, so its hash moves.

You do not normally need to compare those hash dumps by hand. Put the starting version in Git, make the same edits, and ask Prism for the semantic diff:

```shell
git init
git add prism.toml src
git commit -m "Start rainbow"

# Edit src/Colour.pr, then:
prism diff
```

Bare `prism diff` compares Git `HEAD` with the whole working tree, including staged changes. It reports definitions whose Core identity changed, shows a compact source patch, and names the dependent definitions affected by the change. A comment-only or formatting-only edit has no semantic changes to report. To compare two explicit revisions instead, pass two files, project directories, or manifests: `prism diff OLD NEW`.

The hash commits to more than the expression tree. It also includes elaboration facts an importer relies on, including the generalized type, principal effect row, allocation mode, and borrow mask. Changing a public contract therefore changes identity even if a similar-looking body remains.

Those facts are inspectable too. The command for auditing the project-owned functions in the checked program is:

```shell
prism dump usage-summary .
```

For the rainbow project it includes:

```text
# prism-usage-summary-v1  tier=pure
# name        noalloc  discipline  borrow  row
Colour.band  no       -           -       {}
Colour.name  no       -           -       {}
main         no       -           -       {IO}
```

The final column is each function's checked effect row: `band` and `name` are pure, while `main` performs `IO`. The other columns expose the allocation certificate, `fip`/`fbip` discipline, and parameter borrow mask that also feed semantic identity. Use `usage-summary-md` for a Markdown table or `usage-summary-json` for tooling.

## Definitions form a Merkle graph

When one top-level definition refers to another, Prism places the dependency's hash into the caller's identity. A changed `band` therefore affects definitions that depend on its behavior, while an unrelated definition can retain its identity.

This turns the program into a Merkle graph:

```text
band hash ──▶ caller hash ──▶ module/package root
name hash ──▶ caller hash
```

Names remain a human-facing index over that graph. A top-level rename can leave the definition's anonymous Core object unchanged while moving the named namespace entry. Packages and the standard library are pinned by roots over their definitions and declared shapes:

```shell
prism dump stdlib-hash .
```

This supports precise rebuilds, reproducible package pins, lineage, and replay: unchanged content already has a stable name, and a change propagates through its dependency closure.

One limit matters. A Core hash is not a proof that all differently written programs with the same mathematical result will be recognized as equivalent. Equal identities name the same canonical compiler form under Prism's hashing scheme. Unequal identities do not prove that two programs could never behave the same.

## What you can now build

The project is intentionally small, but it contains the complete beginner workflow:

- immutable pure functions model the domain.
- an algebraic data type names every output category.
- pattern matching covers those categories.
- module visibility separates an API from its implementation.
- tests exercise the pure core.
- `main` owns the observable output boundary.
- content identities reveal which semantic artifacts changed.

Extend it by accepting several readings, processing them as a fused stream, and returning `Option(Band)` for wavelengths outside the visible range. Add a custom effect that supplies readings, then write one handler with fixed test data and another with a real input capability. That exercise revisits every major idea without changing the pure classification logic.

Next, [The Prism Way](./prism-way.md) condenses those ideas into habits worth carrying into larger programs.

**Further reading:** [modules](../spec.md#modules), [projects](../spec.md#projects), [test declarations](../spec.md#test-declarations), [typed holes](../compiler.md#typed-hole-workflow), and [content-addressed Core](../compiler.md#content-addressed-core).

The future of code review will be less about staring at ever larger diffs and more about asking which guarantees moved. As LLMs make code cheap to produce, review becomes the scarce and critical act, and textual plausibility is no longer enough. Advanced static types can expose a change's effects and resource contracts, while a Merkle closure can trace those facts through every caller whose behavior depends on them. Prism brings these views together. `prism diff` identifies the semantic change and its affected cone, while the usage summary reveals the checked effect rows and resource promises inside that cone. The result is a review process built around static evidence about what code can do and where its consequences travel, which makes machine-generated changes far easier to audit than a raw patch ever could.
