#![allow(clippy::multiple_crate_versions)]

use std::process::{self, ExitCode};

use clap::{Parser, Subcommand};
use prism::cli::{self, CmdResult, ExampleStdin};
use prism::error::Error;
use std::path::{Path, PathBuf};

const DEFAULT_EXAMPLES_DIR: &str = "examples";

// A CLI argument struct is the canonical exception to `struct_excessive_bools`:
// the `--no-<pass>` flags and `--mlir` are independent on/off switches, exactly
// what clap models as bool fields, not a state machine.
#[allow(clippy::struct_excessive_bools)]
#[derive(Parser, Debug)]
#[command(
    name = "prism",
    version,
    about = "A modern typed functional language with a call-by-push-value core that lowers to LLVM",
    args_conflicts_with_subcommands = true
)]
struct Cli {
    #[command(subcommand)]
    cmd: Option<Cmd>,
    /// A `.pr` file or project to compile; no path starts the REPL
    file: Option<PathBuf>,
    /// Output path for the compiled binary
    #[arg(short, long)]
    out: Option<PathBuf>,
    /// Use the MLIR backend instead of LLVM
    #[arg(long)]
    mlir: bool,
    /// Core optimizer level (0-2; bare -O is highest)
    #[arg(
        short = 'O',
        long = "opt",
        value_name = "LEVEL",
        global = true,
        num_args = 0..=1,
        default_missing_value = "2"
    )]
    opt: Option<String>,
    /// Explicit pass list, overriding -O (see docs)
    #[arg(long = "passes", value_name = "SPEC", global = true)]
    passes: Option<String>,
    /// C-compiler optimization level for the emitted code (0-3, s, z)
    #[arg(long = "backend-opt", value_name = "LEVEL", global = true)]
    backend_opt: Option<String>,
    /// Default cooperative scheduler policy (cooperative or lifo)
    #[arg(long = "scheduler", value_name = "POLICY", global = true)]
    scheduler: Option<String>,
    /// Disable the newtype-erasure pass
    #[arg(long, global = true)]
    no_erase_newtypes: bool,
    /// Disable the dictionary-specialization pass
    #[arg(long, global = true)]
    no_specialize: bool,
    /// Disable the simplifier pass
    #[arg(long, global = true)]
    no_simplify: bool,
    /// Disable the inliner pass
    #[arg(long, global = true)]
    no_inline: bool,
    /// Disable the scalar-CSE pass
    #[arg(long, global = true)]
    no_cse: bool,
    /// Force stream fusion of pull-Sequence pipelines below -O2 (on at -O2)
    #[arg(long, global = true)]
    fuse: bool,
    /// Disable the stream-fusion pass
    #[arg(long, global = true)]
    no_fuse: bool,
    /// Disable the native effect driver
    #[arg(long, global = true)]
    no_native_effects: bool,
    /// Disable the free-monad trampoline
    #[arg(long, global = true)]
    no_trampoline: bool,
    /// Run Core Lint between optimization passes
    #[arg(long, global = true)]
    core_lint: bool,
    /// Print per-pass rewrite counts to stderr
    #[arg(long, global = true)]
    opt_stats: bool,
    /// Print compiler-query hit, miss, and write counts
    #[arg(long, global = true)]
    compiler_stats: bool,
    /// Explain native artifact cache decisions after a build
    #[arg(long, global = true)]
    explain_cache: bool,
    /// Worker count for independent compiler queries
    #[arg(long, value_name = "N", global = true)]
    query_threads: Option<usize>,
    /// Emit one timing row per compiler phase to stderr
    #[arg(long, global = true)]
    time_compile: bool,
    /// Print effect-lowering fusion-fallback warnings to stderr (off by default)
    #[arg(long, global = true)]
    verbose: bool,
    /// Disable the persistent compiler artifact cache
    #[arg(long, global = true)]
    no_compiler_cache: bool,
    /// Dump Core after each pass to SINK (stdout, stderr, or a directory)
    #[arg(long = "dump-core", value_name = "SINK", global = true)]
    dump_core: Option<String>,
    /// Flag your own definitions sharing a behavior hash: `warn` reports them,
    /// `strict` fails the build (bare `--warn-dupes` is `warn`; off by default)
    #[arg(
        long = "warn-dupes",
        value_name = "LEVEL",
        global = true,
        num_args = 0..=1,
        require_equals = true,
        default_missing_value = "warn"
    )]
    warn_dupes: Option<String>,
    /// Flag a definition that reimplements a standard-library function: `warn`
    /// (default) reports it, `strict` fails the build, `off` silences it
    #[arg(
        long = "warn-stdlib-dupes",
        value_name = "LEVEL",
        global = true,
        num_args = 0..=1,
        require_equals = true,
        default_missing_value = "warn"
    )]
    warn_stdlib_dupes: Option<String>,
}

#[derive(Subcommand, Debug)]
enum Cmd {
    /// Type-check and run in the interpreter
    Run {
        /// A `.pr` file or project to run
        file: Option<PathBuf>,
        /// Run every `.pr` file under DIR, or `examples/` when DIR is omitted
        #[arg(long, value_name = "DIR", num_args = 0..=1, default_missing_value = DEFAULT_EXAMPLES_DIR)]
        examples: Option<PathBuf>,
        /// Stdin policy for `--examples`
        #[arg(long = "stdin", value_enum, default_value_t = ExampleStdin::Fixture)]
        stdin: ExampleStdin,
        /// Capture the run's trace to a `.replay` file
        #[arg(long, value_name = "PATH")]
        record: Option<PathBuf>,
        /// Write a run-lineage sidecar (requires `--record`, which it explains)
        #[arg(long, value_name = "PATH", requires = "record")]
        lineage: Option<PathBuf>,
        /// Persist observations to a crash-safe log at PATH and resume from it
        #[arg(long, value_name = "PATH", conflicts_with = "record")]
        durable: Option<PathBuf>,
        /// Defer typed holes to deterministic interpreter faults
        #[arg(long)]
        defer_holes: bool,
        /// Program arguments, separated from compiler arguments by `--`
        #[arg(last = true, value_name = "ARG")]
        args: Vec<String>,
    },
    /// Compile the enclosing project to a native binary
    Build {
        /// Where to start the search for the project's `prism.toml`
        #[arg(default_value = ".")]
        path: PathBuf,
        /// Output path for the compiled binary
        #[arg(short, long)]
        out: Option<PathBuf>,
        /// Use the MLIR backend instead of LLVM
        #[arg(long)]
        mlir: bool,
    },
    /// Remove the build-artifact directory (`target/`)
    Clean {
        /// Where to start the search for the project's `prism.toml`
        #[arg(default_value = ".")]
        path: PathBuf,
    },
    /// Type-check a file, or the enclosing project when FILE is omitted
    Check {
        /// A `.pr` file or project to type-check; omitted checks the enclosing project
        file: Option<PathBuf>,
    },
    /// Discharge a file's function contracts through an external SMT solver
    Verify {
        /// A `.pr` file whose `requires`/`ensures` contracts to verify
        file: PathBuf,
        /// Solver executable (found on PATH, or an absolute path)
        #[arg(long, value_name = "SOLVER", default_value = "z3")]
        solver: String,
        /// Discharge with several solvers (comma-separated); with
        /// --require-agreement every one must report unsat
        #[arg(long, value_name = "SOLVERS", value_delimiter = ',')]
        solvers: Vec<String>,
        /// Require every selected solver to agree on unsat; any split fails closed
        #[arg(long)]
        require_agreement: bool,
    },
    /// Print one pipeline phase artifact
    ///
    /// PHASE is one of: tokens, ast, types, hir, interface, module-graph, core,
    /// core-json, core-hash, tc-input, tc-facts, elab-input, native-kont-table,
    /// native-kont-state-map, shape, dupes, namespace, stdlib-hash, fbip, lowered,
    /// tier, captures, usage-summary, usage-summary-md, usage-summary-json,
    /// llvm, mlir, verify, smt, totality.
    Dump { phase: String, file: PathBuf },
    /// Behavior or lineage diff by content hash
    ///
    /// With no revisions, diff the enclosing project's Git HEAD against the
    /// working tree. Two source revisions (a `.pr` file, directory, or
    /// `prism.toml`) diff by Core hash; two `.plineage` sidecars by logical key.
    Diff {
        /// The old revision, or a `.plineage` sidecar (requires NEW)
        #[arg(requires = "new")]
        old: Option<PathBuf>,
        /// The new revision, or a `.plineage` sidecar (requires OLD)
        #[arg(requires = "old")]
        new: Option<PathBuf>,
        /// Print the sidecar diff as JSON (lineage sidecars only)
        #[arg(long)]
        json: bool,
    },
    /// Print every pipeline phase for a program
    Report { file: PathBuf },
    /// Start the interactive shell
    Repl {
        /// Skip the startup banner
        #[arg(long)]
        no_banner: bool,
    },
    /// Format source files in place
    Fmt {
        /// Files or directories to format; `-` for stdin, default current dir
        files: Vec<PathBuf>,
        /// Check only: exit 1 if any file is not canonical, write nothing
        #[arg(long)]
        check: bool,
    },
    /// Generate Markdown API docs from doc comments
    Docs {
        /// Project directory, `prism.toml`, or `.pr` file to document
        #[arg(default_value = ".")]
        path: PathBuf,
        /// Output directory (default: `<project>/target/docs`)
        #[arg(short, long)]
        out: Option<PathBuf>,
        /// Document the embedded standard library instead of `path`
        #[arg(long)]
        stdlib: bool,
        /// Run the doctests (`prism` blocks in doc comments) instead of writing
        #[arg(long)]
        test: bool,
        /// Rewrite stale/empty `output` expectation blocks with the actual output
        /// (implies `--test`); exits nonzero if anything was rewritten
        #[arg(long, visible_alias = "bless")]
        accept: bool,
        /// Check only: exit 1 if any committed page is out of date, write nothing
        #[arg(long)]
        check: bool,
        /// Verify the committed docs manifest against the pages in the output
        /// directory (rehash pages, confirm roots have not drifted); write nothing
        #[arg(long)]
        verify_manifest: bool,
        /// Open the generated index after writing
        #[arg(long)]
        open: bool,
    },
    /// Execution control over recorded runs and snapshots
    #[command(subcommand)]
    Exec(ExecCmd),
    /// Inspect and verify lineage sidecars
    #[command(subcommand)]
    Lineage(LineageCmd),
    /// Explain an artifact from its lineage sidecar, without reading source
    WhyOutput {
        /// The built artifact or its `.plineage` sidecar
        artifact: PathBuf,
        /// The output to explain: a path or the literal `stdout`; defaults to the
        /// sidecar's primary output
        output: Option<String>,
        /// Print the explanation as JSON instead of prose
        #[arg(long)]
        json: bool,
    },
    /// Package manager and store-publishing verbs
    #[command(subcommand)]
    Pkg(PkgCmd),
    /// Discover and run `test fn` declarations
    Test {
        /// A `.pr` file or project to test (defaults to the current project)
        file: Option<PathBuf>,
        /// Substring filter over logical test IDs
        filter: Option<String>,
        /// Match FILTER as a complete logical ID
        #[arg(long)]
        exact: bool,
        /// Discover and print matching tests without running
        #[arg(long)]
        list: bool,
        /// Compile the selected test targets without executing
        #[arg(long)]
        no_run: bool,
        /// Output format: human or json
        #[arg(long, value_name = "FMT", default_value = "human")]
        format: String,
        /// Show captured output for successful tests too
        #[arg(long)]
        show_output: bool,
        /// Make an empty selection a command failure
        #[arg(long)]
        fail_if_no_tests: bool,
    },
    /// Content-addressed store verbs
    #[command(subcommand)]
    Store(StoreCmd),
    /// Digest-pinned semantic patch verbs
    #[command(subcommand)]
    Patch(PatchCmd),
    /// mdbook preprocessor for `prism` code blocks
    #[command(hide = true)]
    Mdbook {
        /// mdbook passes `supports <renderer>` here; the book JSON otherwise
        /// arrives on stdin.
        #[arg(trailing_var_arg = true, allow_hyphen_values = true)]
        rest: Vec<String>,
    },
}

/// The execution-control family: reproduce, step, pause, and resume runs.
#[derive(Subcommand, Debug)]
enum ExecCmd {
    /// Reproduce a recorded run from a `.replay` trace
    Replay {
        /// The program the trace was recorded against
        file: PathBuf,
        /// The `.replay` trace file to reproduce
        trace: PathBuf,
    },
    /// Reverse-step debugger over a `.replay` trace
    Debug {
        /// The program the trace was recorded against
        file: PathBuf,
        /// The `.replay` trace file to step through
        trace: PathBuf,
    },
    /// Run a program and print each observation with the machine step it fired at
    Steps {
        /// The program to run
        file: PathBuf,
        /// Print the ruler as JSON instead of a table
        #[arg(long)]
        json: bool,
    },
    /// Pause a running program and snapshot it to a `kont` file
    Suspend {
        /// The program to run
        file: PathBuf,
        /// Pause after this many machine steps (0 snapshots before the first step)
        #[arg(long, value_name = "STEP", conflicts_with_all = ["at_call", "at_op"])]
        at: Option<usize>,
        /// Pause on the k-th entry to a definition, e.g. `count` or `count:3`
        #[arg(long = "at-call", value_name = "DEF[:K]")]
        at_call: Option<String>,
        /// Pause before the k-th performance of a capability op, e.g.
        /// `Console.print` or `FileSystem.read_file:2`
        #[arg(long = "at-op", value_name = "OP[:K]")]
        at_op: Option<String>,
        /// Where to write the `kont` snapshot
        #[arg(short, long, value_name = "PATH")]
        out: PathBuf,
    },
    /// Resume a program from a `kont` snapshot, running it to completion
    Resume {
        /// The program the snapshot was captured against
        file: PathBuf,
        /// The `kont` snapshot file to resume
        snapshot: PathBuf,
    },
}

/// Lineage inspection: render a sidecar, explain an output, or verify one.
#[derive(Subcommand, Debug)]
enum LineageCmd {
    /// Explain reuse and recompilation across the durable query graph
    WhyRecompiled {
        /// A `.pr` file or project; omitted uses the enclosing project
        file: Option<PathBuf>,
    },
    /// Render a build or run `.plineage` sidecar
    Show {
        /// The built artifact or its `.plineage` sidecar
        file: PathBuf,
        /// Print the raw JSON sidecar
        #[arg(long)]
        json: bool,
    },
    /// Explain why an output exists by walking a sidecar backward
    Why {
        /// The run or build `.plineage` sidecar
        sidecar: PathBuf,
        /// The output to explain: a path, or the literal `stdout`
        output: String,
        /// Print the explanation as JSON instead of prose
        #[arg(long)]
        json: bool,
    },
    /// Verify a sidecar: rehash the recorded artifacts, or replay to re-check
    Verify {
        /// The build or run `.plineage` sidecar
        sidecar: PathBuf,
        /// Replay the run's sibling trace and compare the trace, stdout, and
        /// input-file digests, verifying by replay rather than trusting the sidecar
        #[arg(long)]
        replay: bool,
        /// On success, write a certificate over the sidecar digest to this path
        /// (`replay-verified` with `--replay`, else `lineage-verified`)
        #[arg(long)]
        certify: Option<PathBuf>,
    },
    /// Check a lineage certificate against the sidecar it names
    CheckCert {
        /// The certificate file minted by `verify --certify`
        cert: PathBuf,
        /// The `.plineage` sidecar the certificate vouches for
        sidecar: PathBuf,
    },
}

/// Package manager and store-publishing verbs.
#[derive(Subcommand, Debug)]
enum PkgCmd {
    /// Create a minimal package, prompting for its package and directory names
    Init,
    /// Add a dependency, pinning its resolved root hash
    Add {
        /// The git reference or content-hash pin to depend on
        target: String,
    },
    /// Sign and log a name -> root pointer at a tag
    Publish {
        /// The project directory, `prism.toml`, or `.pr` file to publish
        file: PathBuf,
        /// The git tag this release is cut at (an opaque label, never a range)
        #[arg(long)]
        tag: String,
        /// The published name (default: the package name, or the file stem)
        #[arg(long)]
        name: Option<String>,
        /// Canonical package identity signed into the index (default: published name)
        #[arg(long)]
        origin: Option<String>,
    },
    /// Re-verify published roots against the store
    Audit {
        /// Accept an unsigned (dev-mode) index instead of failing on it
        #[arg(long)]
        allow_unsigned: bool,
    },
    /// Explain why a hash is in the build closure
    Why {
        /// The dependency name or content hash to explain
        target: String,
    },
    /// Materialize a namespace to a canonical `.pr` file
    Export {
        /// The project directory, `prism.toml`, or `.pr` file to export
        file: PathBuf,
        /// Output directory for the `.pr` projection and its manifest
        #[arg(short, long)]
        out: Option<PathBuf>,
    },
    /// Check a package universe and report digest-addressed inputs
    CheckWorld {
        /// A package project, or a directory containing package projects
        #[arg(default_value = "packages")]
        path: PathBuf,
        /// Print a machine-readable report
        #[arg(long)]
        json: bool,
        /// Exit nonzero when the package universe is internally incompatible
        #[arg(long)]
        strict: bool,
        /// Under `--strict`, also fail when a committed usage summary has drifted
        /// (default: usage is report-only and never fails strict mode)
        #[arg(long)]
        strict_usage: bool,
        /// A prior check-world `--json` report; each package's public-surface
        /// hashes are diffed against it and the moved definitions are named
        #[arg(long)]
        baseline: Option<PathBuf>,
    },
    /// Regenerate the package's usage summary and write `usage-summary.md`
    AcceptUsage {
        /// The package project directory, `prism.toml`, or `.pr` file
        #[arg(default_value = ".")]
        path: PathBuf,
    },
}

/// Content-addressed store verbs: attest, query, reseat wire goldens.
#[derive(Subcommand, Debug)]
enum StoreCmd {
    /// Attest two backends emit identical output
    Attest { file: PathBuf },
    /// Query the definition dependency graph
    Query {
        /// callers | dependents | deps | uses-type
        kind: String,
        /// The definition name to query (a type name for `uses-type`)
        name: String,
        /// Source file to query (the prelude is included)
        file: PathBuf,
    },
    /// Reseat stable-block rung digests
    Wire {
        /// Recompute and rewrite the goldens in place (required; a bare `wire` is a
        /// no-op guard against an accidental rewrite)
        #[arg(long)]
        accept: bool,
        /// The `.pr` file whose `stable` blocks to reseat
        file: PathBuf,
    },
    /// Lock or verify stable-migration behavior
    Lock {
        /// Re-derive and write the committed lock manifest in place (required to
        /// write; a bare `lock` verifies the family against its committed manifest)
        #[arg(long)]
        accept: bool,
        /// The `.pr` file whose locked `stable` families to derive or verify
        file: PathBuf,
    },
}

/// Semantic patches: inspect, judge, stage, and atomically commit.
#[derive(Subcommand, Debug)]
enum PatchCmd {
    /// Fetch an owned definition and its semantic facts by name or digest
    Fetch {
        /// A `.pr` file or project containing the definition
        file: PathBuf,
        /// Definition name, full digest, or `scheme:digest`
        target: String,
    },
    /// Read the transitive importer cone of a definition
    Impact {
        /// A `.pr` file or project to analyze
        file: PathBuf,
        /// Definition name, full digest, or `scheme:digest`
        target: String,
    },
    /// Build a `prism-patch-v1` artifact from one replacement declaration
    Create {
        /// A `.pr` file or project containing the current definition
        file: PathBuf,
        /// Definition name or digest to pin
        target: String,
        /// File containing exactly one replacement declaration, or `-` for stdin
        replacement: PathBuf,
    },
    /// Judge and stage a patch without changing source files
    #[command(visible_alias = "submit")]
    Apply {
        /// A `.pr` file or project the patch targets
        file: PathBuf,
        /// A `prism-patch-v1` JSON file, or `-` for stdin
        patch: PathBuf,
    },
    /// Compare old and replacement observations over an explicit input corpus
    Behavior {
        /// A `.pr` file or project the patch targets
        file: PathBuf,
        /// A `prism-patch-v1` JSON file
        patch: PathBuf,
        /// A `prism-patch-behavior-corpus-v1` JSON file
        corpus: PathBuf,
    },
    /// Re-judge and atomically commit the staged patch
    Commit {
        /// The staged `.pr` file or project
        file: PathBuf,
    },
    /// Discard the staged patch, leaving source files unchanged
    Discard {
        /// The staged `.pr` file or project
        file: PathBuf,
    },
    /// Serve the same verbs as versioned JSON lines over stdio
    Serve {
        /// A `.pr` file or project fixed for this protocol session
        file: PathBuf,
    },
}

// Parse a `--warn-dupes` / `--warn-stdlib-dupes` severity, reporting an invalid
// spelling under the given flag name. Shared by both knobs' CLI overrides.
fn parse_warn_mode(flag: &str, s: &str) -> Option<prism::WarnDupes> {
    let mode = prism::WarnDupes::parse(s);
    if mode.is_none() {
        eprintln!("invalid {flag} `{s}` (expected off, warn, or strict)");
    }
    mode
}

fn main() -> ExitCode {
    let cli = Cli::parse();
    if cli.opt.is_some() && cli.passes.is_some() {
        eprintln!("error: `--passes` and `-O` are mutually exclusive");
        return ExitCode::FAILURE;
    }
    // Resolve the behavior knobs by precedence CLI > env > prism.toml > default:
    // the enclosing project's `[flags]` table seeds the base, the environment
    // overlays it, and the explicit CLI flags below win last. The resolved value
    // threads through every compile call, replacing the old process-global knobs.
    let toml_base = prism::project::flag_overrides(Path::new("."), prism::DynFlags::default());
    let mut cfg = prism::Config::from_flags(prism::DynFlags::from_env_over(&toml_base));
    cfg.session = Some(prism::CompilerSession::new());
    if let Some(s) = &cli.opt {
        let Some(level) = prism::OptLevel::parse(s) else {
            eprintln!("invalid optimization level `-O{s}` (expected 0, 1, or 2)");
            return ExitCode::FAILURE;
        };
        cfg.opt = level;
    }
    if let Some(s) = &cli.passes {
        match prism::PassSpec::parse(s) {
            Ok(spec) => cfg.passes = Some(spec),
            Err(e) => {
                eprintln!("error: invalid pass specification: {e}");
                return ExitCode::FAILURE;
            }
        }
    }
    if let Some(s) = &cli.backend_opt {
        let Some(level) = prism::BackendOpt::parse(s) else {
            eprintln!(
                "invalid backend optimization level `--backend-opt {s}` (expected {})",
                prism::BackendOpt::levels()
            );
            return ExitCode::FAILURE;
        };
        cfg.backend_opt = level;
    }
    if let Some(s) = &cli.scheduler {
        let Some(sched) = prism::Scheduler::parse(s) else {
            eprintln!("invalid scheduler `--scheduler {s}` (expected cooperative, fifo, or lifo)");
            return ExitCode::FAILURE;
        };
        cfg.scheduler = sched;
    }
    cfg.disabled.extend(
        [
            (cli.no_erase_newtypes, prism::CorePass::EraseNewtypes),
            (cli.no_specialize, prism::CorePass::Specialize),
            (cli.no_simplify, prism::CorePass::Simplify),
            (cli.no_inline, prism::CorePass::Inline),
            (cli.no_cse, prism::CorePass::Cse),
            (cli.no_fuse, prism::CorePass::Fuse),
        ]
        .into_iter()
        .filter_map(|(off, pass)| off.then_some(pass)),
    );
    // Behavior toggles: the env baseline (via `from_env`) stands unless a flag
    // overrides it, the same "explicit flag wins" rule as `-O`/`--scheduler`.
    if cli.no_native_effects {
        cfg.flags.native_effects = false;
    }
    if cli.no_trampoline {
        cfg.flags.trampoline = false;
    }
    if cli.fuse {
        cfg.flags.fuse = true;
    }
    if cli.core_lint {
        cfg.flags.core_lint = true;
    }
    if cli.opt_stats {
        cfg.flags.opt_stats = true;
    }
    if cli.compiler_stats {
        cfg.flags.compiler_stats = true;
    }
    if cli.explain_cache {
        cfg.flags.explain_cache = true;
    }
    if let Some(threads) = cli.query_threads {
        if threads == 0 {
            eprintln!("invalid --query-threads 0 (expected a positive integer)");
            return ExitCode::FAILURE;
        }
        cfg.flags.query_threads = threads;
    }
    if cli.time_compile {
        cfg.flags.time_compile = true;
    }
    if cli.verbose {
        cfg.flags.verbose = true;
    }
    if cli.no_compiler_cache {
        cfg.flags.compiler_cache = false;
    }
    if let Some(sink) = cli.dump_core {
        cfg.flags.dump_core = Some(sink.into());
    }
    if let Some(s) = &cli.warn_dupes {
        let Some(mode) = parse_warn_mode("--warn-dupes", s) else {
            return ExitCode::FAILURE;
        };
        cfg.flags.warn_dupes = mode;
    }
    if let Some(s) = &cli.warn_stdlib_dupes {
        let Some(mode) = parse_warn_mode("--warn-stdlib-dupes", s) else {
            return ExitCode::FAILURE;
        };
        cfg.flags.warn_stdlib_dupes = mode;
    }
    // Install the per-phase timing sink for this top-level compile when the flag
    // or `PRISM_TIME_COMPILE` asked for it. The sink lives only on this config, so
    // the compiler's internal re-elaborations (which build their own `from_env`
    // config) stay silent.
    if cfg.flags.time_compile {
        cfg.timing = Some(prism::TimingSink::new());
    }
    let result = match (cli.cmd, cli.file) {
        (Some(cmd), _) => dispatch(cmd, &cfg),
        // Bare `prism <path>` compiles to a native binary (rustc-style: the
        // output is named after the source); with no path, the REPL opens.
        (None, Some(file)) => cli::build_input(&file, cli.out, cli.mlir, &cfg),
        (None, None) => {
            prism::repl::repl(true);
            return ExitCode::SUCCESS;
        }
    };
    if cfg.flags.compiler_stats {
        if let Some(session) = &cfg.session {
            let stats = session.stats();
            eprintln!(
                "compiler queries: {} hit, {} miss, {} write",
                stats.hits, stats.misses, stats.writes
            );
        }
    }
    match result {
        Ok(()) => ExitCode::SUCCESS,
        // A runtime fault prints exactly what the native trap prints (the C
        // runtime's `fatal: <msg>` on stderr, exit 1), so a faulting program is
        // byte-identical across backends; compile-time errors keep the
        // span-annotated diagnostic report.
        Err((Error::RuntimeEvaluation(msg), _, _)) => {
            eprintln!("fatal: {msg}");
            ExitCode::FAILURE
        }
        // Semantic-patch refusals are already canonical JSON. Keep stdout
        // machine-readable and do not wrap them in a human diagnostic.
        Err((Error::SemanticPatch(json), _, _)) => {
            println!("{json}");
            ExitCode::FAILURE
        }
        Err((e, src, name)) => {
            eprint!("{}", e.render(&src, &name));
            ExitCode::FAILURE
        }
    }
}

fn dispatch(cmd: Cmd, cfg: &prism::Config) -> CmdResult {
    match cmd {
        Cmd::Run {
            file,
            examples,
            stdin,
            record,
            lineage,
            durable,
            defer_holes,
            args,
        } => match (file, examples) {
            (Some(_), Some(_)) => Err((
                Error::ResolveCommand(
                    "`prism run` accepts either FILE or `--examples`, not both".into(),
                ),
                String::new(),
                "run".into(),
            )),
            (None, None) => Err((
                Error::ResolveCommand("`prism run` requires FILE or `--examples`".into()),
                String::new(),
                "run".into(),
            )),
            (None, Some(dir)) => {
                if defer_holes {
                    return Err((
                        Error::ResolveCommand(
                            "`--defer-holes` requires a single FILE, not `--examples`".into(),
                        ),
                        String::new(),
                        dir.display().to_string(),
                    ));
                }
                if record.is_some() {
                    return Err((
                        Error::ResolveCommand(
                            "`--record` cannot be combined with `--examples`".into(),
                        ),
                        String::new(),
                        dir.display().to_string(),
                    ));
                }
                if durable.is_some() {
                    return Err((
                        Error::ResolveCommand(
                            "`--durable` cannot be combined with `--examples`".into(),
                        ),
                        String::new(),
                        dir.display().to_string(),
                    ));
                }
                if !args.is_empty() {
                    return Err((
                        Error::ResolveCommand(
                            "program arguments cannot be combined with `--examples`".into(),
                        ),
                        String::new(),
                        dir.display().to_string(),
                    ));
                }
                cli::run::run_examples_cmd(&dir, cfg, stdin)
            }
            (Some(file), None) => {
                let exit = cli::run::run_file_cmd(
                    &file,
                    record.as_deref(),
                    lineage.as_deref(),
                    durable.as_deref(),
                    args,
                    cfg,
                    defer_holes,
                )?;
                if let Some(code) = exit {
                    process::exit(code);
                }
                Ok(())
            }
        },
        Cmd::Exec(exec) => dispatch_exec(exec, cfg),
        Cmd::Lineage(lineage) => dispatch_lineage(lineage, cfg),
        Cmd::WhyOutput {
            artifact,
            output,
            json,
        } => cli::lineage::why_output_top_cmd(&artifact, output.as_deref(), json),
        Cmd::Pkg(pkg) => dispatch_pkg(pkg, cfg),
        Cmd::Store(store) => dispatch_store(store, cfg),
        Cmd::Patch(patch) => dispatch_patch(patch, cfg),
        Cmd::Build { path, out, mlir } => {
            // `build` is the project verb: locate the nearest enclosing
            // `prism.toml` and compile it. A single file compiles via
            // `prism <file.pr>`. Canonicalize first so the default `.` has real
            // parent components to walk up through.
            let start = path.canonicalize().unwrap_or(path);
            let manifest = prism::project::find_manifest(&start).ok_or_else(|| {
                (
                    Error::ResolveCommand(
                        "no prism.toml found: `prism build` compiles a project; \
                         compile a single file with `prism <file.pr>`"
                            .into(),
                    ),
                    String::new(),
                    start.display().to_string(),
                )
            })?;
            cli::build_input(&manifest, out, mlir, cfg)
        }
        Cmd::Clean { path } => cli::clean_cmd(&path),
        Cmd::Check { file } => cli::check_cmd(file.as_deref(), cfg),
        Cmd::Test {
            file,
            filter,
            exact,
            list,
            no_run,
            format,
            show_output,
            fail_if_no_tests,
        } => cli::test::test_cmd(
            file.as_deref(),
            &cli::test::TestOptions {
                filter,
                exact,
                list,
                no_run,
                json: format == "json",
                show_output,
                fail_if_no_tests,
            },
            cfg,
        ),
        Cmd::Verify {
            file,
            solver,
            solvers,
            require_agreement,
        } => cli::verify_cmd(&file, &solver, &solvers, require_agreement, cfg),
        Cmd::Dump { phase, file } => cli::dump_cmd(&phase, &file, cfg),
        Cmd::Diff { old, new, json } => {
            cli::lineage::diff_cmd(old.as_deref(), new.as_deref(), json, cfg)
        }
        Cmd::Report { file } => cli::report_cmd(&file, cfg),
        Cmd::Repl { no_banner } => {
            prism::repl::repl(!no_banner);
            Ok(())
        }
        Cmd::Fmt { files, check } => cli::fmt::fmt_cmd(&files, check),
        Cmd::Docs {
            path,
            out,
            stdlib,
            test,
            accept,
            check,
            verify_manifest,
            open,
        } => cli::docs::docs_cmd(
            &path,
            out,
            stdlib,
            test,
            accept,
            check,
            verify_manifest,
            open,
            cfg,
        ),
        Cmd::Mdbook { rest } => cli::docs::mdbook_cmd(&rest, cfg.flags.mdbook_strict),
    }
}

// The execution-control family: reproduce, step, pause, and resume runs.
fn dispatch_exec(exec: ExecCmd, cfg: &prism::Config) -> CmdResult {
    match exec {
        ExecCmd::Replay { file, trace } => cli::exec::replay(&file, &trace, cfg),
        ExecCmd::Debug { file, trace } => cli::exec::debug(&file, &trace, cfg),
        ExecCmd::Steps { file, json } => cli::exec::steps(&file, json, cfg),
        ExecCmd::Suspend {
            file,
            at,
            at_call,
            at_op,
            out,
        } => cli::exec::suspend(&file, at, at_call.as_deref(), at_op.as_deref(), &out, cfg),
        ExecCmd::Resume { file, snapshot } => cli::exec::resume(&file, &snapshot, cfg),
    }
}

// Lineage inspection: render a sidecar, explain an output, or verify one.
fn dispatch_lineage(lineage: LineageCmd, cfg: &prism::Config) -> CmdResult {
    match lineage {
        LineageCmd::WhyRecompiled { file } => {
            cli::lineage::why_recompiled_cmd(file.as_deref(), cfg)
        }
        LineageCmd::Show { file, json } => cli::lineage::lineage_cmd(&file, json),
        LineageCmd::Why {
            sidecar,
            output,
            json,
        } => cli::lineage::why_output_cmd(&sidecar, &output, json),
        // Without `--replay` the recorded artifacts are rehashed (the old
        // build-sidecar verify); with it the run is replayed and re-checked. Either
        // form can mint a certificate over the sidecar digest on success.
        LineageCmd::Verify {
            sidecar,
            replay,
            certify,
        } => {
            if replay {
                cli::lineage::verify_lineage_cmd(&sidecar, certify.as_deref(), cfg)
            } else {
                cli::lineage::verify_rehash_cmd(&sidecar, certify.as_deref())
            }
        }
        LineageCmd::CheckCert { cert, sidecar } => cli::lineage::check_cert_cmd(&cert, &sidecar),
    }
}

// Package manager and store-publishing verbs.
fn dispatch_pkg(pkg: PkgCmd, cfg: &prism::Config) -> CmdResult {
    match pkg {
        PkgCmd::Init => cli::pkg::init(),
        PkgCmd::Add { target } => cli::pkg::add(&target, cfg),
        PkgCmd::Why { target } => cli::pkg::why(&target, cfg),
        PkgCmd::Export { file, out } => cli::pkg::export(&file, out, cfg),
        PkgCmd::Publish {
            file,
            tag,
            name,
            origin,
        } => cli::pkg::publish(&file, &tag, name, origin, cfg),
        PkgCmd::Audit { allow_unsigned } => cli::pkg::audit(cfg, allow_unsigned),
        PkgCmd::CheckWorld {
            path,
            json,
            strict,
            strict_usage,
            baseline,
        } => cli::check_world::check_world_cmd(
            &path,
            json,
            strict,
            strict_usage,
            baseline.as_deref(),
            cfg,
        ),
        PkgCmd::AcceptUsage { path } => cli::pkg::accept_usage(&path, cfg),
    }
}

// Content-addressed store verbs: attest, query, reseat wire goldens.
fn dispatch_store(store: StoreCmd, cfg: &prism::Config) -> CmdResult {
    match store {
        StoreCmd::Attest { file } => cli::store::attest(&file, cfg),
        StoreCmd::Query { kind, name, file } => cli::store::query(&kind, &name, &file, cfg),
        StoreCmd::Wire { accept, file } => cli::store::wire(accept, &file),
        StoreCmd::Lock { accept, file } => cli::store::lock(accept, &file, cfg),
    }
}

fn dispatch_patch(patch: PatchCmd, cfg: &prism::Config) -> CmdResult {
    match patch {
        PatchCmd::Fetch { file, target } => cli::patch::fetch(&file, &target, cfg),
        PatchCmd::Impact { file, target } => cli::patch::impact(&file, &target, cfg),
        PatchCmd::Create {
            file,
            target,
            replacement,
        } => cli::patch::create(&file, &target, &replacement, cfg),
        PatchCmd::Apply { file, patch } => cli::patch::apply(&file, &patch, cfg),
        PatchCmd::Behavior {
            file,
            patch,
            corpus,
        } => cli::patch::behavior(&file, &patch, &corpus, cfg),
        PatchCmd::Commit { file } => cli::patch::commit(&file, cfg),
        PatchCmd::Discard { file } => cli::patch::discard(&file, cfg),
        PatchCmd::Serve { file } => cli::patch::serve(&file, cfg),
    }
}
