// One tooling consumer of the public Prism source representation, gated end to
// end.
//
// `Syntax.Query` is a Prism module that reads a decoded `prism-syntax-tokens-v1`
// artifact and reports a stable inventory of the source: its content digest,
// ordered imports, comment spans, ordered top-level declaration heads, and a
// token-kind histogram. It is a *source-identity* view, and this gate pins the
// one property that makes such a tool honest under Prism's determinism contract:
// source identity and Core identity are distinct axes.
//
//   - A comment-only or formatting-only edit moves the source view (digest and
//     comment spans change) but leaves Core identity untouched: the whole-program
//     namespace root and every per-definition hash are byte-identical.
//   - A semantic edit moves Core identity, and only within the dependent closure:
//     the edited definition and its callers change hash; an independent
//     definition keeps its hash.
//   - The consumer is a pure function of the artifact bytes. It reads only the
//     explicit artifact path, never ambient workspace state, so the same bytes
//     from two different locations yield the identical report.
//
// The compiler stays authoritative: the artifact is produced by the compiler's
// own `dump syntax-tokens`, and the Prism consumer is compared and reported,
// never substituted for a compiler stage.

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

use prism::{default_roots, dump, interpret_io_on_with_args, namespace_root, with_prelude, Config};

const FIXTURE_DIR: &str = "tests/fixtures/syntax";
const HARNESS: &str = "consumers/query_report.pr";
// The private content-addressed store the cache-independence gate primes.
const WARM_STORE_PREFIX: &str = "prism_source_identity_store_";

// The base program: two independent definitions and a `main` that calls both.
const BASE: &str = "\
-- base program
fn double(x : Int) : Int = x * 2
fn triple(x : Int) : Int = x * 3
fn main() : Int = double(10) + triple(10)
";

// Same program, differing only in an added comment and reflowed whitespace: the
// same Core, a different source surface.
const COMMENT: &str = "\
-- base program
-- an extra explanatory comment
fn double(x : Int) : Int = x * 2
fn triple(x : Int) : Int =   x * 3
fn main() : Int = double(10) + triple(10)
";

// One semantic edit: `triple`'s body 3 -> 4. `double` is untouched and
// independent of `triple`; `main` calls `triple`.
const SEM: &str = "\
-- base program
fn double(x : Int) : Int = x * 2
fn triple(x : Int) : Int = x * 4
fn main() : Int = double(10) + triple(10)
";

fn fixture_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(FIXTURE_DIR)
}

fn roots() -> Vec<prism::Root> {
    default_roots(Path::new(env!("CARGO_MANIFEST_DIR")))
}

// The whole-program namespace root: a Merkle fold over every definition's Core
// hash, blind to comments and formatting by construction.
fn root_of(src: &str) -> String {
    namespace_root(src, &roots()).expect("namespace root")
}

// Per-definition Core hashes, keyed by (qualified) name. Prelude definitions are
// qualified (`Data.Char.is_alnum`); the program's own definitions are bare
// (`double`, `triple`, `main`).
fn core_hashes(src: &str) -> BTreeMap<String, String> {
    dump("core-hash", src)
        .expect("core-hash dump")
        .lines()
        .filter_map(|l| {
            let (h, n) = l.split_once("  ")?;
            Some((n.to_string(), h.to_string()))
        })
        .collect()
}

// Produce the compiler's syntax-tokens artifact for a source, then run the Prism
// query consumer over it from an explicit temp path and capture its report. The
// `label` only names the temp file; the report must not depend on it.
fn query_report(src: &str, label: &str) -> String {
    query_report_on(src, label, &Config::from_env())
}

// As above, under an explicit configuration, so a caller can vary compiler cache
// state without disturbing the ambient one.
fn query_report_on(src: &str, label: &str, cfg: &Config) -> String {
    let artifact = dump("syntax-tokens", src).expect("syntax-tokens dump");
    let tmp =
        std::env::temp_dir().join(format!("prism_source_identity_{label}.syntax-tokens.json"));
    fs::write(&tmp, &artifact).expect("write artifact");

    let harness = fs::read_to_string(fixture_dir().join(HARNESS)).expect("harness source");
    let full = with_prelude(&harness);
    let args = vec![tmp.display().to_string()];
    let mut sink = Vec::new();
    interpret_io_on_with_args(&full, &roots(), &mut sink, &mut &b""[..], cfg, args)
        .unwrap_or_else(|e| panic!("query harness run: {e}"));
    String::from_utf8(sink)
        .expect("utf8 report")
        .trim()
        .to_string()
}

// The compiler cache off, and on against a fresh private store: a first run
// through the warm configuration primes that store and a second is served from
// it, without ever reading or writing the developer's real cache.
fn cache_configs() -> (Config, Config, PathBuf) {
    let store = std::env::temp_dir().join(format!("{WARM_STORE_PREFIX}{}", std::process::id()));
    let _ = fs::remove_dir_all(&store);
    let mut cold = Config::from_env();
    cold.flags.compiler_cache = false;
    let mut warm = Config::from_env();
    warm.flags.compiler_cache = true;
    warm.flags.store_path = Some(store.clone());
    (cold, warm, store)
}

fn store_entries(dir: &Path) -> usize {
    let Ok(entries) = fs::read_dir(dir) else {
        return 0;
    };
    entries
        .filter_map(Result::ok)
        .map(|e| {
            if e.path().is_dir() {
                store_entries(&e.path())
            } else {
                1
            }
        })
        .sum()
}

fn report_lines<'a>(report: &'a str, prefix: &str) -> Vec<&'a str> {
    report.lines().filter(|l| l.starts_with(prefix)).collect()
}

// The `decl` lines with their trailing byte offset dropped: the keyword+name
// structure of the declaration inventory, independent of where in the source it
// sits.
fn decl_heads(report: &str) -> Vec<String> {
    report_lines(report, "decl ")
        .iter()
        .map(|l| {
            l.rsplit_once(' ')
                .map_or_else(|| (*l).to_string(), |(head, _)| head.to_string())
        })
        .collect()
}

// The consumer's report is a function of the artifact bytes, not of compiler
// cache state. The seams themselves only lex and parse and never reach the
// content-addressed store, but the consumer runs the checker over the harness
// and does, so this is where cold-versus-warm can be observed at all. The store
// is asserted non-empty afterwards: a cache that silently never engaged would
// otherwise make the equality vacuous.
#[test]
fn consumer_report_is_identical_cold_and_warm() {
    let (cold, warm, store) = cache_configs();

    let uncached = query_report_on(BASE, "cache_cold", &cold);
    let primed = query_report_on(BASE, "cache_prime", &warm);
    let served = query_report_on(BASE, "cache_warm", &warm);

    assert!(
        store_entries(&store) > 0,
        "the warm run never populated {}; the comparison would be vacuous",
        store.display()
    );
    assert_eq!(
        uncached, primed,
        "the consumer's report moved when the compiler cache was enabled"
    );
    assert_eq!(
        uncached, served,
        "the consumer's report moved when served from a warm compiler cache"
    );

    let _ = fs::remove_dir_all(&store);
}

// A comment-only / formatting-only edit is invisible to Core: the namespace root
// and every per-definition hash are byte-identical.
#[test]
fn core_identity_blind_to_comments_and_formatting() {
    assert_eq!(
        root_of(BASE),
        root_of(COMMENT),
        "a comment/formatting-only edit moved the namespace root"
    );
    assert_eq!(
        dump("core-hash", BASE).unwrap(),
        dump("core-hash", COMMENT).unwrap(),
        "a comment/formatting-only edit moved a per-definition Core hash"
    );
}

// A semantic edit moves Core identity, and only within the dependent closure of
// the edit: the edited definition and its caller change; an independent
// definition is preserved.
#[test]
fn semantic_edit_moves_bounded_closure() {
    assert_ne!(
        root_of(BASE),
        root_of(SEM),
        "a semantic edit left the namespace root unchanged"
    );

    let base = core_hashes(BASE);
    let sem = core_hashes(SEM);

    assert_eq!(
        base["double"], sem["double"],
        "an independent definition changed hash under an unrelated edit"
    );
    assert_ne!(
        base["triple"], sem["triple"],
        "the edited definition did not change hash"
    );
    assert_ne!(
        base["main"], sem["main"],
        "the caller of the edited definition did not change hash"
    );
}

// The duality: for the very same pair of programs, Core identity holds while the
// consumer's source view moves. The comment variant has a different content
// digest and one more comment span than the base.
#[test]
fn source_identity_moves_while_core_holds() {
    // Core identity holds (restated here so the duality lives in one test).
    assert_eq!(root_of(BASE), root_of(COMMENT));

    let base = query_report(BASE, "dual_base");
    let comment = query_report(COMMENT, "dual_comment");

    assert_ne!(
        base, comment,
        "the source view did not move under a comment edit"
    );

    let base_digest = report_lines(&base, "digest ");
    let comment_digest = report_lines(&comment, "digest ");
    assert_ne!(
        base_digest, comment_digest,
        "the content digest did not move under a comment edit"
    );

    let base_comments = report_lines(&base, "comment ").len();
    let comment_comments = report_lines(&comment, "comment ").len();
    assert!(
        comment_comments > base_comments,
        "the added comment did not appear in the source view: base={base_comments} comment={comment_comments}"
    );

    // The declaration structure is preserved: the same keyword+name heads in the
    // same order. Their byte offsets, however, shift with the added comment,
    // which is precisely the source-position signal a source-identity view must
    // carry.
    assert_eq!(
        decl_heads(&base),
        decl_heads(&comment),
        "a comment/formatting edit changed the declaration keyword+name structure"
    );
    assert_ne!(
        report_lines(&base, "decl "),
        report_lines(&comment, "decl "),
        "the declaration byte offsets did not shift under an added comment"
    );
}

// The consumer is a pure function of the artifact bytes: the same artifact read
// from two different temp paths yields the identical report, so it consults no
// ambient state.
#[test]
fn consumer_is_pure_function_of_artifact_bytes() {
    let a = query_report(BASE, "pure_a");
    let b = query_report(BASE, "pure_b");
    assert_eq!(
        a, b,
        "the query report depended on something other than the artifact bytes"
    );
    assert!(a.starts_with("digest "), "unexpected report shape: {a}");
}
