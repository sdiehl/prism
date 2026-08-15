// Determinism harness.
//
// `Sym` interns into a process-global table with a process-global fresh-id
// counter (`src/sym.rs`). A program compiled after an unrelated one therefore
// sees a shifted fresh-id supply and, for shared spellings, a different
// first-seen intern order. The compiler's CANONICAL output (content hashes)
// must not depend on any of that: it is what content addressing, replay, and
// the equivalence gate rest on. These tests pin that invariant: canonical output
// must remain independent of prior-compilation and scheduling history even if
// symbol ownership changes.
//
// Note: raw human dumps (`dump core`) print fresh ids like `t@733` verbatim and
// are deliberately NOT asserted here; only the alpha-invariant `core-hash` and
// the stdlib hash are canonical.

const P: &str = "\
fn compose(f : (b) -> c, g : (a) -> b, x : a) : c = f(g(x))
fn inc(n : Int) : Int = n + 1
fn dbl(n : Int) : Int = n + n
fn main() : Int = compose(inc, dbl, 20)
";

const UNRELATED: &str = "\
type Tree(a) = Leaf | Node(Tree(a), a, Tree(a))
fn sz(t : Tree(a)) : Int =
  match t of
    Leaf => 0
    Node(l, _, r) => sz(l) + 1 + sz(r)
fn main() : Int = sz(Node(Leaf, 7, Node(Leaf, 8, Leaf)))
";

fn core_hash(src: &str) -> String {
    prism::dump("core-hash", src).expect("program compiles")
}

// Compiling an unrelated program in between (which advances the global fresh-id
// counter and interns new spellings) must not change P's canonical core hash.
#[test]
fn core_hash_is_independent_of_prior_compilations() {
    let first = core_hash(P);
    // Advance the process-global interner and fresh counter with other work.
    let _ = core_hash(UNRELATED);
    let _ = core_hash(UNRELATED);
    let again = core_hash(P);
    assert_eq!(
        first, again,
        "core hash depends on prior-compilation intern/fresh history"
    );
}

// Interleaving the two programs must not change either one's hash: a warm
// process compiling many projects reaches the same canonical result as a cold
// one compiling a single project.
#[test]
fn core_hash_is_independent_of_interleaving() {
    let solo = core_hash(P);
    let _ = core_hash(UNRELATED);
    let _ = core_hash(P);
    let _ = core_hash(UNRELATED);
    let interleaved = core_hash(P);
    assert_eq!(solo, interleaved, "core hash depends on interleaving order");
}

// The stdlib hash is a pure function of the compiler and stdlib source, never of
// what else the process has compiled.
#[test]
fn stdlib_hash_is_independent_of_prior_compilations() {
    let first = prism::stdlib_hash().expect("stdlib compiles").root;
    let _ = core_hash(UNRELATED);
    let _ = core_hash(P);
    let again = prism::stdlib_hash().expect("stdlib compiles").root;
    assert_eq!(first, again, "stdlib root depends on prior compilations");
}

// Independent compilations on many threads (each self-contained on its own
// thread) that also churn the shared interner yield one hash. NOTE: this covers
// only CROSS-compilation parallelism. INTRA-compilation parallelism (one
// compilation spread across `query_threads` workers, where a `Sym` crosses
// worker threads) is exercised by `tests/native/compiler_cache.rs`
// (`query_threads=1` vs `=N`, byte-diffed). Symbol-universe changes must preserve
// BOTH invariants: a thread-local universe passes this test but fails that one.
#[test]
fn core_hash_is_independent_of_parallel_scheduling() {
    let expected = core_hash(P);
    let handles: Vec<_> = (0..8)
        .map(|i| {
            std::thread::spawn(move || {
                // Half the threads churn the interner first, to vary the order in
                // which the shared global table sees P's spellings.
                if i % 2 == 0 {
                    let _ = core_hash(UNRELATED);
                }
                core_hash(P)
            })
        })
        .collect();
    for h in handles {
        assert_eq!(
            h.join().expect("thread"),
            expected,
            "core hash depends on parallel scheduling"
        );
    }
}
