// The Prism-side least fixpoint (`Data.Fixpoint`) and its worked consumer over
// resolved syntax (`Syntax.Flow`).
//
// The standard library's worklist and the compiler's own round-based
// `least_fixpoint` are two implementations of one specification, so the gate is
// agreement rather than a comment claiming it: both solve the same relation and
// their answers are compared byte for byte, once on a fixture graph with a
// self-loop, a mutual-recursion cycle, and a chain, and once on the call graph
// of a real `prism-resolved-syntax-v1` document that each side extracts for
// itself. The remaining gates are the ones a fixpoint has to earn: the
// semilattice laws hold on every instance, the answer does not depend on the
// order the relation was built in, and a transfer function that ascends forever
// exhausts the budget and fails instead of spinning.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};

use prism::{default_roots, dump_at, interpret, interpret_io_on_with_args, with_prelude, Config};
use prism_common::fixpoint::least_fixpoint;
use serde_json::Value;

// A relation as literal data: each node with its successors, in the order the
// fixture spells them rather than a canonical one.
type Rel = &'static [(&'static str, &'static [&'static str])];

// A self-loop, a mutual-recursion cycle, a chain, and a node with two
// successors: the shapes an iteration order or a cap would get wrong.
const CALLS: Rel = &[
    ("a", &["b"]),
    ("b", &["c"]),
    ("c", &[]),
    ("e", &["c", "b"]),
    ("f", &["f"]),
    ("g", &["h"]),
    ("h", &["g"]),
];

// The same relation, entries and successor lists reversed. Nothing about the
// solution may depend on the difference.
const CALLS_SHUFFLED: Rel = &[
    ("h", &["g"]),
    ("g", &["h"]),
    ("f", &["f"]),
    ("e", &["b", "c"]),
    ("c", &[]),
    ("b", &["c"]),
    ("a", &["b"]),
];

// What each node contributes on its own, before anything propagates.
const OWN: Rel = &[("c", &["D"]), ("f", &["A"]), ("g", &["B"]), ("h", &["C"])];

// The document the worked consumer runs over: mutual recursion, a shared leaf,
// and a component no entry point reaches.
const FLOW_SOURCE: &str = r"fn main() = println(show(flow_entry(3)))

fn flow_entry(n : Int) : Int = flow_even(n) + flow_shared(n)

fn flow_even(n : Int) : Int = if n <= 0 then 0 else flow_odd(n - 1)

fn flow_odd(n : Int) : Int = if n <= 0 then 1 else flow_even(n - 1) + flow_shared(n)

fn flow_shared(n : Int) : Int = n * 2

fn flow_orphan(n : Int) : Int = flow_shared(n) + flow_lonely(n)

fn flow_lonely(n : Int) : Int = n + 1
";

// Decode the document, then print the call graph, the transitive reach, the
// live set from `main`, the dead set, and the recursive functions: one line per
// answer, each a tag then ascending names.
const FLOW_HARNESS: &str = r#"import Data.List (map)

import Data.Map (map_to_list)

import Data.Set (set_to_list)

import Syntax.Codec (..)

import Syntax.Flow (..)

import Syntax.Resolved (..)

fn main() =
  match decode_resolved(read_file(arg(0))) of
    Err(e) => println("decode error: {codec_error_message(e)}")
    Ok(d) => default(\() -> print_flow(d), ())

fn print_rows(tag : String, rows : List((String, List(String)))) : Unit ! {IO} =
  match rows of
    Nil => ()
    Cons(p, rest) =>
      println(str_join(" ", Cons(tag, Cons(fst(p), snd(p)))))
      print_rows(tag, rest)

fn print_flow(d : ResolvedDoc) =
  print_rows("calls", map_to_list(fl_calls(d)))
  print_rows(
      "reaches",
      map(\(p) -> (fst(p), set_to_list(snd(p))), map_to_list(fl_transitive(d))),
    )
  println(str_join(" ", Cons("live", set_to_list(fl_live(d, ["main"])))))
  println(str_join(" ", Cons("dead", fl_dead(d, ["main"]))))
  println(str_join(" ", Cons("recursive", fl_recursive(d))))
"#;

const ARTIFACT: &str = "resolved-syntax";
// The tag the harness prints the transitive reach under.
const REACHES: &str = "reaches";

fn manifest() -> &'static Path {
    Path::new(env!("CARGO_MANIFEST_DIR"))
}

// Run a Prism program under the prelude, joining its printed values.
fn out(src: &str) -> String {
    let run = interpret(&with_prelude(src)).expect("resolves and runs");
    run.out.iter().fold(String::new(), |mut s, v| {
        s.push_str(&v.show());
        s.push('\n');
        s
    })
}

fn to_map(rel: Rel) -> BTreeMap<String, Vec<String>> {
    rel.iter()
        .map(|(k, vs)| {
            (
                (*k).to_string(),
                vs.iter().map(|v| (*v).to_string()).collect(),
            )
        })
        .collect()
}

// The compiler's own substrate on the same problem: seed every node with its own
// contribution, then close under the relation. `least_fixpoint` unions rather
// than replaces, so this is the least solution above the seed.
fn rust_solution(own: Rel, calls: Rel) -> BTreeMap<String, BTreeSet<String>> {
    let own = to_map(own);
    let calls = to_map(calls);
    let mut nodes: BTreeSet<String> = own.keys().cloned().collect();
    for (k, vs) in &calls {
        nodes.insert(k.clone());
        nodes.extend(vs.iter().cloned());
    }
    let seed: BTreeMap<String, BTreeSet<String>> = nodes
        .iter()
        .map(|k| {
            let base: BTreeSet<String> = own.get(k).into_iter().flatten().cloned().collect();
            (k.clone(), base)
        })
        .collect();
    least_fixpoint(seed, |k, cur| {
        let mut s: BTreeSet<String> = own.get(k).into_iter().flatten().cloned().collect();
        for j in calls.get(k).into_iter().flatten() {
            s.extend(cur.get(j).into_iter().flatten().cloned());
        }
        s
    })
}

// One line per node: the node, then its members, all ascending and space
// separated. The shape both sides print, so the comparison is on the answer and
// not on a formatting convention.
fn render(sol: &BTreeMap<String, BTreeSet<String>>, tag: &str) -> String {
    sol.iter().fold(String::new(), |mut s, (k, vs)| {
        let _ = write!(s, "{tag}{k}");
        for v in vs {
            let _ = write!(s, " {v}");
        }
        s.push('\n');
        s
    })
}

fn prism_list(vs: &[&str]) -> String {
    let items: Vec<String> = vs.iter().map(|v| format!("\"{v}\"")).collect();
    format!("[{}]", items.join(", "))
}

fn prism_sets(rel: Rel) -> String {
    let items: Vec<String> = rel
        .iter()
        .map(|(k, vs)| format!("(\"{k}\", set_from_list({}))", prism_list(vs)))
        .collect();
    items.join(", ")
}

fn prism_lists(rel: Rel) -> String {
    let items: Vec<String> = rel
        .iter()
        .map(|(k, vs)| format!("(\"{k}\", {})", prism_list(vs)))
        .collect();
    items.join(", ")
}

// The same solve, spelled in Prism: `fix_propagate` over the standard library's
// worklist, printed in the shared line format.
fn prism_solution(own: Rel, calls: Rel) -> String {
    let src = format!(
        r#"import Data.Fixpoint (..)

fn own() = map_from_list([{own}])

fn calls() = map_from_list([{calls}])

fn print_rows(rows) =
  match rows of
    Nil => ()
    Cons(p, rest) =>
      println(str_join(" ", Cons(fst(p), set_to_list(snd(p)))))
      print_rows(rest)

fn main() =
  default(\() -> print_rows(map_to_list(fix_propagate(own(), calls()))), ())
"#,
        own = prism_sets(own),
        calls = prism_lists(calls),
    );
    out(&src)
}

// The two implementations agree on the fixture the compiler's own fixpoint is
// tested with: a self-loop contributes only its own value, the two nodes of a
// cycle end up with one shared answer, and the chain carries its tail's value
// all the way up.
#[test]
fn fixpoint_agrees_with_the_compilers_own_least_fixpoint() {
    let expected = render(&rust_solution(OWN, CALLS), "");
    assert_eq!(
        prism_solution(OWN, CALLS),
        expected,
        "the standard library worklist and the compiler's own fixpoint disagree"
    );
}

// The relation is a set of edges, not a list of them: permuting the entries and
// the successor lists changes neither the answer nor the order it prints in.
#[test]
fn fixpoint_solution_is_independent_of_input_order() {
    assert_eq!(
        prism_solution(OWN, CALLS_SHUFFLED),
        prism_solution(OWN, CALLS),
        "the solution depends on the order the relation was built in"
    );
}

// The laws the class doc states, checked over every triple of a small sample at
// each instance, up to the equivalence the order induces.
#[test]
fn semilattice_laws_hold_on_every_instance() {
    let src = r#"import Data.Fixpoint (..)

fn holds(x : a, y : a, z : a) : Bool given Semilattice(a) =
  lat_equiv(lat_join(x, lat_join(y, z)), lat_join(lat_join(x, y), z))
    && lat_equiv(lat_join(x, y), lat_join(y, x))
    && lat_equiv(lat_join(x, x), x)
    && lat_equiv(lat_join(lat_bottom(), x), x)
    && (lat_leq(x, y) == lat_equiv(lat_join(x, y), y))

fn laws(xs : List(a)) : Bool given Semilattice(a) =
  all(\(x) -> all(\(y) -> all(\(z) -> holds(x, y, z), xs), xs), xs)

fn sets() =
  [map_empty, set_from_list([1]), set_from_list([2]), set_from_list([1, 2])]

fn nested() =
  [
      map_empty,
      map_from_list([("a", set_from_list([1]))]),
      map_from_list([("a", set_from_list([2])), ("b", map_empty)]),
    ]

fn main() =
  println("unit {show(laws([()]))}")
  println("bool {show(laws([false, true]))}")
  println("option {show(laws([None, Some(false), Some(true)]))}")
  println("pair {show(laws([(false, false), (false, true), (true, true)]))}")
  println("map {show(laws(sets()))}")
  println("nested {show(laws(nested()))}")
"#;
    assert_eq!(
        out(src),
        "unit true\nbool true\noption true\npair true\nmap true\nnested true\n"
    );
}

// A transfer function that invents a fresh key on every visit has no fixed
// point, so the budget is what stands between the solver and an unbounded
// ascending chain. It fails rather than returning the assignment it had reached.
#[test]
fn fixpoint_budget_refuses_an_unbounded_transfer() {
    let src = r#"import Data.Fixpoint (..)

fn grow(key : String, cur : Map(String, Map(Int, Unit))) : Map(Int, Unit) =
  map_insert(map_size(fix_at(cur, key)), (), fix_at(cur, key))

fn main() =
  let seed = map_from_list([("x", map_empty)])
  let uses = map_from_list([("x", ["x"])])
  println(show(optional(\() -> map_size(fix_at(fix_least(seed, uses, grow), "x")))))
"#;
    assert_eq!(out(src), "None\n");
}

// The resolved-syntax artifact for the flow document, written where the harness
// can read it.
fn flow_artifact() -> PathBuf {
    let json = dump_at(ARTIFACT, &with_prelude(FLOW_SOURCE), manifest())
        .expect("resolved-syntax dump of the flow document");
    let path = std::env::temp_dir().join(format!("prism_flow.{ARTIFACT}.json"));
    fs::write(&path, &json).expect("write the flow artifact");
    path
}

// Run the harness over one artifact, capturing stdout.
fn flow_harness(artifact: &Path) -> String {
    let mut sink = Vec::new();
    interpret_io_on_with_args(
        &with_prelude(FLOW_HARNESS),
        &default_roots(manifest()),
        &mut sink,
        &mut &b""[..],
        &Config::from_env(),
        vec![artifact.display().to_string()],
    )
    .expect("flow harness run");
    String::from_utf8(sink).expect("utf8 harness output")
}

// The pinned answer over a real resolved tree: the call graph as the document
// spells it, the transitive reach (where the two mutually recursive functions
// share one answer and each lists itself), the functions `main` reaches, the
// ones it does not, and the recursive ones.
#[test]
fn flow_pins_the_analysis_of_a_resolved_document() {
    assert_eq!(
        flow_harness(&flow_artifact()),
        "calls flow_entry flow_even flow_shared\n\
         calls flow_even flow_odd\n\
         calls flow_lonely\n\
         calls flow_odd flow_even flow_shared\n\
         calls flow_orphan flow_lonely flow_shared\n\
         calls flow_shared\n\
         calls main flow_entry\n\
         reaches flow_entry flow_even flow_odd flow_shared\n\
         reaches flow_even flow_even flow_odd flow_shared\n\
         reaches flow_lonely\n\
         reaches flow_odd flow_even flow_odd flow_shared\n\
         reaches flow_orphan flow_lonely flow_shared\n\
         reaches flow_shared\n\
         reaches main flow_entry flow_even flow_odd flow_shared\n\
         live flow_entry flow_even flow_odd flow_shared main\n\
         dead flow_lonely flow_orphan\n\
         recursive flow_even flow_odd\n"
    );
}

// Every `var` node of a function body, sliced out of the embedded source: the
// same references the Prism side reads, recovered here without its help.
fn var_names(node: &Value, text: &str, out: &mut Vec<String>) {
    if node["kind"] == "var" {
        let span = node["span"].as_array().expect("span pair");
        let lo = usize::try_from(span[0].as_u64().expect("span start")).expect("span start fits");
        let hi = usize::try_from(span[1].as_u64().expect("span end")).expect("span end fits");
        out.push(text[lo..hi].to_string());
    }
    for c in node["children"].as_array().into_iter().flatten() {
        var_names(c, text, out);
    }
}

// The document's call graph, extracted from the artifact JSON: an edge to every
// function of the document a body references.
fn document_calls(doc: &Value) -> BTreeMap<String, BTreeSet<String>> {
    let text = doc["source"]["text"].as_str().expect("embedded source");
    let fns = doc["functions"].as_array().expect("functions");
    let defined: BTreeSet<String> = fns
        .iter()
        .map(|f| f["name"].as_str().expect("function name").to_string())
        .collect();
    fns.iter()
        .map(|f| {
            let mut names = Vec::new();
            var_names(&f["body"], text, &mut names);
            let callees = names.into_iter().filter(|n| defined.contains(n)).collect();
            (
                f["name"].as_str().expect("function name").to_string(),
                callees,
            )
        })
        .collect()
}

// The cross-implementation gate on a real program: the same document, walked
// and solved independently on each side, must yield the same transitive reach.
// The Rust side reads the artifact JSON and runs the compiler's own fixpoint;
// the Prism side decodes the document into the typed vocabulary and runs the
// standard library's worklist.
#[test]
fn flow_reach_agrees_with_the_compilers_own_least_fixpoint() {
    let artifact = flow_artifact();
    let doc: Value =
        serde_json::from_str(&fs::read_to_string(&artifact).expect("artifact")).expect("JSON");
    let calls = document_calls(&doc);
    let seed = calls.clone();
    let solution = least_fixpoint(seed, |k, cur| {
        let mut s: BTreeSet<String> = calls.get(k).into_iter().flatten().cloned().collect();
        for j in calls.get(k).into_iter().flatten() {
            s.extend(cur.get(j).into_iter().flatten().cloned());
        }
        s
    });
    let prism: String = flow_harness(&artifact)
        .lines()
        .filter(|l| l.starts_with(REACHES))
        .fold(String::new(), |mut s, l| {
            let _ = writeln!(s, "{l}");
            s
        });
    assert_eq!(
        prism,
        render(&solution, "reaches "),
        "the standard library's pass over the document and the compiler's own fixpoint disagree"
    );
}
