use std::collections::BTreeSet;
use std::path::Path;

use crate::core::DepGraph;
use crate::driver::namespace_layers;
use crate::sym::Sym;
use crate::{default_roots, with_prelude, ModuleSource};

use super::{
    build, EdgeKind, Index, IndexInput, Kind, PrimitiveKind, TestLayer, Vis, INDEX_FORMAT,
};

const MODULE: &str = "M";

// Index one inline module as the entry, the shape every test below uses. No
// imports, so the module search path is only the embedded standard library.
fn index_of(source: &str) -> Index {
    let modules = vec![ModuleSource {
        dotted: MODULE.into(),
        title: MODULE.into(),
        source: source.into(),
        source_path: "M.pr".into(),
        is_prelude: false,
    }];
    build(IndexInput {
        modules: &modules,
        source: &with_prelude(source),
        roots: &default_roots(Path::new(".")),
        entry: Some(MODULE),
        title: MODULE.into(),
        embed_source: false,
    })
    .expect("index the module")
}

fn def<'a>(index: &'a Index, id: &str) -> &'a super::Def {
    index
        .def(id)
        .unwrap_or_else(|| panic!("no definition `{id}` in {:?}", ids(index)))
}

fn ids(index: &Index) -> Vec<&str> {
    index.defs.iter().map(|d| d.id.as_str()).collect()
}

fn targets<'a>(index: &'a Index, kind: EdgeKind, from: &str) -> Vec<&'a str> {
    index
        .edges
        .iter()
        .filter(|e| e.kind == kind && e.from == from)
        .map(|e| e.to.as_str())
        .collect()
}

// The standard library as one index: the only fixture here that spans modules, so
// the only one where a cross-module property can be stated.
fn stdlib_index() -> Index {
    build(IndexInput {
        modules: &crate::stdlib_modules(),
        source: &crate::driver::stdlib_driver_src(),
        roots: &[crate::Root::Embedded(crate::stdlib::STDLIB)],
        entry: None,
        title: "Standard Library".into(),
        embed_source: false,
    })
    .expect("index the standard library")
}

fn named_unit(mut index: Index, module: &str) -> Index {
    index.modules[0].dotted = module.into();
    for def in &mut index.defs {
        let old = def.id.clone();
        def.module = module.into();
        def.id = format!("{module}.{old}");
        for edge in &mut index.edges {
            if edge.from == old {
                edge.from = def.id.clone();
            }
            if edge.to == old {
                edge.to = def.id.clone();
            }
        }
    }
    index.envelope.title = module.into();
    index
}

#[test]
fn independently_built_units_merge_deterministically() {
    let left = named_unit(index_of("fn one(x : Int) : Int = x\n"), "Left");
    let right = named_unit(index_of("fn two(x : Float) : Float = x\n"), "Right");
    let merged = Index::merge("Reference".into(), vec![left.clone(), right.clone()]).unwrap();
    let again = Index::merge("Reference".into(), vec![left, right]).unwrap();

    assert_eq!(merged, again);
    assert!(merged.def("Left.one").is_some());
    assert!(merged.def("Right.two").is_some());
    assert_eq!(
        merged.builtins.iter().filter(|p| p.name == "Float").count(),
        1
    );
}

#[test]
fn merging_rebases_interned_span_indexes() {
    let mut shared = vec!["keyword".to_string()];
    let packed = super::merge_packed(
        "0 4 0 1 2 1",
        &["type".to_string(), "keyword".to_string()],
        &mut shared,
    )
    .unwrap();
    assert_eq!(packed, "0 4 1 1 2 0");
    assert_eq!(shared, ["keyword", "type"]);
}

const SIMPLE: &str = "\
-- | Double a number.
fn double(x: Int): Int = x * 2

-- | Quadruple via double.
pub fn quad(x: Int): Int = double(double(x))

fn main(): Unit ! {IO} = print(show(quad(3)))
";

// The index must not be a second, parallel notion of identity. A definition's
// address has to be the very digest the namespace layers assign it, or a
// bookmark taken in a viewer would not survive being compared against a build.
#[test]
fn addresses_are_the_namespace_layers_digests() {
    let index = index_of(SIMPLE);
    let layers = namespace_layers(&with_prelude(SIMPLE), &default_roots(Path::new(".")))
        .expect("namespace layers");
    for name in ["double", "quad", "main"] {
        let expected = layers
            .defs
            .get(&Sym::new(name))
            .unwrap_or_else(|| panic!("`{name}` has no behavior hash"));
        assert_eq!(
            def(&index, name).hash.as_deref(),
            Some(expected.as_str()),
            "`{name}`'s index address is not its namespace-layer digest"
        );
    }
}

// The entry module's declarations are compiled at the root, so Core names them
// bare regardless of their `pub` marker. Visibility is still reported, because it
// is what a *reader* needs to know; it just does not enter the address.
#[test]
fn entry_module_declarations_are_addressed_bare() {
    let index = index_of(SIMPLE);
    assert_eq!(ids(&index), vec!["double", "quad", "main"]);
    assert_eq!(def(&index, "quad").vis, Vis::Public);
    assert_eq!(def(&index, "double").vis, Vis::Private);
    assert_eq!(def(&index, "quad").module, MODULE);
}

// `calls` must agree with the graph `prism store query callers` answers, edge for
// edge, or the viewer and the CLI would disagree about what depends on what.
#[test]
fn calls_edges_are_the_core_dependency_graph() {
    let index = index_of(SIMPLE);
    let surface =
        crate::driver::addressable_surface(&with_prelude(SIMPLE), &default_roots(Path::new(".")))
            .expect("elaborate");
    let graph = DepGraph::of(&surface.core);
    for name in ["double", "quad", "main"] {
        let mut expected: Vec<String> = graph
            .direct_deps(Sym::new(name))
            .iter()
            .map(|s| s.as_str().to_string())
            .collect();
        let mut found: Vec<String> = targets(&index, EdgeKind::Calls, name)
            .into_iter()
            .map(str::to_string)
            .collect();
        // An instance-method target is retargeted to its instance declaration,
        // which this program has none of, so the two sets are equal here.
        expected.sort();
        found.sort();
        assert_eq!(found, expected, "`{name}`'s call edges");
    }
    assert!(targets(&index, EdgeKind::Calls, "quad").contains(&"double"));
}

// The effect row is the feature a Prism reviewer navigates by, so it is read off
// the checked declaration rather than matched in the rendered type, and a pure
// definition carries no row at all rather than an empty one.
#[test]
fn effect_rows_are_reported_and_pure_definitions_carry_none() {
    let index = index_of(SIMPLE);
    assert_eq!(def(&index, "double").effects, None);
    assert_eq!(def(&index, "main").effects.as_deref(), Some("{IO}"));
    assert_eq!(targets(&index, EdgeKind::Performs, "main"), vec!["IO"]);
    assert!(targets(&index, EdgeKind::Performs, "double").is_empty());
}

// A viewer renders `source` directly, so the slice must be the declaration
// exactly as written — signature, body, and nothing of its neighbours.
#[test]
fn source_slices_and_doc_comments_are_exact() {
    let index = index_of(SIMPLE);
    let double = def(&index, "double");
    assert_eq!(double.source, "fn double(x: Int): Int = x * 2");
    assert_eq!(&SIMPLE[double.span.start..double.span.end], double.source);
    assert_eq!(double.doc.as_deref(), Some("Double a number."));
    // The doc comment is not part of the declaration's own range.
    assert!(!double.source.contains("-- |"));
    assert_eq!(def(&index, "main").doc, None);
}

const KINDS: &str = "\
type Color = Red | Green

alias Ints = List(Int)

effect Ask
  ask() : Int

class Pretty(a)
  pretty : (a) -> String

instance prettyColor : Pretty(Color)
  fn pretty(c) = \"c\"

pub let origin : Int = 0

total fn ident(x: Int): Int = x

fbip fn drop_it(c: Color): Unit = ()

fn ask_twice(): Int ! {Ask} = ask() + ask()
";

// Every surface declaration kind must appear, addressed in the namespace layer
// that owns it, so a viewer's module page is the module — not the subset of it
// that happens to be a function.
#[test]
fn every_declaration_kind_is_indexed_and_addressed_in_its_own_layer() {
    let index = index_of(KINDS);
    let kind_of = |id: &str| def(&index, id).kind;
    assert_eq!(kind_of("Color"), Kind::Type);
    assert_eq!(kind_of("Ints"), Kind::Synonym);
    assert_eq!(kind_of("Ask"), Kind::Effect);
    assert_eq!(kind_of("Pretty"), Kind::Class);
    assert_eq!(kind_of("prettyColor"), Kind::Instance);
    assert_eq!(kind_of("origin"), Kind::Const);

    // A type, a class, an instance, and an inlined constant each have an address,
    // in four different layers.
    for id in ["Color", "Ask", "Pretty", "prettyColor", "origin"] {
        assert!(
            def(&index, id).hash.is_some(),
            "`{id}` should carry a content address"
        );
    }
    // A synonym erases into the types that mention it, so it has none.
    assert_eq!(def(&index, "Ints").hash, None);

    assert_eq!(
        targets(&index, EdgeKind::InstanceOf, "prettyColor"),
        vec!["Pretty"]
    );
    assert!(targets(&index, EdgeKind::UsesType, "prettyColor.pretty").is_empty());
    assert!(targets(&index, EdgeKind::UsesType, "drop_it").contains(&"Color"));
    assert!(targets(&index, EdgeKind::Performs, "ask_twice").contains(&"Ask"));
}

// The claims are erased before Core, so they never move a behavior hash. That is
// exactly why they have to be carried explicitly: a reviewer cannot infer
// `total` or `fbip` from the address.
#[test]
fn erased_claims_are_carried_on_the_definition() {
    use super::Claim;
    let index = index_of(KINDS);
    assert_eq!(def(&index, "ident").claims, vec![Claim::Total]);
    assert_eq!(def(&index, "drop_it").claims, vec![Claim::Fbip]);
    assert!(def(&index, "ask_twice").claims.is_empty());
}

const TESTED: &str = "\
fn helper(x: Int): Int = x + 1

test fn helper_adds_one() =
  if helper(1) == 2 then () else fail()

fn main(): Unit = ()
";

// A `test fn` is stripped before production Core hashes anything, so without the
// second test-mode pass a test would have no address and "which tests cover this
// definition" would have no answer at all.
#[test]
fn tests_are_addressed_from_the_test_layer_and_linked_to_what_they_exercise() {
    let index = index_of(TESTED);
    assert_eq!(index.envelope.tests, TestLayer::Included);
    let test = def(&index, "helper_adds_one");
    assert_eq!(test.kind, Kind::Test);
    assert!(
        test.hash.is_some(),
        "a test's address comes from the test-mode layer"
    );
    assert_eq!(
        targets(&index, EdgeKind::Tests, "helper_adds_one"),
        vec!["helper"]
    );
}

// A test-free input must say so, rather than leaving an empty edge set that reads
// like "nothing is tested".
#[test]
fn a_test_free_input_reports_an_empty_test_layer() {
    assert_eq!(index_of(SIMPLE).envelope.tests, TestLayer::Empty);
}

const SHADOWED: &str = "\
fn apply_twice(map: (Int) -> Int, x: Int): Int = map(map(x))

fn use_global(xs: List(Int)): List(Int) = map(\\(x) -> x, xs)
";

// A link must cover the name and nothing else. Every other resolution site in
// the renamer carries the span of the construct *around* the name, so this pins
// the one invariant that makes the export usable: each recorded range, sliced out
// of the source the renamer saw, is exactly the identifier that was written.
#[test]
fn every_occurrence_span_is_exactly_the_written_identifier() {
    let full = with_prelude(SIMPLE);
    let doc = super::occurrences::extract(&full, &default_roots(Path::new(".")))
        .expect("extract occurrences");
    assert!(!doc.refs.is_empty());
    for r in &doc.refs {
        // Only the root module's ranges index into `full`; a reference inside an
        // imported module indexes into that module's own source.
        if !r.module.is_empty() {
            continue;
        }
        let written = &full[r.start..r.end];
        let tail = r.target.rsplit(['.', '@']).next().unwrap_or(&r.target);
        assert!(
            written == tail || written == r.target,
            "range {}..{} holds {written:?}, not the name `{}` it resolves to",
            r.start,
            r.end,
            r.target
        );
    }
}

// A parameter that shadows a top-level name refers to the binder, not the
// definition, so it must not be recorded — the failure mode a hand-written walk
// would produce, and the reason collection lives in the renamer, which already
// carries the scope stack.
#[test]
fn a_local_shadowing_a_global_is_not_an_occurrence() {
    let full = with_prelude(SHADOWED);
    let doc = super::occurrences::extract(&full, &default_roots(Path::new(".")))
        .expect("extract occurrences");
    let of = |owner: &str| -> Vec<&str> {
        doc.refs
            .iter()
            .filter(|r| r.owner == owner)
            .map(|r| r.target.as_str())
            .collect()
    };
    // `map` here is the parameter, so the body references no definition at all.
    assert!(
        of("apply_twice").is_empty(),
        "the shadowing parameter was recorded as a reference: {:?}",
        of("apply_twice")
    );
    // The same spelling one function later, unshadowed, is the real reference —
    // and it resolves to the canonical name the prelude's glob import gives it,
    // not the bare spelling, so a consumer can link it without guessing which
    // module it came from.
    assert_eq!(of("use_global"), vec!["Data.List.map"]);
}

// The reference relation, read in both directions from the same rows: forward it
// is goto-definition, and grouped by target it is find-references.
#[test]
fn occurrences_carry_their_owner_and_target() {
    let full = with_prelude(SIMPLE);
    let doc = super::occurrences::extract(&full, &default_roots(Path::new(".")))
        .expect("extract occurrences");
    let quad_calls: Vec<&str> = doc
        .refs
        .iter()
        .filter(|r| r.owner == "quad")
        .map(|r| r.target.as_str())
        .collect();
    assert_eq!(
        quad_calls,
        vec!["double", "double"],
        "quad calls double twice"
    );
    let users_of_quad: Vec<&str> = doc
        .refs
        .iter()
        .filter(|r| r.target == "quad")
        .map(|r| r.owner.as_str())
        .collect();
    assert_eq!(users_of_quad, vec!["main"]);
}

// The document is an artifact like any other: same source, same bytes.
#[test]
fn the_occurrence_document_round_trips_and_is_reproducible() {
    let full = with_prelude(SIMPLE);
    let roots = default_roots(Path::new("."));
    let first = super::occurrences::extract(&full, &roots).expect("extract");
    let second = super::occurrences::extract(&full, &roots).expect("extract");
    let json = first.to_json().expect("serialize");
    assert_eq!(json, second.to_json().expect("serialize"));
    assert_eq!(
        super::occurrences::Occurrences::from_json(&json).expect("round trip"),
        first
    );
    assert!(super::occurrences::Occurrences::from_json(
        &json.replace(super::OCCURRENCES_FORMAT, "prism-occurrences-v0")
    )
    .is_err());
}

// The edges say what a definition depends on; the refs say where in its text. A
// consumer renders a navigable body by slicing `source` at these offsets, so they
// have to index `source` itself — not the compiled program the renamer walked,
// which for the root module begins with the whole prelude.
#[test]
fn refs_are_offsets_into_the_definitions_own_source() {
    let index = index_of(SIMPLE);
    let quad = def(&index, "quad");
    assert_eq!(
        quad.refs
            .iter()
            .map(|r| r.target.as_str())
            .collect::<Vec<_>>(),
        vec!["double", "double"],
    );
    for r in &quad.refs {
        assert_eq!(&quad.source[r.start..r.end], "double");
    }
    // Every definition in the index, not just this one: a ref must slice the name
    // it resolves to out of the text it claims to be in.
    for d in &index.defs {
        for r in &d.refs {
            let written = &d.source[r.start..r.end];
            let tail = r.target.rsplit(['.', '@']).next().unwrap_or(&r.target);
            assert!(
                written == tail || written == r.target,
                "`{}`: offsets {}..{} hold {written:?}, not `{}`",
                d.id,
                r.start,
                r.end,
                r.target
            );
        }
    }
    // A definition that calls nothing has none, rather than an empty-range entry.
    assert!(def(&index, "double").refs.is_empty());
}

// The in-body links and the `calls` edges are two views of one fact, so they must
// not disagree about what a definition references.
#[test]
fn in_body_refs_agree_with_the_calls_edges() {
    let index = index_of(SIMPLE);
    let refs: BTreeSet<&str> = def(&index, "main")
        .refs
        .iter()
        .map(|r| r.target.as_str())
        .filter(|t| index.def(t).is_some())
        .collect();
    let edges: BTreeSet<&str> = targets(&index, EdgeKind::Calls, "main")
        .into_iter()
        .filter(|t| index.def(t).is_some())
        .collect();
    assert_eq!(refs, edges);
}

const MEMBERS: &str = "\
type Tree = Leaf | Node(Tree, Tree)

effect Chime
  ring() : Unit

fn build(): Tree = Node(Leaf, Leaf)

fn ding(): Unit ! {Chime} = ring()

fn main(): Unit ! {IO} = print(show(str_len(\"x\")))
";

// A constructor, an operation, and a method are written *inside* another
// declaration and are not definitions in their own right, so a reference to one
// used to resolve to nothing — and `Cons`, `Some`, and `Err` are among the most
// written names in any program. Each now lands on the declaration its source is
// in, the same retarget a lowered instance method gets.
#[test]
fn a_constructor_or_operation_reference_lands_on_its_declaration() {
    let index = index_of(MEMBERS);
    let target_of = |owner: &str, written: &str| -> Option<&str> {
        let d = def(&index, owner);
        d.refs
            .iter()
            .find(|r| &d.source[r.start..r.end] == written)
            .map(|r| r.target.as_str())
    };
    assert_eq!(target_of("build", "Node"), Some("Tree"));
    assert_eq!(target_of("build", "Leaf"), Some("Tree"));
    assert_eq!(target_of("ding", "ring"), Some("Chime"));
}

// A primitive is not a link and not a gap. The distinction has to survive into
// the artifact, or a consumer can only report the name as missing — which reads as
// an incomplete index when the truth is that the compiler implements it.
#[test]
fn primitives_are_named_as_such_rather_than_left_unexplained() {
    let index = index_of(MEMBERS);
    let builtins: BTreeSet<&str> = index.builtins.iter().map(|p| p.name.as_str()).collect();
    assert!(
        builtins.contains("str_len"),
        "the builtin table is missing entries"
    );
    // Float operations live in their own table; including only the elaborator's
    // left `to_float` looking like an unexplained reference.
    assert!(
        builtins.contains("to_float"),
        "float primitives are missing"
    );
    assert!(builtins.contains("IO"), "wired-in effects are missing");
    for name in [
        "Unit", "Int", "I64", "U64", "Bool", "Float", "Char", "String",
    ] {
        let primitive = index.builtins.iter().find(|p| p.name == name).unwrap();
        assert_eq!(primitive.kind, PrimitiveKind::Type, "`{name}` kind");
        assert!(primitive.doc.is_some(), "`{name}` should explain itself");
    }
    assert_eq!(
        index.builtins.iter().find(|p| p.name == "IO").unwrap().kind,
        PrimitiveKind::Effect
    );
    // A declared capability is an ordinary definition, never listed as primitive.
    assert!(!builtins.contains("Chime"));

    // Scalar names lex as dedicated keywords rather than uppercase identifiers.
    // They still need source locations so the viewer can make them links.
    let ding = def(&index, "ding");
    assert!(ding
        .refs
        .iter()
        .chain(&ding.ty_refs)
        .any(|r| r.target == "Unit"));
}

// The claim the two fixes together are worth: over an artifact that contains the
// whole program, every written name is either a definition to navigate to or a
// primitive that can be named as one. Nothing is left reported as missing, which
// is what made a complete index look full of holes.
#[test]
fn no_reference_in_a_whole_program_index_is_left_unexplained() {
    let index = stdlib_index();
    let ids: BTreeSet<&str> = index.defs.iter().map(|d| d.id.as_str()).collect();
    let builtins: BTreeSet<&str> = index.builtins.iter().map(|p| p.name.as_str()).collect();
    let mut unexplained: Vec<String> = Vec::new();
    for d in &index.defs {
        for r in &d.refs {
            let bare = r.target.rsplit(['.', '@']).next().unwrap_or(&r.target);
            if !ids.contains(r.target.as_str()) && !builtins.contains(bare) {
                unexplained.push(format!("{} (in {})", r.target, d.id));
            }
        }
    }
    unexplained.sort();
    unexplained.dedup();
    assert!(
        unexplained.is_empty(),
        "{} references are neither indexed nor known primitives: {:?}",
        unexplained.len(),
        &unexplained[..unexplained.len().min(10)]
    );
}

const EFFECT_REFS: &str = "\
effect Ask
  ask() : Int

effect Chirp(a)
  chirp(a) : Unit

fn one(): Int ! {Ask} = ask()

fn two(): Unit ! {Ask, Chirp(Int)} = chirp(ask())

fn main(): Unit = ()
";

// A written effect row is the axis a Prism reviewer navigates by, so a label in
// one is a reference like any other name — and it must cover the label's name and
// not its argument list, or the link would swallow `Emit(Int)` entire.
#[test]
fn effect_row_labels_are_occurrences_over_the_label_name_alone() {
    let full = with_prelude(EFFECT_REFS);
    let doc = super::occurrences::extract(&full, &default_roots(Path::new(".")))
        .expect("extract occurrences");
    let of = |owner: &str| -> BTreeSet<&str> {
        doc.refs
            .iter()
            .filter(|r| r.owner == owner)
            .map(|r| r.target.as_str())
            .collect()
    };
    // The row labels, alongside the operation calls that were already reported.
    assert!(
        of("one").contains("Ask"),
        "row label missing: {:?}",
        of("one")
    );
    assert!(
        of("two").contains("Ask") && of("two").contains("Chirp"),
        "{:?}",
        of("two")
    );

    // The span is the name, not the label with its arguments.
    for r in doc
        .refs
        .iter()
        .filter(|r| r.target == "Chirp" && r.owner == "two")
    {
        assert_eq!(&full[r.start..r.end], "Chirp");
    }

    // And the index places them in the definition's own text like any other ref.
    // Both the row labels and the operation calls resolve to the effect: the label
    // because that is what it names, the call because an operation is declared
    // inside its effect and has no definition of its own.
    let index = index_of(EFFECT_REFS);
    let two = def(&index, "two");
    let pairs: Vec<(&str, &str)> = two
        .refs
        .iter()
        .map(|r| (&two.source[r.start..r.end], r.target.as_str()))
        .collect();
    assert_eq!(
        pairs,
        vec![
            ("Ask", "Ask"),
            ("Chirp", "Chirp"),
            ("chirp", "Chirp"),
            ("ask", "Ask")
        ],
        "row labels and operation calls, in source order"
    );
}

const TYPE_REFS: &str = "\
type Doc = Empty | Text(String) | Nest(Doc, Doc)

type Wrap = Wrap(Doc)

alias Docs = List(Doc)

effect Render
  emit_doc(Doc) : Unit

class Pretty(a)
  pretty : (a) -> Doc

fn render(d: Doc): String = \"\"

fn main(): Unit = ()
";

// A type is used by more than the functions over it. Without the types that embed
// it, the classes whose methods mention it, and the effects whose operations carry
// it, "who uses this type" answers a fraction of the question.
#[test]
fn uses_type_covers_declarations_and_not_only_terms() {
    let index = index_of(TYPE_REFS);
    let users: BTreeSet<&str> = index
        .edges
        .iter()
        .filter(|e| e.kind == EdgeKind::UsesType && e.to == "Doc")
        .map(|e| e.from.as_str())
        .collect();
    // A term's inferred type, as before; plus the four declaration positions a
    // type can be written into.
    for from in ["render", "Wrap", "Render", "Pretty", "Docs"] {
        assert!(
            users.contains(from),
            "`{from}` uses `Doc` but is not linked: {users:?}"
        );
    }
    // A recursive type does not use itself: `Nest(Doc, Doc)` is not an edge from
    // `Doc` to `Doc`, which would be noise on every recursive declaration.
    assert!(!users.contains("Doc"));
}

// The reason to walk the type structurally rather than match the rendered text:
// the written name is ambiguous across modules, and the resolved symbol is not.
#[test]
fn uses_type_distinguishes_same_named_types_from_different_modules() {
    // Two modules cannot be declared inline here, so this pins the property on the
    // standard library, which really does declare three distinct `Outcome` types.
    let index = stdlib_index();

    let outcomes: BTreeSet<&str> = index
        .defs
        .iter()
        .filter(|d| d.name == "Outcome")
        .map(|d| d.id.as_str())
        .collect();
    assert!(
        outcomes.len() > 1,
        "this test needs several same-named types to be meaningful: {outcomes:?}"
    );

    // `Cli.run_args : (Cli.Command(a)) -> Cli.Outcome(a)` mentions exactly one of
    // them. Matching the rendered token `Outcome` would link it to all of them.
    let linked: BTreeSet<&str> = index
        .edges
        .iter()
        .filter(|e| e.kind == EdgeKind::UsesType && e.from == "Cli.run_args")
        .map(|e| e.to.as_str())
        .collect();
    let wrong: Vec<&&str> = outcomes
        .iter()
        .filter(|o| **o != "Cli.Outcome" && linked.contains(*o))
        .collect();
    assert!(
        linked.contains("Cli.Outcome"),
        "the real one is missing: {linked:?}"
    );
    assert!(
        wrong.is_empty(),
        "linked to a same-named type it does not use: {wrong:?}"
    );
}

// One broken file must not take the index of everything else down with it: a
// scratch buffer, or a fixture that exists to be invalid, is carried with its
// diagnostic — the same posture the test layer takes — and every other module
// is indexed exactly as if the broken one were absent.
#[test]
fn a_module_that_does_not_parse_is_carried_with_its_diagnostic() {
    let modules = vec![
        ModuleSource {
            dotted: MODULE.into(),
            title: MODULE.into(),
            source: SIMPLE.into(),
            source_path: "M.pr".into(),
            is_prelude: false,
        },
        ModuleSource {
            dotted: "Scratch".into(),
            title: "Scratch".into(),
            // The contradiction the parser refuses, verbatim from the compiler's
            // own negative fixture corpus.
            source: "fn broken(x : Int @ {once, many}) : Int = x\n".into(),
            source_path: "Scratch.pr".into(),
            is_prelude: false,
        },
    ];
    let index = build(IndexInput {
        modules: &modules,
        source: &with_prelude(SIMPLE),
        roots: &default_roots(Path::new(".")),
        entry: Some(MODULE),
        title: MODULE.into(),
        embed_source: false,
    })
    .expect("the good module still indexes");
    let broken = index
        .modules
        .iter()
        .find(|m| m.dotted == "Scratch")
        .expect("the broken module is still listed");
    assert!(
        broken
            .error
            .as_deref()
            .is_some_and(|e| e.contains("contradict")),
        "{:?}",
        broken.error
    );
    assert!(!index.defs.iter().any(|d| d.module == "Scratch"));
    assert!(def(&index, "quad").hash.is_some());
}

// A declaration's own member sites are members, not references. `Tip` and `Bin`
// inside a recursive type's declaration are where those members come into being;
// resolving them as references would link the declaration back to itself and
// list it among its own members' users.
#[test]
fn a_declarations_own_member_sites_are_members_not_self_references() {
    let index = index_of(
        "\
type Tree = Leaf | Node(Int, Tree, Tree)

fn singleton(n: Int): Tree = Node(n, Leaf, Leaf)

fn main(): Unit ! {IO} = ()
",
    );
    let tree = def(&index, "Tree");
    let members: Vec<&str> = tree.members.iter().map(|m| m.name.as_str()).collect();
    assert_eq!(members, ["Leaf", "Node"]);
    // The declaration sites carry no reference; the recursive `Tree` mentions
    // still do, which is what makes the recursion navigable.
    for m in &tree.members {
        assert!(
            !tree.refs.iter().any(|r| r.start < m.end && m.start < r.end),
            "`{}`'s declaration site should not be a reference",
            m.name
        );
    }
    assert!(tree
        .refs
        .iter()
        .any(|r| tree.source[r.start..r.end] == *"Tree"));
    // A use in another definition still resolves to the owning declaration.
    let singleton = def(&index, "singleton");
    assert!(singleton
        .refs
        .iter()
        .any(|r| singleton.source[r.start..r.end] == *"Node" && r.target == "Tree"));
}

// An effect-row alias is a type-like name. Written inside another alias — the
// composition `alias App = {Boom, Tick}` is what row aliases are for — it must
// link to its declaration exactly as an effect written there does.
#[test]
fn a_row_alias_links_to_the_aliases_it_mentions() {
    let index = index_of(
        "\
effect Raise
  raise(Int) : Int

alias Boom = {Raise}

alias App = {Boom}

fn main(): Unit ! {IO} = print(\"ok\")
",
    );
    let app = def(&index, "App");
    assert_eq!(app.kind, Kind::RowAlias);
    let linked: Vec<&str> = app.refs.iter().map(|r| r.target.as_str()).collect();
    assert!(linked.contains(&"Boom"), "{linked:?}");
    // And an effect written in an alias links as it always did.
    assert!(def(&index, "Boom").refs.iter().any(|r| r.target == "Raise"));
}

// A leaf edit, and the tower of definitions above it.
const REV_OLD: &str = "\
fn base(n: Int): Int = n + 1

fn mid(n: Int): Int = base(n) * 2

fn top(n: Int): Int = mid(n) + mid(n)

fn spare(n: Int): Int = n

fn main(): Unit ! {IO} = print(show(top(1)))
";

fn status_of(diff: &super::IndexDiff, id: &str) -> Option<super::Status> {
    diff.entries.iter().find(|e| e.id == id).map(|e| e.status)
}

// The classification the whole diff exists for.
//
// One edited leaf re-hashes everything above it, because a content address folds
// in what a definition depends on. A tool that reports four changes here is
// useless on a real change; this must report one edit and three consequences.
#[test]
fn an_edit_is_separated_from_the_cone_it_causes() {
    use super::Status;
    let old = index_of(REV_OLD);
    let new = index_of(&REV_OLD.replace("n + 1", "n + 100"));
    let d = super::diff(&old, &new).expect("comparable schemes");

    assert_eq!(status_of(&d, "base"), Some(Status::Changed));
    for above in ["mid", "top", "main"] {
        assert_eq!(
            status_of(&d, above),
            Some(Status::Cone),
            "`{above}` re-hashed under the edit, but its own text did not move"
        );
    }
    // Untouched and out of the cone: absent from the entry list entirely.
    assert_eq!(status_of(&d, "spare"), None);
    assert_eq!(d.envelope.counts.changed, 1);
    assert_eq!(d.envelope.counts.cone, 3);
    assert_eq!(d.envelope.counts.unchanged, 1);
    // Authored work sorts ahead of the cone it caused.
    assert!(d.entries[0].status.is_authored());
}

// A rename keeps a definition's bytes, so content addressing recognizes it as one
// definition under a new name rather than as an unrelated deletion and addition.
// No similarity heuristic is involved: the hashes are equal or they are not.
#[test]
fn a_rename_is_a_move_rather_than_an_add_and_a_delete() {
    use super::Status;
    let old = index_of(REV_OLD);
    let new = index_of(&REV_OLD.replace("spare", "reserve"));
    let d = super::diff(&old, &new).expect("comparable schemes");

    let moved = d
        .entries
        .iter()
        .find(|e| e.status == Status::Moved)
        .expect("the renamed definition");
    assert_eq!(moved.id, "reserve");
    assert_eq!(moved.old_id.as_deref(), Some("spare"));
    assert_eq!(d.envelope.counts.added, 0);
    assert_eq!(d.envelope.counts.removed, 0);
    // Nothing referenced it, so nothing re-hashed.
    assert_eq!(d.envelope.counts.cone, 0);
}

// Reformatting moves text without moving behavior. Separating that from a real
// edit is what keeps a formatting pass from reading as a semantic change — and
// nothing above it re-hashes, which a text diff cannot tell you.
#[test]
fn a_reformat_is_cosmetic_and_causes_no_cone() {
    use super::Status;
    let old = index_of(REV_OLD);
    let new = index_of(&REV_OLD.replace(
        "fn mid(n: Int): Int = base(n) * 2",
        "fn mid(n: Int): Int =\n  base(n) * 2",
    ));
    let d = super::diff(&old, &new).expect("comparable schemes");

    assert_eq!(status_of(&d, "mid"), Some(Status::Cosmetic));
    assert_eq!(d.envelope.counts.changed, 0);
    assert_eq!(d.envelope.counts.cone, 0, "a reformat moves no hash");
}

// Adding and removing, and the artifact's own contract.
#[test]
fn additions_and_removals_carry_only_the_revision_they_have() {
    use super::Status;
    let old = index_of(REV_OLD);
    let new = index_of(&REV_OLD.replace("fn spare(n: Int): Int = n\n\n", ""));
    let d = super::diff(&old, &new).expect("comparable schemes");

    let gone = d
        .entries
        .iter()
        .find(|e| e.id == "spare")
        .expect("the removed definition");
    assert_eq!(gone.status, Status::Removed);
    assert!(gone.new.is_none() && gone.old.is_some());

    // The artifact is self-contained, so a consumer renders a side-by-side from
    // it alone; round-tripping proves the records travel.
    let json = d.to_json().expect("serialize");
    assert_eq!(super::IndexDiff::from_json(&json).expect("round trip"), d);
    assert!(super::IndexDiff::from_json(
        &json.replace(super::INDEX_DIFF_FORMAT, "prism-index-diff-v0")
    )
    .is_err());
}

// Equal hashes prove equal executable behavior, and nothing more. A claims edit
// swaps a proof for a trust root without moving a hashed byte, and a doc comment
// sits outside the definition's source slice, so a doc-only edit moves neither
// the hash nor the text. Both are authored review-facing changes; "cosmetic" for
// the first and silence for the second are exactly the wrong reports.
#[test]
fn a_trust_or_doc_edit_is_authored_rather_than_cosmetic() {
    use super::Status;
    let old = index_of(REV_OLD);

    let trusted = index_of(&REV_OLD.replace("fn spare", "assume total fn spare"));
    assert_eq!(
        def(&old, "spare").hash,
        def(&trusted, "spare").hash,
        "this test needs the claim to be invisible to the hash to be meaningful"
    );
    let d = super::diff(&old, &trusted).expect("comparable schemes");
    assert_eq!(status_of(&d, "spare"), Some(Status::Changed));

    let documented =
        index_of(&REV_OLD.replace("fn spare", "-- | Kept for the next refactor.\nfn spare"));
    assert_eq!(def(&old, "spare").source, def(&documented, "spare").source);
    let d = super::diff(&old, &documented).expect("comparable schemes");
    assert_eq!(status_of(&d, "spare"), Some(Status::Changed));
}

// Digests from different hash schemes are not comparable in either direction:
// equal strings prove nothing, and unequal ones would report identical source as
// a program-wide dependency cone.
#[test]
fn indexes_committing_to_different_schemes_refuse_to_diff() {
    let index = index_of(REV_OLD);
    let mut old = index.clone();
    old.envelope.scheme = "prism-core-hash-v0".into();
    let err = super::diff(&old, &index).expect_err("schemes differ");
    assert!(err.contains("hash schemes"), "{err}");
}

// The entry records index their parent's shared tables, so the diff must carry
// each side's tables or a consumer cannot decode the old side's spans at all.
#[test]
fn the_diff_carries_each_sides_shared_tables() {
    let old = index_of(REV_OLD);
    let new = index_of(&REV_OLD.replace("n + 1", "n + 100"));
    let d = super::diff(&old, &new).expect("comparable schemes");
    assert_eq!(d.envelope.old.token_classes, old.token_classes);
    assert_eq!(d.envelope.old.type_table, old.type_table);
    assert_eq!(d.envelope.new.token_classes, new.token_classes);
    assert_eq!(d.envelope.new.type_table, new.type_table);
}

// Comparing a revision with itself is the identity: the degenerate pair a plain
// single-revision view is.
#[test]
fn a_revision_against_itself_has_no_entries() {
    let index = index_of(REV_OLD);
    let d = super::diff(&index, &index).expect("comparable schemes");
    assert!(d.entries.is_empty());
    assert_eq!(d.envelope.counts.unchanged, index.defs.len());
}

// The artifact is the input to a `--check` gate, so identical source must yield
// identical bytes.
#[test]
fn the_artifact_is_byte_reproducible() {
    let first = index_of(SIMPLE).to_json().expect("serialize");
    let second = index_of(SIMPLE).to_json().expect("serialize");
    assert_eq!(first, second);
}

// Decoding is the consumer's contract: a foreign format and an edge from nowhere
// are both refused, so a viewer never has to defend against them.
#[test]
fn decoding_refuses_a_foreign_format_and_a_dangling_edge_source() {
    let index = index_of(SIMPLE);
    let json = index.to_json().expect("serialize");
    let decoded = Index::from_json(&json).expect("round trip");
    assert_eq!(decoded, index);
    assert_eq!(decoded.envelope.format, INDEX_FORMAT);

    let foreign = json.replace(INDEX_FORMAT, "prism-index-v0");
    assert!(Index::from_json(&foreign)
        .expect_err("a foreign format is refused")
        .contains("prism-index-v0"));

    let dangling = json.replace("\"from\": \"quad\"", "\"from\": \"nowhere\"");
    assert!(Index::from_json(&dangling)
        .expect_err("an edge from an unindexed definition is refused")
        .contains("nowhere"));
}

// A signature is not source: no file holds it, and the typechecker rendered the
// string. So the renamer has no occurrence in it and no lexer has run over it,
// and a consumer that wanted `List` in a type to be the same link it is in a body
// had to tokenize the rendered string itself — a second tokenizer, drifting from
// this one about what a name is. The compiler renders the type, so the compiler
// lexes it too.
#[test]
fn a_rendered_type_carries_its_own_links_and_highlighting() {
    let index = index_of(MEMBERS);
    let build = def(&index, "build");
    let ty = build.ty.as_deref().expect("a term has a rendered type");
    let names: Vec<(&str, &str)> = build
        .ty_refs
        .iter()
        .map(|r| (&ty[r.start..r.end], r.target.as_str()))
        .collect();
    assert_eq!(
        names,
        vec![("Tree", "Tree")],
        "the type name in `{ty}` should resolve to its declaration"
    );
    // The effect row gets the same treatment, so `{Chime}` reaches the effect.
    let ding = def(&index, "ding");
    let row = ding
        .effects
        .as_deref()
        .expect("an effectful term has a row");
    assert_eq!(
        ding.eff_refs
            .iter()
            .map(|r| (&row[r.start..r.end], r.target.as_str()))
            .collect::<Vec<_>>(),
        vec![("Chime", "Chime")],
    );
    // And the spans land inside the text they describe, in order.
    let mut at = 0;
    for triple in build.ty_tokens.split(' ').collect::<Vec<_>>().chunks(3) {
        let [gap, len, _] = triple else { continue };
        let start = at + gap.parse::<usize>().expect("a gap");
        at = start + len.parse::<usize>().expect("a length");
        assert!(at <= ty.len(), "a highlight span runs past `{ty}`");
    }
    assert!(!build.ty_tokens.is_empty(), "a type gains highlight spans");
}

// Handling an effect is what *removes* it from a row, so the definition that
// gives an effect its meaning is precisely the one whose inferred effects no
// longer mention it. Read the rows alone and an effect nobody in this unit
// performs relates to nothing at all — which is the standard library's `Output`,
// performed by programs and handled four times.
#[test]
fn an_effect_reaches_the_definitions_that_handle_it() {
    let index = index_of(HANDLED);
    let handled: Vec<&str> = index
        .edges
        .iter()
        .filter(|e| e.kind == EdgeKind::Handles && e.to == "Chime")
        .map(|e| e.from.as_str())
        .collect();
    assert_eq!(handled, vec!["silence"], "the handler should reach `Chime`");
    // And the effect is genuinely gone from the handler's own row, which is why
    // `performs` cannot answer this.
    let silence = def(&index, "silence");
    assert_eq!(silence.effects, None, "handling discharges the row");
    assert!(!index
        .edges
        .iter()
        .any(|e| e.kind == EdgeKind::Performs && e.from == "silence"),);
}

const HANDLED: &str = "\
effect Chime
  ring() : Unit

fn ding(): Unit ! {Chime} = ring()

fn silence(): Unit = handle ding() with
  ring() resume k => k(())
";

// A declaration's members have to come from the declaration, not from what
// happens to reference them. `Output`'s operations are performed by *programs*, so
// an index of the library that declares it would recover none of them from
// occurrences — and a reader searching for `out_print` would be told the name does
// not exist.
#[test]
fn a_declaration_records_the_members_it_introduces() {
    let index = index_of(MEMBERS);
    let named = |owner: &str| -> Vec<(String, String)> {
        let d = def(&index, owner);
        d.members
            .iter()
            .map(|m| (m.name.clone(), d.source[m.start..m.end].to_string()))
            .collect()
    };
    // The span is the declaration's own text saying the name, every time.
    for owner in ["Tree", "Chime"] {
        for (name, written) in named(owner) {
            assert_eq!(name, written, "`{owner}` misplaced a member");
        }
    }
    assert_eq!(
        named("Tree")
            .into_iter()
            .map(|(n, _)| n)
            .collect::<Vec<_>>(),
        vec!["Leaf", "Node"],
    );
    // An operation nothing in this unit performs is recorded all the same.
    assert_eq!(
        named("Chime")
            .into_iter()
            .map(|(n, _)| n)
            .collect::<Vec<_>>(),
        vec!["ring"],
    );
}

// Elaboration lifts each instance method to its own top-level function
// (`i@showInt@show`), so an instance has no Core node of its own. Asking the
// dependency graph about the instance's own name therefore answered nothing, and
// not one of the standard library's 100 instances had a single outgoing edge —
// a card for an instance could show the class it implements and nothing about the
// functions plainly written in its body.
#[test]
fn an_instance_calls_what_its_methods_call() {
    let index = index_of(INSTANCE_BODY);
    let calls: Vec<&str> = index
        .edges
        .iter()
        .filter(|e| e.kind == EdgeKind::Calls && e.from == "showPair")
        .map(|e| e.to.as_str())
        .collect();
    assert_eq!(
        calls,
        vec!["render"],
        "the instance should reach its method's callee"
    );
    // The instance is still not a term, so it has no address of its own to confuse
    // with the lifted method's.
    assert_eq!(def(&index, "showPair").kind, Kind::Instance);
}

const INSTANCE_BODY: &str = "\
class Show2(a)
  show2 : (a) -> String

fn render(s : String) : String = s

instance showPair : Show2(String)
  fn show2(x) = render(x)
";

// An instance method is checked from inside its instance rather than as a
// top-level function, so it never becomes a `DeclInfo` and its inferred effect row
// was computed, held to the class signature, and dropped. Recording it is the only
// way an instance can say what it performs: Core carries no rows either.
#[test]
fn an_instance_performs_what_its_methods_perform() {
    let index = index_of(EFFECTFUL_INSTANCE);
    let performs: Vec<&str> = index
        .edges
        .iter()
        .filter(|e| e.kind == EdgeKind::Performs && e.from == "noisyInt")
        .map(|e| e.to.as_str())
        .collect();
    assert_eq!(
        performs,
        vec!["Chime"],
        "the instance should report its method's row"
    );
    // The row is the method's own, not the class's declared bound: an instance
    // whose method performs nothing reports nothing.
    assert!(!index
        .edges
        .iter()
        .any(|e| e.kind == EdgeKind::Performs && e.from == "quietInt"),);
}

const EFFECTFUL_INSTANCE: &str = "\
effect Chime
  ring() : Unit

class Bell(a)
  peal : (a) -> Unit ! {Chime}

class Hush(a)
  still : (a) -> Unit ! {Chime}

instance noisyInt : Bell(Int)
  fn peal(x) = ring()

instance quietInt : Hush(Int)
  fn still(x) = ()
";

// The signature answers "what does this take" and stops there; a reader in the
// body wants to know what a name *is* where it is used. The checker stamps every
// expression node with an identity and records a presentable type against it, so
// the index carries the join rather than making a consumer recompute it.
#[test]
fn a_definition_carries_the_type_of_each_name_in_it() {
    let index = index_of(TYPED);
    let d = def(&index, "shout");
    let named: Vec<(&str, &str)> = decode_types(&index, d);
    assert!(
        named.contains(&("who", "String")),
        "the parameter should be typed at its binding site and its uses: {named:?}"
    );
    // Both the binding site and the use inside the call. An argument is reconciled
    // with its parameter by unification rather than synthesized against it, and it
    // carries a type either way.
    assert_eq!(
        named.iter().filter(|(n, _)| *n == "who").count(),
        2,
        "{named:?}"
    );
    assert!(
        named.contains(&("concat", "(String, String) -> String")),
        "a called name is typed too: {named:?}"
    );
    // Only names: a call is not a span of its own, so the sets never nest.
    assert!(named.iter().all(|(n, _)| !n.contains('(')), "{named:?}");
}

#[test]
fn pattern_binders_are_typed_at_their_binding_site() {
    let index = index_of(BINDERS);
    let d = def(&index, "sum_from");
    let named: Vec<(&str, &str)> = decode_types(&index, d);
    // A binder is a pattern, not an expression, so it is typed only because arm
    // patterns are stamped with an identity and the pattern checker records
    // against it. Both names bind at one site and are used at one more.
    assert_eq!(
        named.iter().filter(|(n, _)| *n == "y").count(),
        2,
        "`y` should be typed where it binds and where it is used: {named:?}"
    );
    assert!(named.contains(&("y", "Int")), "{named:?}");
    assert!(
        named.contains(&("rest", "List(Int)")),
        "a binder takes the constructor field's solved type, not the scrutinee's: {named:?}"
    );
}

// The packed triples, resolved against the shared table.
fn decode_types<'a>(index: &'a Index, d: &'a super::Def) -> Vec<(&'a str, &'a str)> {
    let mut out = Vec::new();
    let mut at = 0usize;
    let fields: Vec<&str> = d.types.split(' ').collect();
    for triple in fields.chunks(3) {
        let [gap, len, which] = triple else { continue };
        let start = at + gap.parse::<usize>().expect("a gap");
        let end = start + len.parse::<usize>().expect("a length");
        at = end;
        out.push((
            &d.source[start..end],
            index.type_table[which.parse::<usize>().expect("an index")].as_str(),
        ));
    }
    out
}

const TYPED: &str = "\
fn shout(who : String) : String = concat(who, \"!\")
";

const BINDERS: &str = "\
fn sum_from(xs : List(Int)) : Int =
  match xs of { Nil => 0, Cons(y, rest) => y + sum_from(rest) }
";
