//! Multi-module resolution: qualified, selective, and aliased imports;
//! private-name namespacing; canonical disjoint namespaces; and the scoping
//! rules that let modules share a short name.

use std::path::Path;

use prism::{check_at, interpret_at, with_prelude};
use rstest::rstest;

fn base() -> &'static Path {
    Path::new(concat!(env!("CARGO_MANIFEST_DIR"), "/tests/modules"))
}

fn out(src: &str) -> String {
    let run = interpret_at(&with_prelude(src), base()).expect("should resolve and run");
    run.out.iter().fold(String::new(), |mut s, v| {
        s.push_str(&v.show());
        s.push('\n');
        s
    })
}

fn err(src: &str) -> String {
    check_at(&with_prelude(src), base())
        .expect_err("should fail to resolve")
        .to_string()
}

#[derive(Clone, Copy, Debug)]
enum RunCase {
    QualifiedImport,
    SelectiveImport,
    Alias,
    QualifiedConstructor,
    PrivateExportedWrapper,
    SelectiveSynonym,
    QualifiedSynonym,
    QualifiedNewtype,
    OpaqueExports,
    DottedModulePath,
    FullPathQualifier,
    SharedNamesQualified,
    RootDefinitionShadowsImport,
    PubImportReexportsQualified,
    PubImportSelectivelyImportable,
    PubImportAllReexportsEverything,
    ReexportsChain,
}

impl RunCase {
    const fn src(self) -> &'static str {
        match self {
            Self::QualifiedImport => "import Math\nfn main() = print(Math.square(Math.bump(3)))",
            Self::SelectiveImport => "import Math (square)\nfn main() = print(square(5))",
            Self::Alias => "import Math as M\nfn main() = print(M.square(6))",
            Self::QualifiedConstructor => {
                "import Shape\nfn main() = print(Shape.area(Shape.Circle(4)))"
            }
            Self::PrivateExportedWrapper => "import Box\nfn main() = print(Box.make(7))",
            Self::SelectiveSynonym => {
                r"import Pairs (Pair, mk)
fn snd(p : Pair(Int)) : Int = match p of { (a, b) => b }
fn main() = print(snd(mk(4)))"
            }
            Self::QualifiedSynonym => {
                "import Pairs\nfn main() = match Pairs.mk(9) of { (a, b) => print(a) }"
            }
            Self::QualifiedNewtype => {
                "import Ids\nfn main() = print(Ids.same(Ids.UserId(3), Ids.mk(3)))"
            }
            Self::OpaqueExports => {
                r"import Stack
fn main() =
  let s = Stack.push(5, Stack.empty())
  print(Stack.top(s) == Stack.top(Stack.push(5, Stack.empty())))"
            }
            Self::DottedModulePath => "import Geo.Util\nfn main() = print(Util.one())",
            Self::FullPathQualifier => "import Geo.Util\nfn main() = print(Geo.Util.one())",
            Self::SharedNamesQualified => {
                "import Apple\nimport Banana\nfn main() = print(Apple.dup() + Banana.dup())"
            }
            Self::RootDefinitionShadowsImport => {
                "import Math\nfn square(x : Int) : Int = x\nfn main() = print(square(5))"
            }
            Self::PubImportReexportsQualified => {
                "import Facade\nfn main() = print(Facade.square(5))"
            }
            Self::PubImportSelectivelyImportable => {
                "import Facade (square)\nfn main() = print(square(6))"
            }
            Self::PubImportAllReexportsEverything => {
                "import FacadeAll\nfn main() = print(FacadeAll.bump(3))"
            }
            Self::ReexportsChain => "import Facade2\nfn main() = print(Facade2.square(7))",
        }
    }

    const fn want(self) -> &'static str {
        match self {
            Self::QualifiedImport | Self::QualifiedConstructor => "16\n",
            Self::SelectiveImport | Self::PubImportReexportsQualified => "25\n",
            Self::Alias | Self::PubImportSelectivelyImportable => "36\n",
            Self::PrivateExportedWrapper => "7\n",
            Self::DottedModulePath | Self::FullPathQualifier => "1\n",
            Self::SelectiveSynonym | Self::PubImportAllReexportsEverything => "4\n",
            Self::QualifiedSynonym => "9\n",
            Self::QualifiedNewtype | Self::OpaqueExports => "true\n",
            Self::SharedNamesQualified => "3\n",
            Self::RootDefinitionShadowsImport => "5\n",
            Self::ReexportsChain => "49\n",
        }
    }
}

#[rstest]
fn module_programs_resolve_and_run(
    #[values(
        RunCase::QualifiedImport,
        RunCase::SelectiveImport,
        RunCase::Alias,
        RunCase::QualifiedConstructor,
        RunCase::PrivateExportedWrapper,
        RunCase::SelectiveSynonym,
        RunCase::QualifiedSynonym,
        RunCase::QualifiedNewtype,
        RunCase::OpaqueExports,
        RunCase::DottedModulePath,
        RunCase::FullPathQualifier,
        RunCase::SharedNamesQualified,
        RunCase::RootDefinitionShadowsImport,
        RunCase::PubImportReexportsQualified,
        RunCase::PubImportSelectivelyImportable,
        RunCase::PubImportAllReexportsEverything,
        RunCase::ReexportsChain
    )]
    case: RunCase,
) {
    assert_eq!(out(case.src()), case.want(), "{case:?}");
}

#[derive(Clone, Copy, Debug)]
enum RejectCase {
    PrivateSelectiveImport,
    OpaqueConstructorHidden,
    OpaqueConstructorUnmatchable,
    SharedNameUnqualified,
    SelectiveImportIsolation,
    QualifiedPrivateName,
    UnqualifiedAmbiguity,
    PlainImportDoesNotReexport,
    SelectiveImportMissingName,
    UnknownQualifier,
    UnimportedModule,
}

impl RejectCase {
    const fn src(self) -> &'static str {
        match self {
            Self::PrivateSelectiveImport => "import Box (unwrap)\nfn main() = print(0)",
            Self::OpaqueConstructorHidden => {
                "import Stack\nfn main() = print(Stack.top(Stack.Push(9, Stack.empty())))"
            }
            Self::OpaqueConstructorUnmatchable => {
                r"import Stack
fn main() = match Stack.empty() of { Stack.Empty => print(0), _ => print(1) }"
            }
            Self::SharedNameUnqualified => "import Apple\nimport Banana\nfn main() = print(dup())",
            Self::SelectiveImportIsolation => "import Math (square)\nfn main() = print(bump(1))",
            Self::QualifiedPrivateName => "import Math\nfn main() = print(Math.helper(1))",
            Self::UnqualifiedAmbiguity => {
                "import LibA (map)\nimport LibB (map)\nfn main() = print(map(1))"
            }
            Self::PlainImportDoesNotReexport => {
                "import PlainFacade\nfn main() = print(PlainFacade.square(5))"
            }
            Self::SelectiveImportMissingName => "import Math (nope)\nfn main() = print(0)",
            Self::UnknownQualifier => "import Math\nfn main() = print(Nope.square(1))",
            Self::UnimportedModule => "import Missing\nfn main() = print(0)",
        }
    }

    const fn needle(self) -> &'static str {
        match self {
            Self::PrivateSelectiveImport => "does not export `unwrap`",
            Self::OpaqueConstructorHidden => "does not export `Push`",
            Self::OpaqueConstructorUnmatchable => "does not export `Empty`",
            Self::SharedNameUnqualified | Self::SelectiveImportIsolation => "unbound variable",
            Self::QualifiedPrivateName => "does not export `helper`",
            Self::UnqualifiedAmbiguity => "`map` is ambiguous",
            Self::PlainImportDoesNotReexport => "does not export `square`",
            Self::SelectiveImportMissingName => "does not export `nope`",
            Self::UnknownQualifier => "Nope",
            Self::UnimportedModule => "Missing",
        }
    }
}

#[rstest]
fn module_programs_reject_with_expected_surface(
    #[values(
        RejectCase::PrivateSelectiveImport,
        RejectCase::OpaqueConstructorHidden,
        RejectCase::OpaqueConstructorUnmatchable,
        RejectCase::SharedNameUnqualified,
        RejectCase::SelectiveImportIsolation,
        RejectCase::QualifiedPrivateName,
        RejectCase::UnqualifiedAmbiguity,
        RejectCase::PlainImportDoesNotReexport,
        RejectCase::SelectiveImportMissingName,
        RejectCase::UnknownQualifier,
        RejectCase::UnimportedModule
    )]
    case: RejectCase,
) {
    let e = err(case.src());
    assert!(e.contains(case.needle()), "{case:?}: {e}");
}

fn warnings(src: &str) -> Vec<String> {
    check_at(&with_prelude(src), base())
        .expect("should type check")
        .warnings
        .into_iter()
        .map(|w| w.msg)
        .collect()
}

#[test]
fn type_local_instance_is_not_an_orphan() {
    // Stack derives Eq in its own module, anchored to the type: no warning.
    let ws = warnings("import Stack\nfn main() = print(0)");
    assert!(!ws.iter().any(|w| w.contains("orphan")), "{ws:?}");
}

#[test]
fn instance_far_from_class_and_type_warns_orphan() {
    // `Orphan` defines Eq(Widget) but owns neither Eq (prelude) nor Widget (Typ).
    let ws = warnings("import Orphan\nfn main() = print(0)");
    assert!(
        ws.iter().any(|w| w.contains("orphan instance `weq`")),
        "{ws:?}"
    );
}

#[test]
fn overlap_across_modules_is_coherence_error() {
    // Two independently-authored Eq(Widget) instances assembled into one program:
    // coherence forbids silent ambiguity, so it is a definition-site error unless
    // the importer designates a canonical one (the open-world "importer decides").
    let e = err("import Orphan\nimport OrphanB\nfn main() = print(0)");
    assert!(
        e.contains("instances for") && e.contains("canonical"),
        "{e}"
    );
}

#[test]
fn canonical_designation_resolves_cross_module_overlap() {
    // The importer breaks the tie with a canonical binding; the program checks.
    let ws = warnings(
        "import Typ (Widget)\nimport Orphan\nimport OrphanB\ncanonical Eq(Widget) = weq\nfn main() = print(0)",
    );
    assert!(!ws.iter().any(|w| w.contains("instances for")), "{ws:?}");
}
