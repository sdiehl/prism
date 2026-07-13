use std::collections::BTreeMap;

use prism::{check_on_in, with_prelude, CompilerSession, Config, Root, SessionStats};

#[test]
fn repeated_frontend_query_hits_by_raw_input_identity() {
    let session = CompilerSession::new();
    let cfg = Config {
        session: Some(session.clone()),
        ..Config::default()
    };
    let roots = [Root::Embedded(prism::stdlib::STDLIB)];
    let src = with_prelude("fn answer() = 42");

    let first = check_on_in(&src, &roots, &cfg).unwrap();
    assert_eq!(
        session.stats(),
        SessionStats {
            hits: 0,
            misses: 1,
            writes: 1
        }
    );
    let second = check_on_in(&src, &roots, &cfg).unwrap();
    let first_facts = first
        .decls
        .iter()
        .map(|decl| (decl.name.clone(), decl.ty.show()))
        .collect::<Vec<_>>();
    let second_facts = second
        .decls
        .iter()
        .map(|decl| (decl.name.clone(), decl.ty.show()))
        .collect::<Vec<_>>();
    assert_eq!(first_facts, second_facts);
    assert_eq!(
        session.stats(),
        SessionStats {
            hits: 1,
            misses: 1,
            writes: 1
        }
    );

    let changed = with_prelude("fn answer() = 43");
    check_on_in(&changed, &roots, &cfg).unwrap();
    assert_eq!(
        session.stats(),
        SessionStats {
            hits: 1,
            misses: 2,
            writes: 2
        }
    );
}

#[test]
fn trivia_edit_reuses_semantics_and_rebases_diagnostics() {
    let session = CompilerSession::new();
    let cfg = Config {
        session: Some(session.clone()),
        ..Config::default()
    };
    let roots = [Root::Embedded(prism::stdlib::STDLIB)];
    let before = with_prelude("fn answer() : Int ! {IO} =\n  let unused = 1\n  42\n");
    let after =
        with_prelude("\n-- shifted trivia\nfn answer () : Int ! {IO} =\n  let unused = 1\n  42\n");

    let first = check_on_in(&before, &roots, &cfg).unwrap();
    let second = check_on_in(&after, &roots, &cfg).unwrap();
    let first_warning = first
        .warnings
        .iter()
        .find(|warning| warning.msg.contains("unused"))
        .unwrap();
    let second_warning = second
        .warnings
        .iter()
        .find(|warning| warning.msg.contains("unused"))
        .unwrap();
    assert_eq!(first_warning.msg, second_warning.msg);
    assert_ne!(first_warning.span, second_warning.span);
    let first_checker_warning = first
        .warnings
        .iter()
        .find(|warning| warning.msg.contains("never performed"))
        .unwrap();
    let second_checker_warning = second
        .warnings
        .iter()
        .find(|warning| warning.msg.contains("never performed"))
        .unwrap();
    assert_eq!(first_checker_warning.msg, second_checker_warning.msg);
    assert_ne!(first_checker_warning.span, second_checker_warning.span);
    assert_eq!(
        first
            .decls
            .iter()
            .map(|decl| decl.ty.show())
            .collect::<Vec<_>>(),
        second
            .decls
            .iter()
            .map(|decl| decl.ty.show())
            .collect::<Vec<_>>()
    );
    assert_eq!(
        session.stats(),
        SessionStats {
            hits: 1,
            misses: 1,
            writes: 2
        }
    );
}

#[test]
fn imported_module_trivia_reuses_the_frontend_query() {
    let session = CompilerSession::new();
    let cfg = Config {
        session: Some(session.clone()),
        ..Config::default()
    };
    let source = with_prelude("import Helper\nfn answer() : Int = Helper.value()\n");
    let roots = |module: &str| {
        vec![
            Root::source_bundle(
                "fixture".to_string(),
                BTreeMap::from([("Helper".to_string(), module.to_string())]),
            ),
            Root::Embedded(prism::stdlib::STDLIB),
        ]
    };

    let first = check_on_in(&source, &roots("pub fn value() : Int = 42\n"), &cfg).unwrap();
    let second = check_on_in(
        &source,
        &roots("\n-- module trivia\npub fn value () : Int = 42\n"),
        &cfg,
    )
    .unwrap();
    assert_eq!(
        first
            .decls
            .iter()
            .map(|decl| decl.ty.show())
            .collect::<Vec<_>>(),
        second
            .decls
            .iter()
            .map(|decl| decl.ty.show())
            .collect::<Vec<_>>()
    );
    assert_eq!(
        session.stats(),
        SessionStats {
            hits: 1,
            misses: 1,
            writes: 2
        }
    );
}
