//! End-to-end conformance for the `prism test` lane (TESTING.md T0-T2).
//!
//! Covers the "Initial conformance suite" items: inline private access,
//! integration public-only access, discovery of an unreachable module, absence
//! of tests from a normal build, production neutrality, invalid-signature and
//! duplicate diagnostics, distinct outcome classification, output capture and
//! `--show-output`, filter/exact/list/no-match, fresh-world isolation, canonical
//! JSON events, byte-identical repeated manifests, and both project and
//! single-file invocation.

use std::path::{Path, PathBuf};

use prism::cli::test::TestOptions;
use prism::testing::{
    decode_failure, decode_manifest, descriptors_for_file, descriptors_for_project, encode_failure,
    encode_manifest, event_bytes, list_output, run_results, structured_failure_events, test_cmd,
    Failure, TestStatus,
};
use prism::Config;

fn project() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/projects/prism_test_basic")
}

fn case(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(format!("tests/cases/prism_test/{name}"))
}

fn opts() -> TestOptions {
    TestOptions::default()
}

fn filtered(filter: &str) -> TestOptions {
    TestOptions {
        filter: Some(filter.to_string()),
        ..TestOptions::default()
    }
}

fn ids(results: &[prism::testing::TestResult]) -> Vec<String> {
    results.iter().map(|r| r.id.clone()).collect()
}

fn status_of<'a>(
    results: &'a [prism::testing::TestResult],
    id: &str,
) -> &'a prism::testing::TestResult {
    results
        .iter()
        .find(|r| r.id == id)
        .unwrap_or_else(|| panic!("no result for `{id}` in {:?}", ids(results)))
}

// 1, 3, 14: inline private access, unreachable module, and integration
// discovery, all for a project invocation.
#[test]
fn discovers_units_integration_and_unreachable() {
    let results = run_results(Some(&project()), &opts(), &Config::default()).expect("run project");
    let names = ids(&results);
    assert!(
        names.contains(&"Parser::normalize_is_private_but_visible_inline".to_string()),
        "inline unit test with private access missing: {names:?}"
    );
    assert!(
        names.contains(&"Unreached::unreached_module_is_tested".to_string()),
        "unreachable module test missing: {names:?}"
    );
    assert!(
        names.contains(&"integration::public::public_api_is_reachable".to_string()),
        "integration test missing: {names:?}"
    );
    // The inline private-access test passes, proving the private helper is visible.
    assert_eq!(
        status_of(&results, "Parser::normalize_is_private_but_visible_inline").status,
        TestStatus::Passed
    );
    assert_eq!(
        status_of(&results, "integration::public::public_api_is_reachable").status,
        TestStatus::Passed
    );
    assert_eq!(
        status_of(&results, "Unreached::unreached_module_is_tested").status,
        TestStatus::Passed
    );
}

// 4, 5: tests are absent from a normal build's namespace, and test-only edits
// leave production Core hashes byte-identical (production neutrality).
#[test]
fn production_build_excludes_tests_and_is_neutral() {
    let base = "fn inc(n) = n + 1\nfn main() = println(inc(3))\n";
    let with_test =
        "fn inc(n) = n + 1\ntest fn inc_adds_one() = if inc(3) == 4 then () else fail()\nfn main() = println(inc(3))\n";
    let roots = prism::default_roots(Path::new("."));
    let a = prism::namespace_root(&prism::with_prelude(base), &roots).expect("base namespace");
    let b = prism::namespace_root(&prism::with_prelude(with_test), &roots)
        .expect("with-test namespace");
    assert_eq!(a, b, "adding a test moved the production namespace root");

    // The test symbol is absent from the production build's symbols.
    let dump = prism::dump("core-hash", &prism::with_prelude(with_test)).expect("core-hash");
    assert!(
        !dump.contains("inc_adds_one"),
        "test symbol leaked into production core-hash"
    );
    assert!(
        dump.contains("inc"),
        "production symbol missing from core-hash"
    );
}

// 2: an integration test may not reach a private package declaration.
#[test]
fn integration_cannot_reach_private() {
    let dir = tempdir_project_with_bad_integration();
    let err = run_results(Some(&dir), &opts(), &Config::default())
        .expect_err("integration touching a private name must fail");
    let msg = format!("{err}");
    assert!(
        msg.contains("normalize") || msg.contains("does not export"),
        "expected a visibility diagnostic, got: {msg}"
    );
    let _ = std::fs::remove_dir_all(&dir);
}

// 6: invalid-signature and duplicate diagnostics are stable and declaration-local.
#[test]
fn invalid_signatures_and_duplicates_are_rejected() {
    let expect_msg = |file: &str, needle: &str| {
        let err = run_results(Some(&case(file)), &opts(), &Config::default())
            .expect_err(&format!("{file} must be rejected"));
        let msg = format!("{err}");
        assert!(
            msg.contains(needle),
            "for {file}: expected `{needle}` in `{msg}`"
        );
    };
    expect_msg("bad_param.pr", "must take no parameters");
    expect_msg("bad_return.pr", "must return Unit");
    expect_msg("bad_effect.pr", "unsupported test effect");
    expect_msg("duplicate.pr", "more than once");
    // A test named `main` would shadow the synthesized harness entry.
    expect_msg("bad_main_name.pr", "may not be named `main`");
}

// 7: pass, fail(), runtime fault, and explicit exit (nonzero and zero) are
// classified distinctly.
#[test]
fn outcomes_are_classified_distinctly() {
    let results =
        run_results(Some(&case("outcomes.pr")), &opts(), &Config::default()).expect("run outcomes");
    assert_eq!(
        status_of(&results, "outcomes::passes").status,
        TestStatus::Passed
    );
    assert_eq!(
        status_of(&results, "outcomes::fails").status,
        TestStatus::Failed
    );
    assert_eq!(
        status_of(&results, "outcomes::faults").status,
        TestStatus::Fault
    );
    // Any exit is a failure, even a zero code.
    assert_eq!(
        status_of(&results, "outcomes::exits_nonzero").status,
        TestStatus::Exit
    );
    assert_eq!(
        status_of(&results, "outcomes::exits_zero").status,
        TestStatus::Exit
    );
}

// 8: output is captured per test, shown on failure, and available on a pass.
#[test]
fn output_is_captured_per_test() {
    let results =
        run_results(Some(&case("outcomes.pr")), &opts(), &Config::default()).expect("run outcomes");
    let failing = status_of(&results, "outcomes::prints_then_fails");
    assert_eq!(failing.status, TestStatus::Failed);
    assert!(
        failing.output.contains("diagnostic context"),
        "captured failure output missing: {:?}",
        failing.output
    );
    let passing = status_of(&results, "outcomes::prints_and_passes");
    assert_eq!(passing.status, TestStatus::Passed);
    assert!(
        passing.output.contains("visible only with show-output"),
        "captured pass output missing: {:?}",
        passing.output
    );
}

// 10: a fresh world per test prevents state and output leakage between tests.
#[test]
fn fresh_world_isolates_state_and_output() {
    let results = run_results(Some(&case("isolation.pr")), &opts(), &Config::default())
        .expect("run isolation");
    let first = status_of(&results, "isolation::counts_to_three");
    let second = status_of(&results, "isolation::counts_to_one");
    assert_eq!(first.status, TestStatus::Passed, "state leaked: {first:?}");
    assert_eq!(
        second.status,
        TestStatus::Passed,
        "state leaked: {second:?}"
    );
    assert_eq!(first.output, "first", "output leaked into first: {first:?}");
    assert_eq!(
        second.output, "second",
        "output leaked into second: {second:?}"
    );
}

// 14 (single file) plus the user-`main` neutralization: a single-file program
// that defines `main` runs its test without the user main's output.
#[test]
fn single_file_with_user_main() {
    let results = run_results(Some(&case("with_main.pr")), &opts(), &Config::default())
        .expect("run single file");
    let r = status_of(&results, "with_main::helper_doubles");
    assert_eq!(r.status, TestStatus::Passed);
    assert!(
        !r.output.contains("user main must not run"),
        "user main leaked into a test run: {:?}",
        r.output
    );
}

// 9: filtering, exact matching, listing, and no-match behavior are stable.
#[test]
fn filter_exact_and_list_are_stable() {
    // Substring filter.
    let subset = run_results(
        Some(&case("outcomes.pr")),
        &filtered("exits"),
        &Config::default(),
    )
    .expect("filtered run");
    let mut names = ids(&subset);
    names.sort();
    assert_eq!(
        names,
        vec!["outcomes::exits_nonzero", "outcomes::exits_zero"]
    );

    // Exact match selects exactly one.
    let exact = TestOptions {
        filter: Some("outcomes::passes".to_string()),
        exact: true,
        ..TestOptions::default()
    };
    let one = run_results(Some(&case("outcomes.pr")), &exact, &Config::default()).expect("exact");
    assert_eq!(ids(&one), vec!["outcomes::passes"]);

    // No match yields an empty selection (a warning + success at the CLI level).
    let none = run_results(
        Some(&case("outcomes.pr")),
        &filtered("nope"),
        &Config::default(),
    )
    .expect("no-match run");
    assert!(none.is_empty());

    // Discovery order (the `--list` order) is sorted by logical ID.
    let listed = descriptors_for_file(&case("passing.pr"), &Config::default()).expect("list");
    let ordered: Vec<String> = listed.iter().map(|d| d.logical_id.clone()).collect();
    let mut sorted = ordered.clone();
    sorted.sort();
    assert_eq!(
        ordered, sorted,
        "discovery order is not sorted by logical id"
    );
}

// 12: repeated discovery produces byte-identical manifests, and the manifest
// round-trips through its codec without the diagnostic location.
#[test]
fn manifests_are_byte_identical_and_round_trip() {
    let a = descriptors_for_project(&project(), &Config::default()).expect("descriptors a");
    let b = descriptors_for_project(&project(), &Config::default()).expect("descriptors b");
    let bytes_a = encode_manifest(&a);
    let bytes_b = encode_manifest(&b);
    assert_eq!(
        bytes_a, bytes_b,
        "repeated manifests are not byte-identical"
    );

    let decoded = decode_manifest(&bytes_a).expect("decode");
    // The location is stripped from canonical bytes; every other field survives.
    for (orig, back) in a.iter().zip(&decoded) {
        assert_eq!(orig.logical_id, back.logical_id);
        assert_eq!(orig.definition_id, back.definition_id);
        assert_eq!(orig.test_core_digest, back.test_core_digest);
        assert!(back.diagnostic_location.is_empty());
    }
    // Re-encoding the decoded set is byte-identical.
    assert_eq!(encode_manifest(&decoded), bytes_a);

    // A truncated frame is rejected, not misread.
    assert!(decode_manifest(&bytes_a[..bytes_a.len() - 1]).is_err());
}

// 11: JSON events are canonical, byte-stable across runs, and free of absolute
// paths and timings. The golden fixture pins the exact bytes.
#[test]
fn json_events_are_canonical_and_stable() {
    let events = TestOptions {
        json: true,
        ..TestOptions::default()
    };
    let a = event_bytes(Some(&case("passing.pr")), &events, &Config::default()).expect("events a");
    let b = event_bytes(Some(&case("passing.pr")), &events, &Config::default()).expect("events b");
    assert_eq!(a, b, "event bytes differ across runs");

    let text = String::from_utf8(a.clone()).expect("utf8 events");
    assert!(
        !text.contains('/'),
        "event stream contains a path separator: {text}"
    );
    assert!(
        text.contains("\"schema\":\"prism-test-events-v1\""),
        "missing schema tag: {text}"
    );

    let fixture = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/prism_test/passing.events.ndjson");
    if std::env::var("PRISM_ACCEPT_TEST_FIXTURES").is_ok() {
        let tmp = fixture.with_extension("tmp");
        std::fs::write(&tmp, &a).unwrap();
        std::fs::rename(&tmp, &fixture).unwrap();
    }
    let golden = std::fs::read(&fixture).expect("read events fixture");
    assert_eq!(a, golden, "event bytes drifted from the golden fixture");
}

// The manifest version-compat fixture: golden bytes decode, and re-encoding is
// byte-identical; a wrong-schema and a truncated frame are rejected.
#[test]
fn manifest_golden_fixture_round_trips() {
    let descriptors = descriptors_for_project(&project(), &Config::default()).expect("descriptors");
    let bytes = encode_manifest(&descriptors);

    let fixture =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/prism_test/basic.manifest.bin");
    if std::env::var("PRISM_ACCEPT_TEST_FIXTURES").is_ok() {
        let tmp = fixture.with_extension("tmp");
        std::fs::write(&tmp, &bytes).unwrap();
        std::fs::rename(&tmp, &fixture).unwrap();
    }
    let golden = std::fs::read(&fixture).expect("read manifest fixture");
    assert_eq!(
        bytes, golden,
        "manifest bytes drifted from the golden fixture"
    );

    let decoded = decode_manifest(&golden).expect("golden decodes");
    assert_eq!(
        encode_manifest(&decoded),
        golden,
        "re-encode is not identical"
    );

    // A frame under a foreign scheme byte is rejected.
    let mut foreign = golden.clone();
    foreign[1] ^= 0xff;
    assert!(
        decode_manifest(&foreign).is_err(),
        "foreign scheme accepted"
    );
    // A truncated frame is rejected.
    assert!(decode_manifest(&golden[..golden.len() - 1]).is_err());
}

// 4 (calling): a production compile that references a test fails resolution
// exactly as if the test did not exist.
#[test]
fn production_cannot_call_a_test() {
    let src = prism::with_prelude("test fn my_test() = ()\nfn main() = my_test()\n");
    let roots = prism::default_roots(Path::new("."));
    let err = prism::check(&src)
        .err()
        .or_else(|| prism::check_validated_on_in(&src, &roots, &Config::default()).err());
    let msg = format!("{}", err.expect("production must reject a call to a test"));
    assert!(
        msg.contains("my_test") && (msg.contains("unbound") || msg.contains("Scope")),
        "expected an unbound-variable diagnostic, got: {msg}"
    );
}

// A malformed test body is a source error even in production (every file is
// parsed), but a well-formed test's type error surfaces only under `prism test`
// (production does not type-check the test supplement).
#[test]
fn parse_errors_surface_but_type_errors_are_deferred() {
    // A parse error inside a test surfaces in a production check.
    let bad_syntax = prism::with_prelude("test fn broken() = @#$ nope\nfn main() = ()\n");
    assert!(
        prism::check(&bad_syntax).is_err(),
        "parse error must surface in production"
    );

    // A well-formed test with a type error passes production check but is caught
    // by `prism test`.
    let type_error_src = "test fn type_error() = 1 + \"s\"\nfn main() = ()\n";
    let full = prism::with_prelude(type_error_src);
    assert!(
        prism::check(&full).is_ok(),
        "production check must not type-check a well-formed test body"
    );

    let file = write_temp("prism_test_typeerr", "src.pr", type_error_src);
    let err = run_results(Some(&file), &opts(), &Config::default())
        .expect_err("prism test must surface the test's type error");
    assert!(
        format!("{err}").contains("type mismatch"),
        "expected a type error"
    );
    let _ = std::fs::remove_file(&file);
}

// 5 (project path): a test-only edit to a project module leaves its checked
// module interface digest unchanged, so importers and the module cache are
// undisturbed.
#[test]
fn project_module_interface_is_test_neutral() {
    let base = "fn helper(n : Int) : Int = n + 1\npub fn api() : Int = helper(1)\n";
    let with_test = "fn helper(n : Int) : Int = n + 1\npub fn api() : Int = helper(1)\ntest fn t() = if helper(1) == 2 then () else fail()\n";
    let roots = prism::default_roots(Path::new("."));
    let a =
        prism::module_interface(base, &prism::with_prelude(base), &roots).expect("interface base");
    let b = prism::module_interface(with_test, &prism::with_prelude(with_test), &roots)
        .expect("interface with test");
    assert_eq!(
        a.digest, b.digest,
        "a test-only edit moved the module interface digest"
    );
}

// K0: `test` remains an ordinary identifier everywhere except the item-modifier
// position, so existing programs that name a function or binding `test` still parse
// and check.
#[test]
fn test_is_still_usable_as_an_identifier() {
    let src = prism::with_prelude(
        "fn test(n : Int) : Int = n + 1\nfn main() =\n  let test = 41\n  println(test + 1)\n",
    );
    assert!(
        prism::check(&src).is_ok(),
        "`test` must remain a valid identifier"
    );
}

// K0: a polymorphic result is an invalid test signature and is rejected at the
// declaration (E1998), not left to run tier-dependently.
#[test]
fn polymorphic_test_is_rejected() {
    let err = run_results(Some(&case("poly_return.pr")), &opts(), &Config::default())
        .expect_err("a polymorphic-result test must be rejected");
    assert!(
        format!("{err}").contains("must return Unit"),
        "expected a declaration-local return-type diagnostic, got: {err}"
    );
}

// K0: a test-only edit leaves the emitted (effect-lowered) artifact byte-identical,
// not merely the semantic hash. This is the emitted-artifact half of production
// neutrality, complementing the core-hash and interface checks above.
#[test]
fn test_only_edit_leaves_emitted_artifact_identical() {
    let base = "fn inc(n) = n + 1\nfn main() = println(inc(3))\n";
    let with_test =
        "fn inc(n) = n + 1\ntest fn t() = if inc(3) == 4 then () else fail()\nfn main() = println(inc(3))\n";
    let roots = prism::default_roots(Path::new("."));
    let cfg = Config::default();
    let lower = |src: &str| {
        prism::dump_on("lowered", &prism::with_prelude(src), &roots, &cfg).expect("lowered dump")
    };
    assert_eq!(
        lower(base),
        lower(with_test),
        "a test-only edit moved the emitted (lowered) artifact"
    );
}

// K0: a test in one module cannot be imported and called by another module's
// production code; the test is stripped from the module's interface, so the name
// does not resolve.
#[test]
fn test_cannot_be_imported_by_another_module() {
    let dir = std::env::temp_dir().join(format!("prism_test_ximport_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(
        dir.join("Lib.pr"),
        "pub fn ok() : Int = 1\ntest fn secret() = if ok() == 1 then () else fail()\n",
    )
    .unwrap();
    let main = prism::with_prelude("import Lib\nfn main() = Lib.secret()\n");
    let roots = prism::default_roots(&dir);
    let err = prism::check_validated_on_in(&main, &roots, &Config::default())
        .expect_err("a production import of another module's test must fail");
    assert!(
        format!("{err}").contains("secret") && format!("{err}").contains("does not export"),
        "expected an export/visibility diagnostic, got: {err}"
    );
    let _ = std::fs::remove_dir_all(&dir);
}

// K1: a dependency package's own tests are never discovered. The dependency is
// compiled and its public API consumed, but only the top project's tests run.
#[test]
fn dependency_tests_are_not_discovered() {
    let dir = tempdir_project_with_dependency();
    let app = dir.join("app");
    let descriptors = descriptors_for_project(&app, &Config::default()).expect("discover app");
    let names: Vec<String> = descriptors.iter().map(|d| d.logical_id.clone()).collect();
    assert!(
        names.iter().any(|n| n == "main::app_test"),
        "the app's own test is missing: {names:?}"
    );
    assert!(
        !names.iter().any(|n| n.contains("dep_internal_test")),
        "a dependency's test was discovered: {names:?}"
    );
    let _ = std::fs::remove_dir_all(&dir);
}

// K1: the manifest is byte-identical across checkout roots. The same project
// copied to two different absolute paths produces the same manifest bytes, since
// the diagnostic location is excluded from the canonical encoding.
#[test]
fn manifest_is_identical_across_checkout_roots() {
    let one = copy_project_to_temp("prism_test_root_one");
    let two = copy_project_to_temp("prism_test_root_two");
    let a = descriptors_for_project(&one, &Config::default()).expect("descriptors one");
    let b = descriptors_for_project(&two, &Config::default()).expect("descriptors two");
    // The diagnostic locations differ (different roots) but the canonical bytes do
    // not.
    assert_ne!(
        a[0].diagnostic_location, b[0].diagnostic_location,
        "the two copies should live at different paths"
    );
    assert_eq!(
        encode_manifest(&a),
        encode_manifest(&b),
        "manifest bytes differ across checkout roots"
    );
    let _ = std::fs::remove_dir_all(&one);
    let _ = std::fs::remove_dir_all(&two);
}

// K1: `prism test --list` renders both the human (one logical ID per line) and the
// JSON (`suite_started`/`test_started`/`suite_finished`) forms.
#[test]
fn list_output_has_human_and_json_forms() {
    let human = list_output(Some(&case("passing.pr")), &opts(), &Config::default()).expect("human");
    let lines: Vec<&str> = human.lines().collect();
    assert_eq!(
        lines,
        vec![
            "passing::double_of_three_is_six",
            "passing::double_of_zero_is_zero",
        ],
        "human list is not the sorted logical IDs"
    );

    let json_opts = TestOptions {
        json: true,
        ..TestOptions::default()
    };
    let json =
        list_output(Some(&case("passing.pr")), &json_opts, &Config::default()).expect("json");
    assert!(json.contains("\"event\":\"suite_started\""));
    assert!(json.contains("\"schema\":\"prism-test-events-v1\""));
    assert!(json.contains("\"event\":\"test_started\""));
    assert!(json.contains("\"event\":\"suite_finished\""));
    // Listing runs nothing, so every selected test is reported as skipped.
    assert!(json.contains("\"skipped\":2"));
    assert!(
        !json.contains("\"event\":\"test_passed\""),
        "listing must not run tests"
    );
}

// K2: exit status is nonzero exactly when compilation succeeds but a selected test
// fails, and `--fail-if-no-tests` turns an empty selection into a failure while the
// default keeps it a success.
#[test]
fn exit_status_reflects_failures_and_fail_if_no_tests() {
    let passing = write_temp("prism_test_exit_ok", "src.pr", "test fn a() = ()\n");
    let failing = write_temp(
        "prism_test_exit_bad",
        "src.pr",
        "test fn a() = ()\ntest fn b() = fail()\n",
    );

    assert!(
        test_cmd(Some(&passing), &opts(), &Config::default()).is_ok(),
        "all-passing run must exit zero"
    );
    assert!(
        test_cmd(Some(&failing), &opts(), &Config::default()).is_err(),
        "a failing test must exit nonzero"
    );

    // No match: a warning and success by default, a failure under the strict flag.
    let strict = TestOptions {
        filter: Some("nomatch".to_string()),
        fail_if_no_tests: true,
        ..TestOptions::default()
    };
    let lax = TestOptions {
        filter: Some("nomatch".to_string()),
        ..TestOptions::default()
    };
    assert!(
        test_cmd(Some(&passing), &lax, &Config::default()).is_ok(),
        "no match without the flag must exit zero"
    );
    assert!(
        test_cmd(Some(&passing), &strict, &Config::default()).is_err(),
        "no match under --fail-if-no-tests must exit nonzero"
    );

    let _ = std::fs::remove_file(&passing);
    let _ = std::fs::remove_file(&failing);
}

// K2: captured output is emitted for a passing test only under `--show-output`,
// through the JSON event path.
#[test]
fn show_output_gates_pass_output_in_events() {
    let hidden = TestOptions {
        filter: Some("prints_and_passes".to_string()),
        ..TestOptions::default()
    };
    let shown = TestOptions {
        show_output: true,
        ..hidden.clone()
    };
    let without = event_bytes(Some(&case("outcomes.pr")), &hidden, &Config::default())
        .expect("events hidden");
    let with =
        event_bytes(Some(&case("outcomes.pr")), &shown, &Config::default()).expect("events shown");
    let without = String::from_utf8(without).unwrap();
    let with = String::from_utf8(with).unwrap();
    assert!(
        !without.contains("\"event\":\"test_output\""),
        "a passing test leaked output without --show-output: {without}"
    );
    assert!(
        with.contains("\"event\":\"test_output\"")
            && with.contains("visible only with show-output"),
        "a passing test's output is missing under --show-output: {with}"
    );
}

// K2: the versioned structured-failure test ABI. A `Failure` round-trips through
// its wire codec and renders through the same event path the runner uses, so the
// later stdlib assertion layer has a stable bridge. Golden fixtures pin both the
// wire bytes and the event bytes; a foreign ABI is rejected.
#[test]
fn structured_failure_bridge_round_trips_through_events() {
    let failure = Failure {
        message: "values differ".to_string(),
        expected: Some("4".to_string()),
        actual: Some("5".to_string()),
        diff: Some("- 4\n+ 5".to_string()),
        site: Some("M.pr:12:3".to_string()),
        context: vec![
            "while checking addition".to_string(),
            "x = 2, y = 3".to_string(),
        ],
    };

    // The wire payload is canonical, byte-stable, and pinned by a golden fixture.
    let bytes = encode_failure(&failure);
    accept_or_check(&bytes, "structured_failure.bin");
    // Every field survives the round trip.
    assert_eq!(decode_failure(&bytes).expect("decode"), failure);

    // The decoded payload renders through the runner's event path.
    let events = structured_failure_events("M::structured", &decode_failure(&bytes).unwrap());
    accept_or_check(&events, "structured_failure.events.ndjson");
    let text = String::from_utf8(events).unwrap();
    for needle in [
        "\"event\":\"test_failed\"",
        "\"kind\":\"fail\"",
        "\"message\":\"values differ\"",
        "\"expected\":\"4\"",
        "\"actual\":\"5\"",
        "\"context\":[\"while checking addition\",\"x = 2, y = 3\"]",
        "\"site\":\"M.pr:12:3\"",
    ] {
        assert!(
            text.contains(needle),
            "structured event missing {needle}: {text}"
        );
    }

    // A foreign ABI byte is rejected rather than misread.
    let mut foreign = bytes;
    foreign[1] ^= 0xff;
    assert!(decode_failure(&foreign).is_err(), "foreign scheme accepted");
}

// Bless or check a golden fixture under `tests/fixtures/prism_test/`.
fn accept_or_check(bytes: &[u8], name: &str) {
    let fixture =
        Path::new(env!("CARGO_MANIFEST_DIR")).join(format!("tests/fixtures/prism_test/{name}"));
    if std::env::var("PRISM_ACCEPT_TEST_FIXTURES").is_ok() {
        let tmp = fixture.with_extension("tmp");
        std::fs::write(&tmp, bytes).unwrap();
        std::fs::rename(&tmp, &fixture).unwrap();
    }
    let golden = std::fs::read(&fixture).unwrap_or_else(|_| panic!("read fixture {name}"));
    assert_eq!(
        bytes,
        golden.as_slice(),
        "{name} drifted from its golden fixture"
    );
}

// Copy the committed basic project into a fresh temp directory, so a manifest can
// be discovered from a different absolute root.
fn copy_project_to_temp(prefix: &str) -> PathBuf {
    let dst = std::env::temp_dir().join(format!("{prefix}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dst);
    copy_dir(&project(), &dst);
    dst
}

fn copy_dir(src: &Path, dst: &Path) {
    std::fs::create_dir_all(dst).unwrap();
    for entry in std::fs::read_dir(src).unwrap() {
        let entry = entry.unwrap();
        let target = dst.join(entry.file_name());
        if entry.file_type().unwrap().is_dir() {
            copy_dir(&entry.path(), &target);
        } else {
            std::fs::copy(entry.path(), &target).unwrap();
        }
    }
}

// A two-package project: an `app` binary with its own test, depending on a path
// `dep` package that also declares a test. Only the app's test must be discovered.
fn tempdir_project_with_dependency() -> PathBuf {
    let dir = std::env::temp_dir().join(format!("prism_test_dep_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(dir.join("app/src")).unwrap();
    std::fs::create_dir_all(dir.join("dep/src")).unwrap();
    std::fs::write(
        dir.join("dep/prism.toml"),
        "[package]\nname = \"dep\"\n\n[bin]\nentry = \"src/Dep.pr\"\n",
    )
    .unwrap();
    std::fs::write(
        dir.join("dep/src/Dep.pr"),
        "pub fn helper() : Int = 7\ntest fn dep_internal_test() = if helper() == 7 then () else fail()\n",
    )
    .unwrap();
    std::fs::write(
        dir.join("app/prism.toml"),
        "[package]\nname = \"app\"\n\n[bin]\nentry = \"src/main.pr\"\n\n[dependencies]\ndep = { path = \"../dep\" }\n",
    )
    .unwrap();
    std::fs::write(
        dir.join("app/src/main.pr"),
        "import Dep\nfn main() = println(Dep.helper())\ntest fn app_test() = if Dep.helper() == 7 then () else fail()\n",
    )
    .unwrap();
    dir
}

fn write_temp(prefix: &str, name: &str, contents: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("{prefix}_{}", std::process::id()));
    let _ = std::fs::create_dir_all(&dir);
    let path = dir.join(name);
    std::fs::write(&path, contents).unwrap();
    path
}

// Build a scratch project whose integration test reaches a private name, so we
// can assert the visibility diagnostic. Kept out of the committed project so its
// mere presence does not fail the happy-path project run.
fn tempdir_project_with_bad_integration() -> PathBuf {
    let dir = std::env::temp_dir().join(format!("prism_test_badint_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(dir.join("src")).unwrap();
    std::fs::create_dir_all(dir.join("tests")).unwrap();
    std::fs::write(
        dir.join("prism.toml"),
        "[package]\nname = \"badint\"\n\n[bin]\nentry = \"src/main.pr\"\n",
    )
    .unwrap();
    std::fs::write(
        dir.join("src/main.pr"),
        "import Lib\nfn main() = println(Lib.pub_fn())\n",
    )
    .unwrap();
    std::fs::write(
        dir.join("src/Lib.pr"),
        "fn priv_fn() : Int = 1\npub fn pub_fn() : Int = priv_fn()\n",
    )
    .unwrap();
    std::fs::write(
        dir.join("tests/reach.pr"),
        "import Lib\ntest fn touches_private() = if Lib.priv_fn() == 1 then () else fail()\n",
    )
    .unwrap();
    dir
}
