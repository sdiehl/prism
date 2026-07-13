use std::fs;
use std::path::Path;
use std::process::Command;

const INTENTIONAL_DOC_VARIANTS: &[&str] = &[
    "effectful_traverse.pr",
    "effects.pr",
    "stable.pr",
    "ufcs.pr",
];

const WASM_VISIBLE_DOC_EXAMPLES: &[&str] = &[
    "docs/examples/app_stack.pr",
    "docs/examples/exceptions.pr",
    "docs/examples/streams.pr",
];

fn repo_path(path: &str) -> String {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join(path)
        .display()
        .to_string()
}

#[test]
fn mirrored_docs_examples_match_examples_unless_allowlisted() {
    let docs = Path::new(env!("CARGO_MANIFEST_DIR")).join("docs/examples");
    let examples = Path::new(env!("CARGO_MANIFEST_DIR")).join("examples");
    let mut drifted = Vec::new();

    for entry in fs::read_dir(&docs).expect("read docs/examples") {
        let path = entry.expect("read docs example").path();
        if path.extension().and_then(|ext| ext.to_str()) != Some("pr") {
            continue;
        }
        let name = path
            .file_name()
            .and_then(|name| name.to_str())
            .expect("utf8 docs example name");
        if INTENTIONAL_DOC_VARIANTS.contains(&name) {
            continue;
        }
        let example = examples.join(name);
        if !example.exists() {
            continue;
        }
        let docs_src = fs::read_to_string(&path).expect("read docs example source");
        let example_src = fs::read_to_string(&example).expect("read example source");
        if docs_src != example_src {
            drifted.push(format!("docs/examples/{name} != examples/{name}"));
        }
    }

    assert!(
        drifted.is_empty(),
        "same-name docs examples drifted from examples; either sync them or add an explicit curated-docs allowlist entry:\n{}",
        drifted.join("\n")
    );
}

#[test]
fn wasm_visible_doc_examples_run_without_polymorphic_print_errors() {
    for path in WASM_VISIBLE_DOC_EXAMPLES {
        let out = Command::new(env!("CARGO_BIN_EXE_prism"))
            .arg("run")
            .arg(repo_path(path))
            .output()
            .unwrap_or_else(|e| panic!("failed to run {path}: {e}"));
        let stderr = String::from_utf8_lossy(&out.stderr);
        let stdout = String::from_utf8_lossy(&out.stdout);
        assert!(
            out.status.success(),
            "{path} failed:\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
        assert!(
            !stdout.contains("cannot print a value of polymorphic type")
                && !stderr.contains("cannot print a value of polymorphic type"),
            "{path} hit the doc-runner polymorphic print diagnostic:\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
    }
}

// These examples cover unboxed products, OrNull, tensors, and usage contracts.
// Pin that each one still checks, so a spec snippet cannot silently rot ahead of
// the compiler.
const SPEC_ADDITION_EXAMPLES: &[&str] = &[
    "docs/examples/unboxed_products.pr",
    "docs/examples/ornull.pr",
    "docs/examples/tensor_intro.pr",
    "docs/examples/usage_contracts.pr",
];

#[test]
fn spec_addition_examples_check() {
    for path in SPEC_ADDITION_EXAMPLES {
        let out = Command::new(env!("CARGO_BIN_EXE_prism"))
            .arg("check")
            .arg(repo_path(path))
            .output()
            .unwrap_or_else(|e| panic!("failed to check {path}: {e}"));
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(out.status.success(), "{path} failed to check:\n{stderr}");
    }
}
