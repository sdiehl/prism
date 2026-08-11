use std::fs;
use std::path::{Path, PathBuf};

use prism::{default_roots, interpret_io_on_with_args, with_prelude, Config};

const FIXTURE_DIR: &str = "tests/fixtures/frontend";

fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join(FIXTURE_DIR)
        .join(name)
}

fn decode(name: &str) -> String {
    let src = fs::read_to_string(fixture("tc_input_decode.pr")).expect("decoder harness");
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut output = Vec::new();
    interpret_io_on_with_args(
        &with_prelude(&src),
        &default_roots(root),
        &mut output,
        &mut &b""[..],
        &Config::from_env(),
        vec![fixture(name).display().to_string()],
    )
    .expect("run tc-input decoder");
    String::from_utf8(output).expect("utf8 decoder output")
}

#[test]
fn prism_decodes_tc_input_fixture() {
    assert_eq!(
        decode("program.tc-input.json"),
        "schema prism-tc-input-v1\ntypes 1\neffects 1\nclasses 1\ninstances 1\nfunctions 4\n"
    );
}

#[test]
fn prism_rejects_wrong_tc_input_schema() {
    assert!(decode("program.tc-input.mismatch.json")
        .starts_with("decode error: $.schema: unsupported schema"));
}
