//! End-to-end `prism lint` output and formatting-invariance tests.
//!
//! The rule that motivates the fixture is the codepoint-scan guard (`L0109`):
//! a recursion that indexes by codepoint re-walks the UTF-8 encoding on every
//! call, so the scan is quadratic in its input. `char_at`/`str_len` are the
//! codepoint family; `byte_at`/`byte_len` are the constant-time answer.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{self, Command};

const PRISM: &str = env!("CARGO_BIN_EXE_prism");
const FIXTURE: &str = "tests/fixtures/lint/codepoint_scan.pr";
const CODE_KEY: &str = "code";
const MESSAGE_KEY: &str = "message";
const FINDINGS_KEY: &str = "findings";

// Non-canonical sources ensure formatting moves finding offsets.
const MESSY_SCAN: &str =
    "fn sum_codes(s:String,i:Int):Int=if i==str_len(s) then 0 else char_at(s,i)+sum_codes(s,i+1)\n\
     fn main()=println(sum_codes(\"HI\",0))\n";
const MESSY_MAGIC: &str = "fn area(r:Int):Int=r*r*3\nfn main()=println(area(4))\n";
const CORPUS: &[(&str, &str)] = &[("scan.pr", MESSY_SCAN), ("magic.pr", MESSY_MAGIC)];

fn temp_dir(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("prism_lint_{name}_{}", process::id()));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    dir
}

// Compare stable rule/message pairs, independent of offsets and walk order.
fn projected_findings(stdout: &str) -> Vec<(String, String)> {
    let report: serde_json::Value =
        serde_json::from_str(stdout).unwrap_or_else(|e| panic!("lint json: {e}\n{stdout}"));
    let mut out: Vec<(String, String)> = report[FINDINGS_KEY]
        .as_array()
        .expect("findings array")
        .iter()
        .map(|f| {
            (
                f[CODE_KEY].as_str().expect("code").to_owned(),
                f[MESSAGE_KEY].as_str().expect("message").to_owned(),
            )
        })
        .collect();
    out.sort();
    out
}

fn lint_json(target: &Path) -> String {
    // Lint exits non-zero when it reports findings; the JSON is on stdout
    // regardless, so the status is expected, not asserted.
    let out = Command::new(PRISM)
        .arg("lint")
        .arg("--json")
        .arg(target)
        .output()
        .unwrap();
    String::from_utf8(out.stdout).expect("lint stdout is utf-8")
}

fn fmt_is_canonical(target: &Path) -> bool {
    Command::new(PRISM)
        .arg("fmt")
        .arg("--check")
        .arg(target)
        .output()
        .unwrap()
        .status
        .success()
}

/// Pin the machine output for the codepoint-scan fixture.
#[test]
fn codepoint_scan_fixture_machine_output() {
    let stdout = lint_json(Path::new(FIXTURE));
    insta::assert_snapshot!(stdout);
}

/// Reformatting may move offsets but must not change rules or messages.
#[test]
fn lint_findings_are_fmt_invariant() {
    let dir = temp_dir("fmt_invariant");
    for (name, src) in CORPUS {
        fs::write(dir.join(name), src).unwrap();
    }

    assert!(
        !fmt_is_canonical(&dir),
        "the corpus must start non-canonical for the check to have teeth"
    );
    let before = lint_json(&dir);
    assert!(
        !projected_findings(&before).is_empty(),
        "the corpus must produce findings to compare:\n{before}"
    );

    let fmt = Command::new(PRISM).arg("fmt").arg(&dir).output().unwrap();
    assert!(fmt.status.success(), "fmt failed: {fmt:?}");
    assert!(
        fmt_is_canonical(&dir),
        "fmt must leave the corpus canonical"
    );

    let after = lint_json(&dir);
    assert_ne!(
        before, after,
        "reformatting must move the byte offsets the report carries"
    );
    assert_eq!(
        projected_findings(&before),
        projected_findings(&after),
        "reformatting must not change which rules fire or what they report"
    );

    let _ = fs::remove_dir_all(&dir);
}
