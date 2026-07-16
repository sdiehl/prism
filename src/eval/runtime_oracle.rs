#[cfg(feature = "native")]
use std::fs;
#[cfg(feature = "native")]
use std::path::PathBuf;
#[cfg(feature = "native")]
use std::process::{Command, Output, Stdio};
#[cfg(feature = "native")]
use std::sync::atomic::{AtomicU64, Ordering};
#[cfg(feature = "native")]
use std::time::{Duration, Instant};

#[cfg(feature = "native")]
use crate::codegen::rt::{write_libm_archive, write_runtime_for, RuntimeProfile};
#[cfg(feature = "native")]
use crate::codegen::MAIN_SYMBOL;

#[cfg(feature = "native")]
static ORACLE_SEQ: AtomicU64 = AtomicU64::new(0);

// Every oracle step is bounded: probing an arbitrary `PRISM_CC` gets a short
// leash, and the compile and run get a generous one, so a broken compiler
// wrapper or a wedged toolchain fails the test instead of hanging it forever.
#[cfg(feature = "native")]
const PROBE_TIMEOUT: Duration = Duration::from_secs(10);
#[cfg(feature = "native")]
const STEP_TIMEOUT: Duration = Duration::from_mins(2);
#[cfg(feature = "native")]
const POLL_INTERVAL: Duration = Duration::from_millis(50);

/// Run a command to completion or kill it at the deadline. `None` means the
/// command could not be spawned or overran its budget; the caller treats both
/// as the step failing.
#[cfg(feature = "native")]
fn output_with_timeout(cmd: &mut Command, timeout: Duration) -> Option<Output> {
    let mut child = cmd
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .ok()?;
    let start = Instant::now();
    loop {
        match child.try_wait() {
            Ok(Some(_)) => return child.wait_with_output().ok(),
            Ok(None) if start.elapsed() >= timeout => {
                let _ = child.kill();
                let _ = child.wait();
                return None;
            }
            Ok(None) => std::thread::sleep(POLL_INTERVAL),
            Err(_) => {
                let _ = child.kill();
                return None;
            }
        }
    }
}

/// Remove the oracle's scratch directory on every exit path. The assertions
/// below panic on a miscompiling or crashing oracle, and an owned guard is what
/// keeps those panics from leaking one temp directory per failure.
#[cfg(feature = "native")]
struct ScratchDir(PathBuf);

#[cfg(feature = "native")]
impl Drop for ScratchDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[cfg(feature = "native")]
pub(super) fn rt_oracle(body: &str) -> Option<Vec<String>> {
    let cc = std::env::var("PRISM_CC").unwrap_or_else(|_| env!("PRISM_BUILD_CC").into());
    let probed = output_with_timeout(Command::new(&cc).arg("--version"), PROBE_TIMEOUT)
        .is_some_and(|o| o.status.success());
    if !probed {
        eprintln!(
            "skipping runtime oracle: C compiler `{cc}` not found or unresponsive (set PRISM_CC)"
        );
        return None;
    }

    let stem = format!(
        "prism_oracle_{}_{}",
        std::process::id(),
        ORACLE_SEQ.fetch_add(1, Ordering::Relaxed)
    );
    let scratch = ScratchDir(std::env::temp_dir().join(&stem));
    let dir = &scratch.0;
    fs::create_dir_all(dir).unwrap();
    let src = dir.join(format!("{stem}.c"));
    let bin = dir.join(&stem);
    let rt_sources = write_runtime_for(dir, RuntimeProfile::HostOracle).unwrap();
    let libm_archive = write_libm_archive(dir).unwrap();
    fs::write(
        &src,
        format!(
            "#include <stdio.h>\n#include <string.h>\n\
             long prism_prim_rand(void);\n\
             long prism_str_lit(const char *, long);\n\
             long prism_big_of_str(long, int *);\n\
             long prism_big_show(long);\n\
             void print_str(long);\n\
             long {MAIN_SYMBOL}(void) {{\n{body}\nreturn 1;\n}}\n"
        ),
    )
    .unwrap();
    let comp = output_with_timeout(
        Command::new(&cc)
            .args(["-O0", "-w"])
            .arg(&src)
            .args(&rt_sources)
            .arg(&libm_archive)
            .arg("-o")
            .arg(&bin),
        STEP_TIMEOUT,
    )
    .expect("runtime oracle: C compile hung past its budget");
    assert!(
        comp.status.success(),
        "runtime oracle failed to compile:\n{}",
        String::from_utf8_lossy(&comp.stderr)
    );
    let run = output_with_timeout(&mut Command::new(&bin), STEP_TIMEOUT)
        .expect("runtime oracle: generated binary hung past its budget");
    assert!(
        run.status.success(),
        "runtime oracle crashed: {:?}",
        run.status
    );
    Some(
        String::from_utf8(run.stdout)
            .unwrap()
            .lines()
            .map(str::to_owned)
            .collect(),
    )
}

#[cfg(not(feature = "native"))]
pub(super) fn rt_oracle(_body: &str) -> Option<Vec<String>> {
    None
}
