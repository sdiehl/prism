#[cfg(feature = "native")]
use std::fs;
#[cfg(feature = "native")]
use std::process::Command;
#[cfg(feature = "native")]
use std::sync::atomic::{AtomicU64, Ordering};

#[cfg(feature = "native")]
use crate::codegen::rt::{write_libm_archive, write_runtime_for, RuntimeProfile};

#[cfg(feature = "native")]
static ORACLE_SEQ: AtomicU64 = AtomicU64::new(0);

#[cfg(feature = "native")]
pub(super) fn rt_oracle(body: &str) -> Option<Vec<String>> {
    let cc = std::env::var("PRISM_CC").unwrap_or_else(|_| env!("PRISM_BUILD_CC").into());
    if !Command::new(&cc)
        .arg("--version")
        .output()
        .is_ok_and(|o| o.status.success())
    {
        eprintln!("skipping runtime oracle: C compiler `{cc}` not found (set PRISM_CC)");
        return None;
    }

    let stem = format!(
        "prism_oracle_{}_{}",
        std::process::id(),
        ORACLE_SEQ.fetch_add(1, Ordering::Relaxed)
    );
    let dir = std::env::temp_dir().join(&stem);
    fs::create_dir_all(&dir).unwrap();
    let src = dir.join(format!("{stem}.c"));
    let bin = dir.join(&stem);
    let rt_sources = write_runtime_for(&dir, RuntimeProfile::HostOracle).unwrap();
    let libm_archive = write_libm_archive(&dir).unwrap();
    fs::write(
        &src,
        format!(
            "#include <stdio.h>\n#include <string.h>\n\
             long prism_prim_rand(void);\n\
             long prism_str_lit(const char *, long);\n\
             long prism_big_of_str(long, int *);\n\
             long prism_big_show(long);\n\
             void print_str(long);\n\
             long prism_main(void) {{\n{body}\nreturn 1;\n}}\n"
        ),
    )
    .unwrap();
    let comp = Command::new(&cc)
        .args(["-O0", "-w"])
        .arg(&src)
        .args(&rt_sources)
        .arg(&libm_archive)
        .arg("-o")
        .arg(&bin)
        .output()
        .unwrap();
    assert!(
        comp.status.success(),
        "runtime oracle failed to compile:\n{}",
        String::from_utf8_lossy(&comp.stderr)
    );
    let run = Command::new(&bin).output().unwrap();
    let _ = fs::remove_dir_all(&dir);
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
