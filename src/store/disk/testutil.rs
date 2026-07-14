//! Shared scratch-directory support for the disk-store unit tests.

use std::fs;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};

// Distinguishes this crate's store-test scratch dirs inside the system temp dir.
const SCRATCH_PREFIX: &str = "prism-store-test";

// A per-process counter so concurrent tests never collide on a scratch dir.
static NONCE: AtomicU64 = AtomicU64::new(0);

/// A unique scratch directory, removed on drop.
pub(crate) struct TempDir {
    pub(crate) path: PathBuf,
}

impl TempDir {
    pub(crate) fn new(tag: &str) -> Self {
        let mut path = std::env::temp_dir();
        let n = NONCE.fetch_add(1, Ordering::Relaxed);
        path.push(format!("{SCRATCH_PREFIX}-{tag}-{}-{n}", std::process::id()));
        fs::create_dir_all(&path).unwrap();
        Self { path }
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}
