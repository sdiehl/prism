//! A fast whole-store census: how many files each layer holds right now.
//!
//! The census opens every `store gc` run (the report the sweep is measured
//! against) and decides when a layer is so far past its budget that the sweep
//! retires it wholesale instead of walking it. It must therefore stay cheap on
//! exactly the stores that need it most, the ones holding millions of files:
//! on macOS each shard directory's entry count is one filesystem metadata read
//! (see `fast_entry_count`), and everywhere else the count reads directory
//! entries without ever opening or stating the files themselves.

use std::fs;
use std::io;
use std::path::Path;

#[cfg(target_os = "macos")]
use std::ffi::CString;
#[cfg(target_os = "macos")]
use std::os::raw::{c_char, c_int, c_void};
#[cfg(target_os = "macos")]
use std::os::unix::ffi::OsStrExt;

use super::{
    CERTS_DIR, DECISIONS_DIR, INDEX_DIR, META_DIR, OBJECTS_DIR, QUERIES_DIR, RETIRED_PREFIX,
    VERIFIED_DIR,
};

// The label the census aggregates every retired tree under; the trees'
// on-disk names are unique per rename and carry no reportable identity.
const RETIRED_LABEL: &str = "retired";

/// One layer's file population, as `store gc` reports it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LayerCensus {
    /// The layer as the user sees it: `objects`, `meta`, `queries/<kind>`,
    /// `index`, or `retired` for trees a bulk sweep has renamed aside.
    pub name: String,
    /// Files currently on disk under the layer.
    pub files: u64,
}

/// Per-layer file populations for a whole store.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct StoreCensus {
    /// One row per layer (and per query kind), in report order.
    pub layers: Vec<LayerCensus>,
}

impl StoreCensus {
    /// Total files across every layer.
    #[must_use]
    pub fn total(&self) -> u64 {
        self.layers.iter().map(|layer| layer.files).sum()
    }

    /// The population recorded for `name`, zero when the layer is absent.
    #[must_use]
    pub fn files(&self, name: &str) -> u64 {
        self.layers
            .iter()
            .find(|layer| layer.name == name)
            .map_or(0, |layer| layer.files)
    }
}

/// Count the files under every layer of the store rooted at `root`.
///
/// # Errors
/// Fails on a filesystem error other than a layer being absent.
pub(super) fn take(root: &Path) -> io::Result<StoreCensus> {
    let mut layers = Vec::new();
    for layer in [OBJECTS_DIR, META_DIR] {
        layers.push(LayerCensus {
            name: layer.to_string(),
            files: count_tree(&root.join(layer))?,
        });
    }
    let queries_root = root.join(QUERIES_DIR);
    for kind in child_dirs(&queries_root)? {
        layers.push(LayerCensus {
            name: format!("{QUERIES_DIR}/{kind}"),
            files: count_tree(&queries_root.join(&kind))?,
        });
    }
    for layer in [INDEX_DIR, DECISIONS_DIR, VERIFIED_DIR, CERTS_DIR] {
        layers.push(LayerCensus {
            name: layer.to_string(),
            files: count_tree(&root.join(layer))?,
        });
    }
    let mut retired = 0u64;
    for entry in fs::read_dir(root)? {
        let entry = entry?;
        let name = entry.file_name();
        let Some(name) = name.to_str() else {
            continue;
        };
        if name.starts_with(RETIRED_PREFIX) && entry.file_type()?.is_dir() {
            retired += count_tree(&entry.path())?;
        }
    }
    if retired > 0 {
        layers.push(LayerCensus {
            name: RETIRED_LABEL.to_string(),
            files: retired,
        });
    }
    Ok(StoreCensus { layers })
}

// Count the files under `dir`: fast-count each child directory plus the plain
// files at the root (layout stamps, index files). Depth one is the store's
// whole shape: every layer is either flat or one level of shard or kind
// directories. An absent directory reads as empty.
fn count_tree(dir: &Path) -> io::Result<u64> {
    let entries = match fs::read_dir(dir) {
        Ok(rd) => rd,
        Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(0),
        Err(e) => return Err(e),
    };
    let mut files = 0u64;
    for entry in entries {
        let entry = entry?;
        if entry.file_type()?.is_dir() {
            files += entry_count(&entry.path())?;
        } else {
            files += 1;
        }
    }
    Ok(files)
}

// The names of `dir`'s immediate subdirectories, empty when it is absent.
fn child_dirs(dir: &Path) -> io::Result<Vec<String>> {
    let entries = match fs::read_dir(dir) {
        Ok(rd) => rd,
        Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(Vec::new()),
        Err(e) => return Err(e),
    };
    let mut names = Vec::new();
    for entry in entries {
        let entry = entry?;
        if entry.file_type()?.is_dir() {
            if let Some(name) = entry.file_name().to_str() {
                names.push(name.to_string());
            }
        }
    }
    names.sort();
    Ok(names)
}

// One directory's entry count. The fast path asks the filesystem for the
// directory's own record; the portable path reads the directory. Neither
// opens or stats any file inside, and a directory that vanishes mid-census
// (a racing sweep) reads as empty.
fn entry_count(dir: &Path) -> io::Result<u64> {
    if let Some(count) = fast_entry_count(dir) {
        return Ok(count);
    }
    match fs::read_dir(dir) {
        Ok(rd) => Ok(rd.count() as u64),
        Err(e) if e.kind() == io::ErrorKind::NotFound => Ok(0),
        Err(e) => Err(e),
    }
}

// The `attrlist` request structure from the platform's `sys/attr.h`; the
// layout is fixed kernel ABI.
#[cfg(target_os = "macos")]
#[repr(C)]
struct AttrList {
    bitmapcount: u16,
    reserved: u16,
    commonattr: u32,
    volattr: u32,
    dirattr: u32,
    fileattr: u32,
    forkattr: u32,
}

#[cfg(target_os = "macos")]
const ATTR_BIT_MAP_COUNT: u16 = 5;
#[cfg(target_os = "macos")]
const ATTR_DIR_ENTRYCOUNT: u32 = 0x0000_0002;
// Returned buffer layout: a u32 total length, then the requested u32 count.
#[cfg(target_os = "macos")]
const ATTR_OUT_LEN: usize = 8;

// The store crate carries no FFI dependency, so the one platform call it
// wants is declared directly; libSystem is always linked.
#[cfg(target_os = "macos")]
#[allow(unsafe_code)]
extern "C" {
    fn getattrlist(
        path: *const c_char,
        attr_list: *mut c_void,
        attr_buf: *mut c_void,
        attr_buf_size: usize,
        options: u32,
    ) -> c_int;
}

// On macOS `getattrlist(ATTR_DIR_ENTRYCOUNT)` reads the entry count straight
// from the directory's catalog record: one call whether the directory holds
// ten entries or a million. Any failure falls back to the portable count.
#[cfg(target_os = "macos")]
#[allow(unsafe_code)]
fn fast_entry_count(dir: &Path) -> Option<u64> {
    let path = CString::new(dir.as_os_str().as_bytes()).ok()?;
    let mut list = AttrList {
        bitmapcount: ATTR_BIT_MAP_COUNT,
        reserved: 0,
        commonattr: 0,
        volattr: 0,
        dirattr: ATTR_DIR_ENTRYCOUNT,
        fileattr: 0,
        forkattr: 0,
    };
    let mut buf = [0u8; ATTR_OUT_LEN];
    // SAFETY: `path` is NUL-terminated by CString; the attribute list requests
    // exactly one u32 attribute, so the out-buffer (a u32 length header plus
    // the u32 payload) is large enough, and the kernel writes at most
    // `attr_buf_size` bytes into it.
    let rc = unsafe {
        getattrlist(
            path.as_ptr(),
            (&raw mut list).cast(),
            buf.as_mut_ptr().cast(),
            buf.len(),
            0,
        )
    };
    if rc != 0 {
        return None;
    }
    let used = u32::from_ne_bytes(buf[0..4].try_into().ok()?) as usize;
    if used < ATTR_OUT_LEN {
        return None;
    }
    Some(u64::from(u32::from_ne_bytes(buf[4..8].try_into().ok()?)))
}

// Everywhere else there is no catalog record to ask, so the caller always walks.
#[cfg(not(target_os = "macos"))]
const fn fast_entry_count(_dir: &Path) -> Option<u64> {
    None
}
