#[cfg(feature = "native")]
use std::collections::BTreeMap;
#[cfg(feature = "native")]
use std::fs;
#[cfg(all(feature = "native", unix))]
use std::os::unix::fs::PermissionsExt;
#[cfg(feature = "native")]
use std::path::Path;

#[cfg(feature = "native")]
use crate::codegen::rt::{runtime_profile_digest, RuntimeProfile};
#[cfg(feature = "native")]
use crate::core::{pass_fingerprint, LoweredCore, PassStage};
#[cfg(feature = "native")]
use crate::error::Error;
#[cfg(feature = "native")]
use crate::lineage::{FactOutcome, QueryKind};
#[cfg(feature = "native")]
use crate::resolve::Root;
#[cfg(feature = "native")]
use crate::store::disk::{atomic_write, resolve_store_path, Store, Written};
#[cfg(feature = "native")]
use crate::types::CtorInfo;

#[cfg(feature = "native")]
use super::identity::compiler_binary_fingerprint;
#[cfg(feature = "native")]
use super::input::{field, source_inputs_digest};
#[cfg(feature = "native")]
use super::session::QueryDecision;
#[cfg(feature = "native")]
use super::Config;

#[cfg(feature = "native")]
const LINKED_NATIVE_RAW_QUERY: &str = "linked-native.raw";
#[cfg(feature = "native")]
const LINKED_NATIVE_SEMANTIC_QUERY: &str = "linked-native.semantic";
#[cfg(feature = "native")]
const LLVM_BITCODE_QUERY: &str = "llvm-bitcode.semantic";
#[cfg(feature = "native")]
const NATIVE_OBJECT_QUERY: &str = "native-object";
#[cfg(feature = "native")]
const RUNTIME_OBJECT_QUERY: &str = "runtime-object";
// These `-vN` suffixes are cache-bust counters, not compat versions: each is
// hashed into its query key so a format change misses stale entries. No old
// version is ever read back, so a bumped counter (e.g. native-object at v2) has no
// backward-compatible read path is required.
#[cfg(feature = "native")]
const LINKED_NATIVE_RAW_SCHEMA: &str = "prism-linked-native-raw-query-v1";
#[cfg(feature = "native")]
const LINKED_NATIVE_SEMANTIC_SCHEMA: &str = "prism-linked-native-semantic-query-v1";
#[cfg(feature = "native")]
const LLVM_BITCODE_SCHEMA: &str = "prism-llvm-bitcode-query-v1";
#[cfg(feature = "native")]
const NATIVE_OBJECT_SCHEMA: &str = "prism-native-object-query-v2";
#[cfg(feature = "native")]
const RUNTIME_OBJECT_SCHEMA: &str = "prism-runtime-object-query-v1";
#[cfg(feature = "native")]
const IDENTITY_LINKED_RAW: &str = "linked-native-raw";
#[cfg(feature = "native")]
const IDENTITY_LINKED_SEMANTIC: &str = "linked-native-semantic";
#[cfg(feature = "native")]
const IDENTITY_WHOLE_BITCODE: &str = "whole-program-bitcode";
#[cfg(all(feature = "native", unix))]
const EXECUTABLE_MODE: u32 = 0o755;

/// Result of consulting or populating the durable native artifact query.
#[cfg(feature = "native")]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum NativeCacheStatus {
    /// Compiler artifact caching was disabled or incompatible with this request.
    #[default]
    Disabled,
    /// No query entry existed; compilation must proceed.
    Miss,
    /// An immutable cached binary was materialized without compiling or linking.
    Hit,
    /// Compilation completed and wrote a new query result.
    Write,
}

#[cfg(feature = "native")]
impl NativeCacheStatus {
    /// Stable spelling used by cache explanations.
    #[must_use]
    pub const fn label(self) -> &'static str {
        match self {
            Self::Disabled => "disabled",
            Self::Miss => "miss",
            Self::Hit => "hit",
            Self::Write => "write",
        }
    }
}

#[cfg(feature = "native")]
pub(super) struct NativeArtifactCache {
    store: Store,
    kind: &'static str,
    identity: String,
    key: String,
}

#[cfg(feature = "native")]
impl NativeArtifactCache {
    pub(super) fn for_build(
        src: &str,
        roots: &[Root],
        out: &Path,
        cfg: &Config,
    ) -> Result<Option<Self>, Error> {
        if !cfg.flags.compiler_cache || cfg.flags.store {
            return Ok(None);
        }
        let store = Store::open_or_create(resolve_store_path(cfg.flags.store_path.as_deref()))?;
        let key = linked_native_raw_key(src, roots, out, cfg)?;
        Ok(Some(Self {
            store,
            kind: LINKED_NATIVE_RAW_QUERY,
            identity: IDENTITY_LINKED_RAW.to_string(),
            key,
        }))
    }

    pub(super) fn for_semantic_build(
        core: &LoweredCore,
        ctors: &BTreeMap<String, CtorInfo>,
        native_kont_table: &str,
        out: &Path,
        cfg: &Config,
    ) -> Result<Option<Self>, Error> {
        if !cfg.flags.compiler_cache || cfg.flags.store {
            return Ok(None);
        }
        let store = Store::open_or_create(resolve_store_path(cfg.flags.store_path.as_deref()))?;
        let mut h = semantic_query_hasher(
            LINKED_NATIVE_SEMANTIC_SCHEMA,
            core,
            ctors,
            native_kont_table,
            cfg,
        )?;
        field(
            &mut h,
            runtime_profile_digest(RuntimeProfile::NativeBackend).as_bytes(),
        );
        field(&mut h, output_identity(out)?.as_os_str().as_encoded_bytes());
        Ok(Some(Self {
            store,
            kind: LINKED_NATIVE_SEMANTIC_QUERY,
            identity: IDENTITY_LINKED_SEMANTIC.to_string(),
            key: h.finalize().to_hex().to_string(),
        }))
    }

    pub(super) fn for_bitcode(
        core: &LoweredCore,
        ctors: &BTreeMap<String, CtorInfo>,
        native_kont_table: &str,
        cfg: &Config,
    ) -> Result<Option<Self>, Error> {
        if !cfg.flags.compiler_cache || cfg.flags.store {
            return Ok(None);
        }
        let store = Store::open_or_create(resolve_store_path(cfg.flags.store_path.as_deref()))?;
        let h = semantic_query_hasher(LLVM_BITCODE_SCHEMA, core, ctors, native_kont_table, cfg)?;
        Ok(Some(Self {
            store,
            kind: LLVM_BITCODE_QUERY,
            identity: IDENTITY_WHOLE_BITCODE.to_string(),
            key: h.finalize().to_hex().to_string(),
        }))
    }

    pub(super) fn for_native_object(
        name: &str,
        bytes: &[u8],
        cfg: &Config,
    ) -> Result<Option<Self>, Error> {
        Self::for_object(
            NATIVE_OBJECT_QUERY,
            NATIVE_OBJECT_SCHEMA,
            name,
            bytes,
            None,
            cfg,
        )
    }

    pub(super) fn for_runtime_object(
        name: &str,
        bytes: &[u8],
        profile: RuntimeProfile,
        cfg: &Config,
    ) -> Result<Option<Self>, Error> {
        Self::for_object(
            RUNTIME_OBJECT_QUERY,
            RUNTIME_OBJECT_SCHEMA,
            name,
            bytes,
            Some(profile),
            cfg,
        )
    }

    fn for_object(
        kind: &'static str,
        schema: &str,
        name: &str,
        bytes: &[u8],
        profile: Option<RuntimeProfile>,
        cfg: &Config,
    ) -> Result<Option<Self>, Error> {
        if !cfg.flags.compiler_cache || cfg.flags.store {
            return Ok(None);
        }
        let store = Store::open_or_create(resolve_store_path(cfg.flags.store_path.as_deref()))?;
        let mut hasher = blake3::Hasher::new();
        field(&mut hasher, schema.as_bytes());
        field(&mut hasher, compiler_binary_fingerprint()?.as_bytes());
        field(
            &mut hasher,
            cfg.artifact_identity_for("llvm").fingerprint().as_bytes(),
        );
        field(&mut hasher, name.as_bytes());
        if let Some(profile) = profile {
            field(&mut hasher, runtime_profile_digest(profile).as_bytes());
        }
        field(&mut hasher, bytes);
        Ok(Some(Self {
            store,
            kind,
            identity: format!("{kind}:{name}"),
            key: hasher.finalize().to_hex().to_string(),
        }))
    }

    pub(super) fn record_decision(
        &self,
        cfg: &Config,
        outcome: FactOutcome,
        output: Option<String>,
        reason: &str,
    ) {
        let kind = if matches!(
            self.kind,
            LINKED_NATIVE_RAW_QUERY | LINKED_NATIVE_SEMANTIC_QUERY
        ) {
            QueryKind::Link
        } else {
            QueryKind::Object
        };
        if let Some(session) = &cfg.session {
            session.record_decision(QueryDecision::new(
                kind,
                self.identity.clone(),
                self.key.clone(),
                outcome,
                output,
                (outcome != FactOutcome::Hit)
                    .then(|| reason.to_string())
                    .into_iter()
                    .collect(),
            ));
        }
    }

    pub(super) fn bind_output(&self, output_hash: &str) -> Result<(), Error> {
        self.store.put_query(self.kind, &self.key, output_hash)?;
        Ok(())
    }

    pub(super) fn materialize(&self, out: &Path) -> Result<Option<String>, Error> {
        self.materialize_file(out, true)
    }

    pub(super) fn materialize_file(
        &self,
        out: &Path,
        executable: bool,
    ) -> Result<Option<String>, Error> {
        let Some(output_hash) = self.store.get_query(self.kind, &self.key)? else {
            return Ok(None);
        };
        let bytes = self.store.get(&output_hash)?;
        let actual = blake3::hash(&bytes).to_hex().to_string();
        if actual != output_hash {
            return Err(Error::Io(std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                format!("cached artifact hashes to {actual}, expected {output_hash}"),
            )));
        }
        atomic_write(out, &bytes)?;
        if executable {
            make_executable(out)?;
        }
        Ok(Some(output_hash))
    }

    pub(super) fn store_result(&self, out: &Path) -> Result<String, Error> {
        let bytes = fs::read(out)?;
        let output_hash = blake3::hash(&bytes).to_hex().to_string();
        match self.store.put(&output_hash, &bytes)? {
            Written::New | Written::Hit => {}
        }
        self.store.put_query(self.kind, &self.key, &output_hash)?;
        Ok(output_hash)
    }
}

#[cfg(feature = "native")]
fn semantic_query_hasher(
    schema: &str,
    core: &LoweredCore,
    ctors: &BTreeMap<String, CtorInfo>,
    native_kont_table: &str,
    cfg: &Config,
) -> Result<blake3::Hasher, Error> {
    let mut h = blake3::Hasher::new();
    field(&mut h, schema.as_bytes());
    field(&mut h, compiler_binary_fingerprint()?.as_bytes());
    field(
        &mut h,
        cfg.artifact_identity_for("llvm").fingerprint().as_bytes(),
    );
    for stage in [PassStage::PreLowering, PassStage::Late] {
        field(
            &mut h,
            pass_fingerprint(
                cfg.opt,
                cfg.passes.as_ref(),
                stage,
                &cfg.disabled,
                &cfg.flags,
            )
            .as_bytes(),
        );
    }
    field(&mut h, &lowered_core_identity(core)?);
    field(&mut h, format!("{ctors:?}").as_bytes());
    field(&mut h, native_kont_table.as_bytes());
    Ok(h)
}

// A stable content encoding of the lowered term for the cache key, not its
// `Debug` rendering. `Debug` is a presentation format with no stability
// contract, so a derive or field-order change would silently move this key;
// `Core` serializes deterministically (ordered vectors and maps, no unordered
// collections), so equal terms always encode to equal bytes.
#[cfg(feature = "native")]
fn lowered_core_identity(core: &LoweredCore) -> Result<Vec<u8>, Error> {
    serde_json::to_vec(&core.0).map_err(|error| {
        Error::InternalInvariant(format!("serialize lowered core for cache key: {error}"))
    })
}

#[cfg(feature = "native")]
fn linked_native_raw_key(
    src: &str,
    roots: &[Root],
    out: &Path,
    cfg: &Config,
) -> Result<String, Error> {
    let mut h = blake3::Hasher::new();
    field(&mut h, LINKED_NATIVE_RAW_SCHEMA.as_bytes());
    field(&mut h, compiler_binary_fingerprint()?.as_bytes());
    field(
        &mut h,
        cfg.artifact_identity_for("llvm").fingerprint().as_bytes(),
    );
    field(
        &mut h,
        runtime_profile_digest(RuntimeProfile::NativeBackend).as_bytes(),
    );
    field(
        &mut h,
        source_inputs_digest(src, roots, cfg.flags.query_threads)?.as_bytes(),
    );
    // The build mode changes which declarations survive into the binary
    // (production strips `test fn`; test retains them) without entering the LLVM
    // artifact identity, so it must split this raw-source key: a test-mode build
    // must never be served a prior production, tests-stripped binary of the same
    // source, or the reverse. Mirrors the session front key's mode split.
    field(&mut h, &[u8::from(cfg.mode == super::BuildMode::Test)]);
    field(&mut h, output_identity(out)?.as_os_str().as_encoded_bytes());
    Ok(h.finalize().to_hex().to_string())
}

#[cfg(feature = "native")]
fn output_identity(out: &Path) -> Result<std::path::PathBuf, Error> {
    if out.is_absolute() {
        Ok(out.to_path_buf())
    } else {
        Ok(std::env::current_dir()?.join(out))
    }
}

#[cfg(all(feature = "native", unix))]
fn make_executable(path: &Path) -> Result<(), Error> {
    let mut permissions = fs::metadata(path)?.permissions();
    permissions.set_mode(EXECUTABLE_MODE);
    fs::set_permissions(path, permissions)?;
    Ok(())
}

#[cfg(all(feature = "native", not(unix)))]
fn make_executable(_path: &Path) -> Result<(), Error> {
    Ok(())
}
