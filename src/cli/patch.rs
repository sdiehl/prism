//! CLI and JSON-lines protocol for semantic patches.

use std::fs::{self, OpenOptions};
use std::io::{self, BufRead, Read, Write};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

use serde::{Deserialize, Serialize};
use serde_json::Value;

use crate::cli::{file_name, resolve_input, user_entry_path, user_source, CmdError, CmdResult};
use crate::error::Error;
use crate::patch::{PatchArtifact, PatchTarget, SurfaceTerm};
use crate::store::disk::{resolve_store_path, Store};
use crate::{BehaviorCase, BehaviorCorpus, PatchRefusal, StagedPatch};

pub const PATCH_PROTOCOL_FORMAT: &str = "prism-patch-protocol-v1";
const PATCH_COMMIT_FORMAT: &str = "prism-patch-commit-v1";
const PATCH_DISCARD_FORMAT: &str = "prism-patch-discard-v1";
const SOURCE_ADDRESS_DOMAIN: &[u8] = b"prism-patch-source-v1";
const STAGE_REF_DOMAIN: &[u8] = b"prism-patch-stage-ref-v1";
const TEMP_PREFIX: &str = ".prism-patch.";

static TEMP_COUNTER: AtomicU64 = AtomicU64::new(0);

struct PatchInput {
    entry_source: String,
    full_source: String,
    roots: Vec<crate::Root>,
    entry_path: PathBuf,
}

#[derive(Deserialize)]
struct BehaviorCorpusSource {
    format: String,
    cases: Vec<BehaviorCase>,
}

#[derive(Serialize)]
struct CommitReport<'a> {
    format: &'static str,
    stage: &'a str,
    path: String,
    report: &'a crate::DeltaReport,
}

#[derive(Serialize)]
struct DiscardReport<'a> {
    format: &'static str,
    discarded: &'a str,
}

#[derive(Debug, Deserialize)]
struct ProtocolRequest {
    protocol: String,
    #[serde(default)]
    id: Value,
    verb: String,
    #[serde(default)]
    target: Option<String>,
    #[serde(default)]
    replacement: Option<String>,
    #[serde(default)]
    patch: Option<PatchArtifact>,
    #[serde(default)]
    corpus: Option<BehaviorCorpus>,
}

#[derive(Serialize)]
struct ProtocolResponse {
    protocol: &'static str,
    id: Value,
    ok: bool,
    payload: Value,
}

pub fn fetch(file: &Path, target: &str, cfg: &crate::Config) -> CmdResult {
    emit(command_result(fetch_value(file, target, cfg)), file)
}

pub fn impact(file: &Path, target: &str, cfg: &crate::Config) -> CmdResult {
    emit(command_result(impact_value(file, target, cfg)), file)
}

pub fn create(file: &Path, target: &str, replacement: &Path, cfg: &crate::Config) -> CmdResult {
    emit(
        command_result(create_value(file, target, replacement, cfg)),
        file,
    )
}

pub fn apply(file: &Path, artifact: &Path, cfg: &crate::Config) -> CmdResult {
    let result = read_artifact(artifact).and_then(|patch| apply_value(file, patch, cfg));
    emit(command_result(result), file)
}

pub fn behavior(file: &Path, artifact: &Path, corpus: &Path, cfg: &crate::Config) -> CmdResult {
    let result = read_artifact(artifact).and_then(|patch| {
        read_behavior_corpus(corpus).and_then(|corpus| behavior_value(file, &patch, &corpus, cfg))
    });
    emit(command_result(result), file)
}

pub fn commit(file: &Path, cfg: &crate::Config) -> CmdResult {
    emit(command_result(commit_value(file, cfg)), file)
}

pub fn discard(file: &Path, cfg: &crate::Config) -> CmdResult {
    emit(command_result(discard_value(file, cfg)), file)
}

/// Serve the CLI-equivalent payloads as one JSON response per input line.
pub fn serve(file: &Path, cfg: &crate::Config) -> CmdResult {
    let stdin = io::stdin();
    let mut stdout = io::stdout().lock();
    for line in stdin.lock().lines() {
        let line = line.map_err(|error| cli_error(Error::Io(error), file))?;
        if line.trim().is_empty() {
            continue;
        }
        let response = match serde_json::from_str::<ProtocolRequest>(&line) {
            Ok(request) => handle_request(file, request, cfg),
            Err(error) => ProtocolResponse {
                protocol: PATCH_PROTOCOL_FORMAT,
                id: Value::Null,
                ok: false,
                payload: refusal_value(simple_refusal(
                    "invalid-request",
                    "decode-request",
                    error.to_string(),
                )),
            },
        };
        serde_json::to_writer(&mut stdout, &response)
            .map_err(|error| cli_error(Error::SemanticPatch(error.to_string()), file))?;
        stdout
            .write_all(b"\n")
            .and_then(|()| stdout.flush())
            .map_err(|error| cli_error(Error::Io(error), file))?;
    }
    Ok(())
}

fn handle_request(file: &Path, request: ProtocolRequest, cfg: &crate::Config) -> ProtocolResponse {
    let id = request.id;
    let result = if request.protocol == PATCH_PROTOCOL_FORMAT {
        match request.verb.as_str() {
            "fetch" => required(request.target, "target")
                .and_then(|target| fetch_value(file, &target, cfg)),
            "impact" => required(request.target, "target")
                .and_then(|target| impact_value(file, &target, cfg)),
            "create" => required(request.target, "target").and_then(|target| {
                required(request.replacement, "replacement")
                    .and_then(|replacement| create_source_value(file, &target, &replacement, cfg))
            }),
            "submit" | "apply" => {
                required(request.patch, "patch").and_then(|patch| apply_value(file, patch, cfg))
            }
            "behavior" => required(request.patch, "patch").and_then(|patch| {
                required(request.corpus, "corpus")
                    .and_then(|corpus| behavior_value(file, &patch, &corpus, cfg))
            }),
            "commit" => commit_value(file, cfg),
            "discard" => discard_value(file, cfg),
            other => Err(simple_refusal(
                "unknown-verb",
                "dispatch-request",
                format!("unknown patch protocol verb `{other}`"),
            )),
        }
    } else {
        Err(simple_refusal(
            "foreign-protocol",
            "decode-request",
            format!("unsupported patch protocol `{}`", request.protocol),
        ))
    };
    match result {
        Ok(payload) => ProtocolResponse {
            protocol: PATCH_PROTOCOL_FORMAT,
            id,
            ok: true,
            payload,
        },
        Err(refusal) => ProtocolResponse {
            protocol: PATCH_PROTOCOL_FORMAT,
            id,
            ok: false,
            payload: refusal_value(refusal),
        },
    }
}

fn fetch_value(file: &Path, target: &str, cfg: &crate::Config) -> Result<Value, PatchRefusal> {
    let input = patch_input(file, cfg)?;
    let report = crate::fetch_semantic_patch(
        &input.entry_source,
        &input.full_source,
        &input.roots,
        target,
    )?;
    serde_json::to_value(report).map_err(|error| json_refusal(&error))
}

fn impact_value(file: &Path, target: &str, cfg: &crate::Config) -> Result<Value, PatchRefusal> {
    let input = patch_input(file, cfg)?;
    let report = crate::impact_semantic_patch(&input.full_source, &input.roots, target)?;
    serde_json::to_value(report).map_err(|error| json_refusal(&error))
}

fn create_value(
    file: &Path,
    target: &str,
    replacement: &Path,
    cfg: &crate::Config,
) -> Result<Value, PatchRefusal> {
    let source = if replacement == Path::new("-") {
        let mut source = String::new();
        io::stdin()
            .read_to_string(&mut source)
            .map_err(|error| io_refusal(&error))?;
        source
    } else {
        fs::read_to_string(replacement).map_err(|error| io_refusal(&error))?
    };
    create_source_value(file, target, &source, cfg)
}

fn create_source_value(
    file: &Path,
    target: &str,
    replacement: &str,
    cfg: &crate::Config,
) -> Result<Value, PatchRefusal> {
    let input = patch_input(file, cfg)?;
    let fetch = crate::fetch_semantic_patch(
        &input.entry_source,
        &input.full_source,
        &input.roots,
        target,
    )?;
    let term = SurfaceTerm::from_source(replacement).map_err(|error| artifact_refusal(&error))?;
    if term.name != fetch.name {
        return Err(simple_refusal(
            "replacement-name",
            "create-patch",
            format!(
                "replacement declares `{}`, but target is `{}`",
                term.name, fetch.name
            ),
        ));
    }
    let patch = PatchArtifact::new(
        fetch.namespace,
        PatchTarget::new(fetch.core_hash),
        term,
        None,
    )
    .map_err(|error| artifact_refusal(&error))?;
    serde_json::to_value(patch).map_err(|error| json_refusal(&error))
}

fn apply_value(
    file: &Path,
    patch: PatchArtifact,
    cfg: &crate::Config,
) -> Result<Value, PatchRefusal> {
    let input = patch_input(file, cfg)?;
    let (report, result_source) = crate::apply_semantic_patch(
        &input.entry_source,
        &input.full_source,
        &input.roots,
        &patch,
    )?;
    let stage = StagedPatch::new(
        source_digest(&input.entry_source),
        patch,
        result_source,
        report.clone(),
    )?;
    let store = patch_store(cfg)?;
    persist_json(&store, &report.digest, &report)?;
    persist_json(&store, &stage.digest, &stage)?;
    store
        .set_ref(&stage_ref(&input.entry_path), &stage.digest)
        .map_err(|error| io_refusal(&error))?;
    serde_json::to_value(report).map_err(|error| json_refusal(&error))
}

fn behavior_value(
    file: &Path,
    patch: &PatchArtifact,
    corpus: &BehaviorCorpus,
    cfg: &crate::Config,
) -> Result<Value, PatchRefusal> {
    let input = patch_input(file, cfg)?;
    let receipt = crate::verify_semantic_patch_behavior(
        &input.entry_source,
        &input.full_source,
        &input.roots,
        patch,
        corpus,
        cfg,
    )?;
    let store = patch_store(cfg)?;
    persist_json(&store, &corpus.digest, corpus)?;
    persist_json(&store, &receipt.digest, &receipt)?;
    serde_json::to_value(receipt).map_err(|error| json_refusal(&error))
}

fn commit_value(file: &Path, cfg: &crate::Config) -> Result<Value, PatchRefusal> {
    let input = patch_input(file, cfg)?;
    let store = patch_store(cfg)?;
    let reference = stage_ref(&input.entry_path);
    let stage_hash = store
        .get_ref(&reference)
        .map_err(|error| io_refusal(&error))?
        .ok_or_else(|| {
            simple_refusal(
                "no-staged-patch",
                "load-stage",
                format!("no patch is staged for {}", input.entry_path.display()),
            )
        })?;
    let bytes = store.get(&stage_hash).map_err(|error| io_refusal(&error))?;
    let stage: StagedPatch =
        serde_json::from_slice(&bytes).map_err(|error| json_refusal(&error))?;
    stage.validate()?;
    let current_digest = source_digest(&input.entry_source);
    if current_digest != stage.source_digest {
        return Err(simple_refusal(
            "stale-source",
            "commit-source",
            "the source changed after the patch was judged; fetch and apply again",
        ));
    }
    let (report, result_source) = crate::apply_semantic_patch(
        &input.entry_source,
        &input.full_source,
        &input.roots,
        &stage.patch,
    )?;
    if report != stage.report || result_source != stage.result_source {
        return Err(simple_refusal(
            "non-deterministic-judgment",
            "rejudge-stage",
            "re-running the staged patch did not reproduce byte-identical evidence",
        ));
    }

    // Populate the cache from the already-judged source before publishing the
    // file. A coherence refusal therefore leaves the source untouched.
    let prefix_len = crate::error::SourceMap::new(&input.full_source).prelude_len();
    let mut result_full = String::with_capacity(prefix_len + result_source.len());
    result_full.push_str(&input.full_source[..prefix_len]);
    result_full.push_str(&result_source);
    crate::commit_to_store(&result_full, &input.roots, cfg)
        .map_err(|error| compiler_refusal("commit-store", &error))?;
    atomic_write(&input.entry_path, result_source.as_bytes())
        .map_err(|error| io_refusal(&error))?;
    store
        .remove_ref(&reference)
        .map_err(|error| io_refusal(&error))?;
    let commit = CommitReport {
        format: PATCH_COMMIT_FORMAT,
        stage: &stage.digest,
        path: input.entry_path.display().to_string(),
        report: &report,
    };
    serde_json::to_value(commit).map_err(|error| json_refusal(&error))
}

fn discard_value(file: &Path, cfg: &crate::Config) -> Result<Value, PatchRefusal> {
    let input = patch_input(file, cfg)?;
    let store = patch_store(cfg)?;
    let reference = stage_ref(&input.entry_path);
    let discarded = store
        .get_ref(&reference)
        .map_err(|error| io_refusal(&error))?
        .ok_or_else(|| {
            simple_refusal(
                "no-staged-patch",
                "discard-stage",
                format!("no patch is staged for {}", input.entry_path.display()),
            )
        })?;
    store
        .remove_ref(&reference)
        .map_err(|error| io_refusal(&error))?;
    serde_json::to_value(DiscardReport {
        format: PATCH_DISCARD_FORMAT,
        discarded: &discarded,
    })
    .map_err(|error| json_refusal(&error))
}

fn patch_input(file: &Path, cfg: &crate::Config) -> Result<PatchInput, PatchRefusal> {
    let entry_source = user_source(file).map_err(|error| cmd_refusal(&error))?;
    let entry_path = user_entry_path(file).map_err(|error| cmd_refusal(&error))?;
    let (full_source, roots, _, _) =
        resolve_input(file, cfg).map_err(|error| cmd_refusal(&error))?;
    Ok(PatchInput {
        entry_source,
        full_source,
        roots,
        entry_path,
    })
}

fn patch_store(cfg: &crate::Config) -> Result<Store, PatchRefusal> {
    Store::open_or_create(resolve_store_path(cfg.flags.store_path.as_deref()))
        .map_err(|error| io_refusal(&error))
}

fn read_artifact(path: &Path) -> Result<PatchArtifact, PatchRefusal> {
    let bytes = if path == Path::new("-") {
        let mut bytes = Vec::new();
        io::stdin()
            .read_to_end(&mut bytes)
            .map_err(|error| io_refusal(&error))?;
        bytes
    } else {
        fs::read(path).map_err(|error| io_refusal(&error))?
    };
    let artifact: PatchArtifact =
        serde_json::from_slice(&bytes).map_err(|error| json_refusal(&error))?;
    artifact
        .validate()
        .map_err(|error| artifact_refusal(&error))?;
    Ok(artifact)
}

fn read_behavior_corpus(path: &Path) -> Result<BehaviorCorpus, PatchRefusal> {
    let bytes = fs::read(path).map_err(|error| io_refusal(&error))?;
    let value: Value = serde_json::from_slice(&bytes).map_err(|error| json_refusal(&error))?;
    if value.get("digest").is_some() {
        let corpus: BehaviorCorpus =
            serde_json::from_value(value).map_err(|error| json_refusal(&error))?;
        corpus.validate()?;
        return Ok(corpus);
    }
    let source: BehaviorCorpusSource =
        serde_json::from_value(value).map_err(|error| json_refusal(&error))?;
    if source.format != crate::PATCH_BEHAVIOR_CORPUS_FORMAT {
        return Err(simple_refusal(
            "foreign-behavior-corpus",
            "decode-behavior-corpus",
            format!("unsupported behavior corpus format `{}`", source.format),
        ));
    }
    BehaviorCorpus::new(source.cases)
}

fn persist_json<T: Serialize>(store: &Store, digest: &str, value: &T) -> Result<(), PatchRefusal> {
    let bytes = serde_json::to_vec(value).map_err(|error| json_refusal(&error))?;
    store
        .put(digest, &bytes)
        .map_err(|error| io_refusal(&error))?;
    Ok(())
}

fn source_digest(source: &str) -> String {
    address(SOURCE_ADDRESS_DOMAIN, source.as_bytes())
}

fn stage_ref(path: &Path) -> String {
    let canonical = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());
    format!(
        "patch-stage-{}",
        address(STAGE_REF_DOMAIN, canonical.to_string_lossy().as_bytes())
    )
}

fn address(domain: &[u8], payload: &[u8]) -> String {
    let mut hasher = blake3::Hasher::new();
    for field in [domain, payload] {
        hasher.update(&(field.len() as u64).to_le_bytes());
        hasher.update(field);
    }
    hasher.finalize().to_hex().to_string()
}

fn atomic_write(path: &Path, bytes: &[u8]) -> io::Result<()> {
    let parent = path.parent().unwrap_or_else(|| Path::new("."));
    fs::create_dir_all(parent)?;
    let name = path
        .file_name()
        .and_then(|name| name.to_str())
        .unwrap_or("source.pr");
    for _ in 0..32 {
        let id = TEMP_COUNTER.fetch_add(1, Ordering::Relaxed);
        let temp = parent.join(format!("{TEMP_PREFIX}{name}.{}.{}", std::process::id(), id));
        let mut file = match OpenOptions::new().write(true).create_new(true).open(&temp) {
            Ok(file) => file,
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => continue,
            Err(error) => return Err(error),
        };
        if let Err(error) = file.write_all(bytes).and_then(|()| file.sync_all()) {
            let _ = fs::remove_file(&temp);
            return Err(error);
        }
        drop(file);
        if let Err(error) = fs::rename(&temp, path) {
            let _ = fs::remove_file(&temp);
            return Err(error);
        }
        return Ok(());
    }
    Err(io::Error::new(
        io::ErrorKind::AlreadyExists,
        "could not allocate a unique patch commit temp file",
    ))
}

fn emit(result: Result<Value, CmdError>, file: &Path) -> CmdResult {
    match result {
        Ok(value) => {
            println!(
                "{}",
                serde_json::to_string(&value)
                    .map_err(|error| cli_error(Error::SemanticPatch(error.to_string()), file))?
            );
            Ok(())
        }
        Err(error) => Err(error),
    }
}

fn command_result(result: Result<Value, PatchRefusal>) -> Result<Value, CmdError> {
    result.map_err(|refusal| {
        let json = refusal
            .to_json()
            .unwrap_or_else(|error| format!("{{\"message\":\"{error}\"}}"));
        (
            Error::SemanticPatch(json),
            String::new(),
            "patch".to_string(),
        )
    })
}

fn required<T>(value: Option<T>, field: &str) -> Result<T, PatchRefusal> {
    value.ok_or_else(|| {
        simple_refusal(
            "missing-field",
            "decode-request",
            format!("patch protocol request is missing `{field}`"),
        )
    })
}

fn refusal_value(refusal: PatchRefusal) -> Value {
    serde_json::to_value(refusal).expect("closed patch refusal protocol always serializes")
}

fn simple_refusal(code: &str, judgment: &str, message: impl Into<String>) -> PatchRefusal {
    PatchRefusal::new(code, judgment, message)
}

fn artifact_refusal(error: &crate::patch::PatchArtifactError) -> PatchRefusal {
    simple_refusal("invalid-artifact", "decode-artifact", error.to_string())
}

fn compiler_refusal(judgment: &str, error: &Error) -> PatchRefusal {
    simple_refusal(error.code().as_str(), judgment, error.to_string())
}

fn json_refusal(error: &serde_json::Error) -> PatchRefusal {
    simple_refusal("invalid-json", "decode-json", error.to_string())
}

fn io_refusal(error: &io::Error) -> PatchRefusal {
    simple_refusal("io", "patch-io", error.to_string())
}

fn cmd_refusal(error: &CmdError) -> PatchRefusal {
    simple_refusal(
        error.0.code().as_str(),
        "resolve-input",
        error.0.to_string(),
    )
}

fn cli_error(error: Error, file: &Path) -> CmdError {
    (error, String::new(), file_name(file))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn protocol_request_refuses_a_foreign_version() {
        let request = ProtocolRequest {
            protocol: "prism-patch-protocol-v0".to_string(),
            id: serde_json::json!(7),
            verb: "fetch".to_string(),
            target: Some("main".to_string()),
            replacement: None,
            patch: None,
            corpus: None,
        };
        let response = handle_request(Path::new("missing.pr"), request, &crate::Config::default());
        assert!(!response.ok);
        assert_eq!(response.id, serde_json::json!(7));
        assert_eq!(response.payload["code"], "foreign-protocol");
    }
}
