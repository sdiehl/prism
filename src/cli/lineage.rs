//! Lineage inspection: render a sidecar, explain an output, verify one, and the
//! `prism diff` dispatch between source revisions and `.plineage` sidecars.

use std::ffi::OsStr;
use std::fs;
use std::path::{Path, PathBuf};
use std::process;

use crate::cli::{resolve_input, CmdResult};
use crate::error::Error;
use crate::lineage::{Variant, LINEAGE_EXTENSION, LINEAGE_FORMAT, LINEAGE_GRAPH_FORMAT};
use crate::store::cert::CertStatus;

// `prism diff OLD NEW`: one verb over two revisions or two lineage sidecars. Two
// `.plineage` sidecars diff by logical key (absorbing the old `lineage --diff`);
// two source revisions diff by Core hash. Mixing the two is a pointed error.
pub fn diff_cmd(old: &Path, new: &Path, json: bool, cfg: &crate::Config) -> CmdResult {
    match (is_lineage_sidecar(old), is_lineage_sidecar(new)) {
        (true, true) => lineage_diff_cmd(old, new, json),
        (false, false) => {
            let (old_full, _, old_name, _) = resolve_input(old, cfg)?;
            let (new_full, roots, new_name, _) = resolve_input(new, cfg)?;
            if json {
                let d = crate::source_diff_on(&old_full, &new_full, &roots, cfg)
                    .map_err(|e| (e, new_full, format!("{old_name} -> {new_name}")))?;
                let text = serde_json::to_string_pretty(&d)
                    .map_err(|e| (Error::Resolve(e.to_string()), String::new(), String::new()))?;
                println!("{text}");
            } else {
                let out = crate::diff_on(&old_full, &new_full, &roots, cfg)
                    .map_err(|e| (e, new_full, format!("{old_name} -> {new_name}")))?;
                print!("{out}");
            }
            Ok(())
        }
        _ => Err((
            Error::Resolve(
                "`prism diff` compares two source revisions or two `.plineage` sidecars; \
                 one argument is a lineage sidecar and the other is not"
                    .into(),
            ),
            String::new(),
            format!("{} -> {}", old.display(), new.display()),
        )),
    }
}

// A path is a lineage sidecar if it carries the `.plineage` extension or its own
// bytes declare a lineage format field. The format peek reads the path itself, not
// the sibling sidecar `read_lineage` would resolve, so a `.pr` source with a stray
// `.plineage` neighbor still diffs as source.
pub fn is_lineage_sidecar(path: &Path) -> bool {
    if path.extension().and_then(OsStr::to_str) == Some(LINEAGE_EXTENSION) {
        return true;
    }
    fs::read_to_string(path)
        .ok()
        .and_then(|text| serde_json::from_str::<serde_json::Value>(&text).ok())
        .and_then(|value| {
            value
                .get("format")
                .and_then(serde_json::Value::as_str)
                .map(str::to_owned)
        })
        .is_some_and(|format| format == LINEAGE_FORMAT || format == LINEAGE_GRAPH_FORMAT)
}

// `lineage verify SIDECAR [--certify OUT]`: rehash the recorded artifacts. A world
// timeline carries no on-disk artifacts to rehash; its ids are self-certifying
// content hashes, so verification is the structural graph invariants, and
// re-derivation (re-running the wasm) is not implemented. A `--certify` path mints a
// `lineage-verified` certificate over the sidecar digest on a clean rehash.
pub fn verify_rehash_cmd(file: &Path, certify: Option<&Path>) -> CmdResult {
    let graph = crate::lineage::read_lineage(file)
        .map_err(|e| (e, String::new(), file.display().to_string()))?;
    if graph.variant == Variant::World {
        if certify.is_some() {
            return Err((
                Error::Resolve(
                    "lineage verify --certify: a world timeline verifies structurally \
                     (self-certifying ids), not by a byte rehash, so it carries no \
                     lineage-verified certificate"
                        .into(),
                ),
                String::new(),
                file.display().to_string(),
            ));
        }
        let report = crate::lineage::verify_world(&graph)
            .map_err(|e| (e, String::new(), file.display().to_string()))?;
        println!(
            "world timelines verify structurally (self-certifying ids); \
             re-derivation is not implemented"
        );
        println!(
            "  well-formed: {} law(s), {} state(s), {} fork(s)",
            report.laws, report.states, report.forks
        );
        return Ok(());
    }
    let sidecar = crate::lineage::sidecar_of(file);
    let base = sidecar.parent().unwrap_or_else(|| Path::new("."));
    let report = crate::lineage::verify(&graph, base)
        .map_err(|e| (e, String::new(), file.display().to_string()))?;
    println!(
        "lineage verified: {} file(s) rehash to the recorded digests",
        report.checked
    );
    if report.skipped > 0 {
        println!(
            "  ({} append/removal write(s) recorded but not rehashable)",
            report.skipped
        );
    }
    if let Some(out) = certify {
        let bytes = fs::read(&sidecar)
            .map_err(|e| (Error::Io(e), String::new(), sidecar.display().to_string()))?;
        let cert = crate::lineage::mint_lineage_cert(&graph, &report, &bytes);
        write_certificate(out, &cert)?;
    }
    Ok(())
}

pub fn lineage_cmd(file: &Path, json: bool) -> CmdResult {
    let graph = crate::lineage::read_lineage(file)
        .map_err(|e| (e, String::new(), file.display().to_string()))?;
    if json {
        let text = graph.to_json_string().map_err(|e| {
            (
                Error::Resolve(e.to_string()),
                String::new(),
                file.display().to_string(),
            )
        })?;
        println!("{text}");
    } else {
        print!("{}", crate::lineage::render_human(&graph));
    }
    Ok(())
}

// `lineage why`: explain one output by walking the sidecar backward. Pure graph
// work, so it explains an old run even after its source files have moved.
pub fn why_output_cmd(sidecar: &Path, output: &str, json: bool) -> CmdResult {
    let graph = crate::lineage::read_lineage(sidecar)
        .map_err(|e| (e, String::new(), sidecar.display().to_string()))?;
    // A world timeline is walked by state hash, not by output selector; the same
    // `why` verb serves both, dispatching on the sidecar's variant.
    if graph.variant == Variant::World {
        return why_world_cmd(sidecar, &graph, output, json);
    }
    let explanation = crate::lineage::why_output(&graph, output)
        .map_err(|e| (e, String::new(), sidecar.display().to_string()))?;
    if json {
        // The terminal and JSON renderings consume the same answer object, so they
        // cannot drift.
        let text = serde_json::to_string_pretty(&explanation).map_err(|e| {
            (
                Error::Resolve(e.to_string()),
                String::new(),
                sidecar.display().to_string(),
            )
        })?;
        println!("{text}");
    } else {
        print!("{}", crate::lineage::render_explanation(&explanation));
    }
    Ok(())
}

// `lineage why <state-hash> world.plineage`: walk a world state back through its
// predecessors, the law it stepped under, and any fork points crossed. Pure graph
// work over self-certifying ids, so it explains an exported timeline offline.
fn why_world_cmd(
    sidecar: &Path,
    graph: &crate::lineage::LineageGraph,
    state: &str,
    json: bool,
) -> CmdResult {
    let explanation = crate::lineage::why_world_state(graph, state)
        .map_err(|e| (e, String::new(), sidecar.display().to_string()))?;
    if json {
        let text = serde_json::to_string_pretty(&explanation).map_err(|e| {
            (
                Error::Resolve(e.to_string()),
                String::new(),
                sidecar.display().to_string(),
            )
        })?;
        println!("{text}");
    } else {
        print!("{}", crate::lineage::render_world_explanation(&explanation));
    }
    Ok(())
}

// The `.plineage` arm of `prism diff`: align two sidecars by logical key. Exits
// nonzero when anything moved, was added, or was removed, so it can gate CI; a
// clean diff exits zero. Either way it prints a one-line verdict first.
fn lineage_diff_cmd(old: &Path, new: &Path, json: bool) -> CmdResult {
    let old_graph = crate::lineage::read_lineage(old)
        .map_err(|e| (e, String::new(), old.display().to_string()))?;
    let new_graph = crate::lineage::read_lineage(new)
        .map_err(|e| (e, String::new(), new.display().to_string()))?;
    let diff = crate::lineage::diff(&old_graph, &new_graph);
    if json {
        let text = serde_json::to_string_pretty(&diff).map_err(|e| {
            (
                Error::Resolve(e.to_string()),
                String::new(),
                "lineage".into(),
            )
        })?;
        println!("{text}");
    } else {
        print!("{}", crate::lineage::render_diff(&diff));
    }
    if diff.changed() {
        process::exit(1);
    }
    Ok(())
}

// `lineage verify SIDECAR --replay`: close the record/verify loop by replay. The
// program and trace are resolved from the sidecar's request and its sibling
// `.replay`; a fresh replay recomputes the trace and stdout digests, and the input
// files are rehashed from disk. Any disagreement is a named error. Shared by the
// `lineage verify` command and the check-world replay gate.
pub fn verify_run_sidecar(
    sidecar: &Path,
    cfg: &crate::Config,
) -> Result<crate::lineage::RunVerification, (Error, String, String)> {
    let path = crate::lineage::sidecar_of(sidecar);
    let graph = crate::lineage::read_lineage(&path)
        .map_err(|e| (e, String::new(), path.display().to_string()))?;
    let base = path
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
        .map_or_else(|| PathBuf::from("."), Path::to_path_buf);
    let entry = crate::lineage::run_entry(&graph)
        .map_err(|e| (e, String::new(), path.display().to_string()))?;
    let program = base.join(&entry);
    // Resolve the durable trace from the graph's own self-description (verifying its
    // digest), falling back to the sibling `.replay` only for pre-relation sidecars.
    let trace_path = crate::lineage::resolve_replay_file(&graph, &path, &base)
        .map_err(|e| (e, String::new(), path.display().to_string()))?;
    let trace_src = crate::cli::read(&trace_path).map_err(|e| {
        (
            e,
            String::new(),
            format!("{}: replay trace not found", trace_path.display()),
        )
    })?;
    let (full, roots, name, _) = resolve_input(&program, cfg)?;
    // Replay into a buffer: verification recomputes digests, it does not reproduce
    // the run's output to the terminal.
    let mut sink: Vec<u8> = Vec::new();
    let replayed = crate::replay_run_on(&full, &roots, &mut sink, &trace_src, cfg)
        .map_err(|e| (e, full, name))?;
    let digest = crate::provenance::trace_digest(&replayed.events);
    crate::lineage::verify_run_replay(&graph, &digest, replayed.term.as_bytes(), &base)
        .map_err(|e| (e, String::new(), path.display().to_string()))
}

pub fn verify_lineage_cmd(
    sidecar: &Path,
    certify: Option<&Path>,
    cfg: &crate::Config,
) -> CmdResult {
    let verified = verify_run_sidecar(sidecar, cfg)?;
    println!(
        "lineage verify: replay matches the sidecar ({} trace event(s), {} stdout byte(s), \
         {} input file(s) rehashed)",
        verified.trace_events, verified.stdout_bytes, verified.input_files
    );
    if verified.written_files > 0 || verified.skipped_writes > 0 {
        println!(
            "  ({} written file(s) rehashed, {} append/removal write(s) skipped)",
            verified.written_files, verified.skipped_writes
        );
    }
    // Only a passed replay reaches here, so a `--certify` path mints a
    // `replay-verified` certificate over the sidecar's own digest.
    if let Some(out) = certify {
        let path = crate::lineage::sidecar_of(sidecar);
        let graph = crate::lineage::read_lineage(&path)
            .map_err(|e| (e, String::new(), path.display().to_string()))?;
        let bytes = fs::read(&path)
            .map_err(|e| (Error::Io(e), String::new(), path.display().to_string()))?;
        let cert = crate::lineage::mint_replay_cert(&graph, &verified, &bytes)
            .map_err(|e| (e, String::new(), path.display().to_string()))?;
        write_certificate(out, &cert)?;
    }
    Ok(())
}

// Write a minted certificate and name where it landed. Certificates are a few
// hundred bytes; a filesystem error is the only failure.
fn write_certificate(out: &Path, cert: &[u8]) -> CmdResult {
    fs::write(out, cert).map_err(|e| (Error::Io(e), String::new(), out.display().to_string()))?;
    println!("  certificate written to {}", out.display());
    Ok(())
}

// `lineage check-cert CERT SIDECAR`: validate a minted certificate against the
// sidecar it names. Recomputes the sidecar digest and checks the certificate's
// bindings (scheme, subject digest, claim recognition) rather than re-running the
// verification, matching the parity-certificate discipline. A tampered sidecar, a
// foreign scheme, or a corrupt certificate is a named failure with a nonzero exit;
// an unrecognized claim is recognized-but-untrusted, also nonzero, never a silent
// pass; a recognized claim whose binding holds exits zero.
pub fn check_cert_cmd(cert: &Path, sidecar: &Path) -> CmdResult {
    let cert_bytes =
        fs::read(cert).map_err(|e| (Error::Io(e), String::new(), cert.display().to_string()))?;
    let sidecar_path = crate::lineage::sidecar_of(sidecar);
    let sidecar_bytes = fs::read(&sidecar_path).map_err(|e| {
        (
            Error::Io(e),
            String::new(),
            sidecar_path.display().to_string(),
        )
    })?;
    match crate::lineage::check_cert(&cert_bytes, &sidecar_bytes) {
        CertStatus::Verified(desc) => {
            println!("certificate ok: {desc}");
            Ok(())
        }
        CertStatus::Unverifiable(desc) => {
            eprintln!("certificate untrusted: {desc}");
            process::exit(1);
        }
        CertStatus::Failed(reason) => Err((
            Error::Resolve(format!("certificate check failed: {reason}")),
            String::new(),
            cert.display().to_string(),
        )),
        CertStatus::Absent => Err((
            Error::Resolve("certificate check failed: no certificate bytes".into()),
            String::new(),
            cert.display().to_string(),
        )),
    }
}
