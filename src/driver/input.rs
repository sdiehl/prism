use crate::error::Error;
use crate::lex::lex;
use crate::parse::parse;
use crate::resolve::{load, Module, Root};
use crate::syntax::ast::Program;

use super::scheduler::QueryScheduler;

pub(super) struct LoadedFrontInputs {
    pub(super) root: Program,
    pub(super) modules: Vec<Module>,
    pub(super) raw_digest: String,
}

/// Parse and load the exact raw input closure while computing its trust-boundary
/// digest. A session miss can consume the retained programs directly instead of
/// parsing and loading the same closure again.
pub(super) fn load_front_inputs(
    src: &str,
    roots: &[Root],
    query_threads: usize,
) -> Result<LoadedFrontInputs, Error> {
    let root = parse(src)?.program;
    let modules = load(&root, roots)?;
    let mut raw = blake3::Hasher::new();
    field(&mut raw, src.as_bytes());
    let module_digests = QueryScheduler::new(query_threads).map_ordered(&modules, |module| {
        let mut hasher = blake3::Hasher::new();
        field(&mut hasher, module.path.join(".").as_bytes());
        field(&mut hasher, module.source.as_bytes());
        hasher.finalize()
    });
    for digest in module_digests {
        field(&mut raw, digest.as_bytes());
    }
    hash_root_identities(&mut raw, roots);
    Ok(LoadedFrontInputs {
        root,
        modules,
        raw_digest: raw.finalize().to_hex().to_string(),
    })
}

/// Digest the raw root source, every module selected by actual first-hit import
/// resolution, and identified source-bundle roots. This deliberately does not use
/// Prism Core hashes: compiler-query invalidation must remain independent of the
/// semantic hasher it helps verify.
pub(super) fn source_inputs_digest(
    src: &str,
    roots: &[Root],
    query_threads: usize,
) -> Result<String, Error> {
    Ok(load_front_inputs(src, roots, query_threads)?.raw_digest)
}

pub(super) fn semantic_inputs_digest(
    src: &str,
    roots: &[Root],
    query_threads: usize,
) -> Result<String, Error> {
    let inputs = load_front_inputs(src, roots, query_threads)?;
    semantic_loaded_inputs_digest(src, &inputs.modules, roots, query_threads)
}

pub(super) fn semantic_loaded_inputs_digest(
    src: &str,
    modules: &[Module],
    roots: &[Root],
    query_threads: usize,
) -> Result<String, Error> {
    let mut semantic = blake3::Hasher::new();
    field(&mut semantic, b"prism-semantic-source-input-v1");
    hash_tokens(&mut semantic, src)?;
    let module_digests = QueryScheduler::new(query_threads).map_ordered(modules, |module| {
        let mut hasher = blake3::Hasher::new();
        field(&mut hasher, module.path.join(".").as_bytes());
        hash_tokens(&mut hasher, &module.source).map(|()| hasher.finalize())
    });
    for digest in module_digests {
        field(&mut semantic, digest?.as_bytes());
    }
    hash_root_identities(&mut semantic, roots);
    Ok(semantic.finalize().to_hex().to_string())
}

fn hash_root_identities(hasher: &mut blake3::Hasher, roots: &[Root]) {
    for root in roots {
        if let Some(identity) = root.source_bundle_identity() {
            field(hasher, identity.descriptor().as_bytes());
        }
    }
}

pub(super) fn semantic_source_digest(src: &str) -> Result<String, Error> {
    let mut hasher = blake3::Hasher::new();
    hash_tokens(&mut hasher, src)?;
    Ok(hasher.finalize().to_hex().to_string())
}

fn hash_tokens(hasher: &mut blake3::Hasher, src: &str) -> Result<(), Error> {
    let (tokens, _) = lex(src)?;
    for (_, token, _) in tokens {
        field(hasher, format!("{token:?}").as_bytes());
    }
    Ok(())
}

pub(super) fn field(h: &mut blake3::Hasher, bytes: &[u8]) {
    h.update(&(bytes.len() as u64).to_le_bytes());
    h.update(bytes);
}

#[cfg(test)]
mod tests {
    use crate::resolve::Root;

    use super::{semantic_inputs_digest, source_inputs_digest};

    const SEQUENTIAL_QUERY_THREADS: usize = 1;
    const PARALLEL_QUERY_THREADS: usize = 4;

    #[test]
    fn source_identity_is_worker_count_independent() {
        let roots = [Root::Embedded(crate::stdlib::STDLIB)];
        let src = "import Data.List\nimport Data.Map\n";
        let sequential = source_inputs_digest(src, &roots, SEQUENTIAL_QUERY_THREADS).unwrap();
        let parallel = source_inputs_digest(src, &roots, PARALLEL_QUERY_THREADS).unwrap();
        assert_eq!(parallel, sequential);
    }

    #[test]
    fn semantic_identity_ignores_trivia_but_not_tokens() {
        let roots = [Root::Embedded(crate::stdlib::STDLIB)];
        let base = "fn answer() : Int = 42\n";
        let trivia = "\n-- comment\nfn answer () : Int = 42\n";
        let changed = "fn answer() : Int = 43\n";
        let digest = semantic_inputs_digest(base, &roots, SEQUENTIAL_QUERY_THREADS).unwrap();
        assert_eq!(
            semantic_inputs_digest(trivia, &roots, PARALLEL_QUERY_THREADS).unwrap(),
            digest
        );
        assert_ne!(
            semantic_inputs_digest(changed, &roots, SEQUENTIAL_QUERY_THREADS).unwrap(),
            digest
        );
    }
}
