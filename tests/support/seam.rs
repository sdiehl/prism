//! Release- and host-neutral golden comparison.
//!
//! Three fields of a committed artifact describe the build that wrote it rather
//! than the program it is about: the compiler version, the host target triple,
//! and the standard library's fingerprint. Punching them out keeps a golden
//! about its program, so a release bump or an unrelated library edit reseats
//! nothing. Everything else the artifact pins (the bundle digest, the
//! source-root fingerprint, the per-function digests) is a function of the
//! program's own closure and still reseats on a genuine change; the compiler's
//! output is untouched, so a real binary carries the real values.
//!
//! Included by path from the golden-comparing test targets rather than declared
//! in `support/mod.rs`, since they use none of the rest of `support`.

// Each including target uses its own subset of this module, so per-target dead
// code analysis would otherwise warn; a test binary is its own crate root, so
// `pub` here is crate-visible only (see `support/mod.rs`).
#![allow(dead_code, unreachable_pub)]

// What a punched-out field leaves behind. Spelled as a placeholder rather than
// as some plausible value, so a golden never reads as a claim about a version
// or a host it was not written on.
pub const VERSION_HOLE: &str = "<version>";
pub const TARGET_HOLE: &str = "<target>";
pub const STDLIB_HOLE: &str = "<stdlib-root>";
pub const NODE_HOLE: &str = "<node>";

// The JSON seam envelope's stamp, and the key whose value the node erasure
// replaces.
const COMPILER_KEY: &str = "\"compiler\": ";
const NODE_ID_KEY: &str = "\"id\": ";

// The artifact rows that name a build rather than a program, as they are
// spelled inside a continuation table: a row key, two spaces, the value.
const BUILD_ROWS: [(&str, &str); 3] = [
    ("compiler  ", VERSION_HOLE),
    ("target  ", TARGET_HOLE),
    ("stdlib-root  ", STDLIB_HOLE),
];

// The native continuation tables, the only lines of a pipeline report carrying
// an artifact envelope.
const KONT_PREFIXES: [&str; 2] = [
    "@prism_native_kont_table = constant [",
    "@prism_native_kont_state_map = constant [",
];

/// A JSON seam artifact with the compiler stamp punched out. The version is
/// explicit so a cross-release comparison can punch an older document's stamp
/// too; [`json`] is the current build's.
pub fn json_stamped(doc: &str, version: &str) -> String {
    doc.replace(
        &format!("{COMPILER_KEY}\"{version}\""),
        &format!("{COMPILER_KEY}\"{VERSION_HOLE}\""),
    )
}

/// A JSON seam artifact as this build writes it, with the stamp punched out.
pub fn json(doc: &str) -> String {
    json_stamped(doc, env!("CARGO_PKG_VERSION"))
}

/// A pipeline report with its build stamps punched out. They live in the
/// native continuation tables, escaped inside an LLVM byte-array constant whose
/// declared length has to be carried along with them.
pub fn report(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    for line in text.lines() {
        out.push_str(&kont_line(line));
        out.push('\n');
    }
    out
}

/// Every node number replaced with a hole. Only `id` carries one and nothing
/// refers to a node by number, so this leaves every structural field of the
/// document under comparison while dropping a numbering that spans the prelude
/// and every imported module, and so moves for reasons outside the document.
pub fn erase_node_ids(doc: &str) -> String {
    let mut out = String::with_capacity(doc.len());
    let mut rest = doc;
    while let Some(at) = rest.find(NODE_ID_KEY) {
        let (head, tail) = rest.split_at(at + NODE_ID_KEY.len());
        out.push_str(head);
        let digits = tail.len() - tail.trim_start_matches(|c: char| c.is_ascii_digit()).len();
        if digits > 0 {
            out.push_str(NODE_HOLE);
        }
        rest = &tail[digits..];
    }
    out.push_str(rest);
    out
}

fn kont_line(line: &str) -> String {
    if !KONT_PREFIXES.iter().any(|prefix| line.starts_with(prefix)) {
        return line.to_string();
    }
    let holed = BUILD_ROWS
        .into_iter()
        .fold(line.to_string(), |line, (key, hole)| {
            hole_row_value(&line, key, hole)
        });
    let delta = holed.len().cast_signed() - line.len().cast_signed();
    resize_byte_array(&holed, delta)
}

// Replace the value following `key` in one escaped artifact row. A row's value
// runs to the escape that opens the next row or to the quote that closes the
// constant, and a version, a triple and a digest can contain neither.
fn hole_row_value(line: &str, key: &str, hole: &str) -> String {
    let Some(at) = line.find(key) else {
        return line.to_string();
    };
    let start = at + key.len();
    let end = line[start..]
        .find(['\\', '"'])
        .map_or(line.len(), |len| start + len);
    format!("{}{hole}{}", &line[..start], &line[end..])
}

// Carry an LLVM byte-array constant's declared `[N x i8]` length across a
// payload edit of `delta` characters. Every substitution above is unescaped
// ASCII on both sides, so a character of payload text is a byte of array. The
// length is adjusted rather than punched out because a constant whose count
// contradicted the bytes beside it would be a worse thing to commit than a
// number no single build emits.
fn resize_byte_array(line: &str, delta: isize) -> String {
    let Some(start) = line.find('[').map(|index| index + 1) else {
        return line.to_string();
    };
    let Some(end) = line[start..].find(" x i8]").map(|len| start + len) else {
        return line.to_string();
    };
    let Ok(len) = line[start..end].parse::<isize>() else {
        return line.to_string();
    };
    format!("{}{}{}", &line[..start], len + delta, &line[end..])
}
