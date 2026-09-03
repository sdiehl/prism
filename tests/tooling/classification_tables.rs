// Two boundaries answer a small integer rather than a message, so that the same
// failure is the same Prism value whichever tier a program is running on and
// whoever wrote the handler: the socket table shared by `src/eval/net.rs`,
// `runtime/prism_net.c`, and `lib/std/Net.pr`, and the mobility table shared by
// `src/eval/mobility.rs`, `runtime/prism_mobility.c`, and `lib/std/Teleport.pr`.
//
// Each of those six lists is a plain sequence of constants in a different
// language, which is exactly the shape that drifts silently: renumbering one
// list does not fail to compile anywhere, it just makes one tier report
// `Refused` where the other reports `Unreachable`. Nothing in the build can
// relate them, so this reads the sources and relates them here.
//
// The C source is the reference because it is the only one of the three that
// states both tables in full. A change made deliberately in all three files
// still passes, which is the point: what is being caught is a change made in
// one.

use std::collections::BTreeMap;
use std::path::Path;

type Table = BTreeMap<String, i64>;

fn read(rel: &str) -> String {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join(rel);
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()))
}

fn define(line: &str, prefix: &str) -> Option<(String, i64)> {
    let rest = line.trim().strip_prefix("#define ")?;
    let (name, value) = rest.split_once(' ')?;
    Some((
        name.strip_prefix(prefix)?.to_lowercase(),
        value.trim().parse().ok()?,
    ))
}

// The classification table in a runtime source: the first unbroken run of
// `#define <prefix><NAME> <n>`. Taking a contiguous block rather than every
// matching line in the file is what separates the table from the unrelated
// `#define`s further down, and it is not a guess: a table whose entries a blank
// line or a comment could be inserted into is not one table.
fn c_table(src: &str, prefix: &str) -> Table {
    src.lines()
        .skip_while(|line| define(line, prefix).is_none())
        .map_while(|line| define(line, prefix))
        .collect()
}

// Every `const NAME: i64 = <n>;` in the file. Both modules use that type for
// their classification codes and for nothing else, so no filtering by position
// is needed and the guard does not depend on where in the file the table sits.
fn rust_table(src: &str) -> Table {
    src.lines()
        .filter_map(|line| {
            let (name, value) = line.trim().strip_prefix("const ")?.split_once(": i64 = ")?;
            Some((
                name.to_lowercase(),
                value.trim_end_matches(';').parse().ok()?,
            ))
        })
        .collect()
}

// Every `let <prefix><name> : Int = <n>` in the file.
fn prism_table(src: &str, prefix: &str) -> Table {
    src.lines()
        .filter_map(|line| {
            let rest = line.trim().strip_prefix("let ")?.strip_prefix(prefix)?;
            let (name, value) = rest.split_once(" : Int = ")?;
            Some((name.to_string(), value.trim().parse().ok()?))
        })
        .collect()
}

// The three lists must agree name for name and number for number, except that
// Prism may leave out codes it never compares against. Those are the ones its
// `else` arm absorbs, and naming them here is what keeps the omission a decision
// rather than an oversight.
fn agree(what: &str, c: &Table, rust: &Table, prism: &Table, prism_omits: &[&str]) {
    assert!(
        !c.is_empty(),
        "{what}: no C table found, so this guard proved nothing"
    );
    assert_eq!(rust, c, "{what}: the interpreter and the runtime disagree");
    let expected: Table = c
        .iter()
        .filter(|(name, _)| !prism_omits.contains(&name.as_str()))
        .map(|(name, code)| (name.clone(), *code))
        .collect();
    assert_eq!(
        prism, &expected,
        "{what}: the stdlib and the runtime disagree"
    );
}

#[test]
fn the_socket_classification_table_is_one_table() {
    agree(
        "Net",
        &c_table(&read("runtime/prism_net.c"), "PRISM_NET_"),
        &rust_table(&read("src/eval/net.rs")),
        &prism_table(&read("lib/std/Net.pr"), "net_code_"),
        // `Other` is the fallback `net_error` reaches when it recognizes nothing,
        // so Net.pr never compares against its code.
        &["other"],
    );
}

#[test]
fn the_mobility_classification_table_is_one_table() {
    agree(
        "Move",
        &c_table(&read("runtime/prism_mobility.c"), "PRISM_MOVE_"),
        &rust_table(&read("src/eval/mobility.rs")),
        &prism_table(&read("lib/std/Teleport.pr"), "move_code_"),
        // `Undelivered` runs the other way: it is a `MoveError` no runtime can
        // raise, so it has a constructor and no code in any of the three files.
        &[],
    );
}

// Three readers that each answer an empty table on a source they do not
// understand would agree with each other about nothing at all, and the tests
// above would pass without having compared anything. This pins them against
// literals instead: each finds its table, stops at the end of it, and ignores
// the constants around it.
#[test]
fn the_readers_find_a_table_and_stop_at_its_edge() {
    let c = "/* a table */\n#define P_A 0\n#define P_B 1\n\n#define P_SLOTS 256\n";
    assert_eq!(
        c_table(c, "P_"),
        Table::from([("a".into(), 0), ("b".into(), 1)])
    );
    let rust = "const A: i64 = 0;\nconst B: i64 = 1;\nconst SLOTS: usize = 256;\n";
    assert_eq!(
        rust_table(rust),
        Table::from([("a".into(), 0), ("b".into(), 1)])
    );
    let prism = "let c_a : Int = 0\n\nlet c_b : Int = 1\n\nlet elsewhere : Int = 9\n";
    assert_eq!(
        prism_table(prism, "c_"),
        Table::from([("a".into(), 0), ("b".into(), 1)])
    );
}

// The bound on how many sockets one run may hold open is a behavior both tiers
// have to share: a program that opens too many must earn `Limit` at the same
// socket in each, or a native binary and an interpreted run of the same source
// disagree about where the failure is.
#[test]
fn both_tiers_stop_issuing_handles_at_the_same_point() {
    let native = read("runtime/prism_net.c")
        .lines()
        .find_map(|line| define(line, "PRISM_NET_SLOTS").map(|(_, n)| n))
        .expect("the native socket table has no declared bound");
    let interpreted = read("src/eval/net.rs")
        .lines()
        .find_map(|line| {
            let value = line.trim().strip_prefix("const SLOTS: usize = ")?;
            value.trim_end_matches(';').parse::<i64>().ok()
        })
        .expect("the interpreter's socket table has no declared bound");
    assert_eq!(
        interpreted, native,
        "the two socket tables hold different numbers of sockets"
    );
}

// `split_address` rejects a port above the 16-bit range before the boundary is
// reached, and the resolver rejects one again on the way in. Two bounds that
// disagree would make one of the two checks unreachable and turn a parse refusal
// into a resolver refusal, which is a different `NetError` for the same address.
#[test]
fn the_stdlib_and_the_resolver_bound_a_port_the_same_way() {
    let native = read("runtime/prism_net.c")
        .lines()
        .find_map(|line| define(line, "PRISM_NET_PORT_MAX").map(|(_, n)| n))
        .expect("the native resolver has no declared port bound");
    let stdlib = prism_table(&read("lib/std/Net.pr"), "net_port_")
        .remove("max")
        .expect("Net.pr has no declared port bound");
    assert_eq!(stdlib, native, "the two port bounds disagree");
}
