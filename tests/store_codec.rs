// The store's central invariant, gated on the codec: for every definition,
// encode -> decode -> re-hash reproduces the identical per-definition content
// hash, and re-encode is byte-identical (the encoding is canonical). Plus a
// sharing proof (a repeated subexpression is one node entry), mutual-recursion
// coverage (a group serializes and re-hashes as a unit), and totality under
// hostile input (random bytes and truncations return Err, never panic).

use std::collections::BTreeMap;

use prism::core::{hash_program, scc_groups, Comp, Core, CoreFn, CoreOp, CorePat, HandleOp, Value};
use prism::store::codec::{decode_def, encode_def, AnonEntry};
use prism::store::CodecError;
use prism::sym::Sym;

fn sym(s: &str) -> Sym {
    Sym::new(s)
}

fn func(name: &str, params: &[&str], body: Comp) -> CoreFn {
    CoreFn {
        name: sym(name),
        params: params.iter().map(|p| sym(p)).collect(),
        dict_arity: 0,
        body,
    }
}

fn member_refs<'a>(core: &'a Core, group: &[Sym]) -> Vec<&'a CoreFn> {
    group
        .iter()
        .map(|s| core.fns.iter().find(|f| f.name == *s).unwrap())
        .collect()
}

// Hash a hand-built program (empty metadata) and encode the definition `name` as
// it would be committed: its whole recursive group, the whole hash map as the
// dependency source, its own hash as the contract.
fn encode_member(core: &Core, name: &str) -> (Vec<u8>, String) {
    let hashes = hash_program(core, &BTreeMap::new());
    let group = scc_groups(core)
        .into_iter()
        .find(|g| g.iter().any(|s| *s == sym(name)))
        .unwrap();
    let members = member_refs(core, &group);
    let target = group.iter().position(|s| *s == sym(name)).unwrap();
    let hash = hashes[&sym(name)].clone();
    let bytes = encode_def(&AnonEntry {
        group: &members,
        target,
        hash: &hash,
        deps: &hashes,
        meta: &BTreeMap::new(),
    });
    (bytes, hash)
}

// Decode, re-hash (must equal the original hash), and re-encode (must be
// byte-identical). The per-definition check, driven off whatever a
// stored object carries.
fn assert_roundtrip_bytes(bytes: &[u8], hash: &str) {
    let decoded = decode_def(bytes).expect("decode");
    assert_eq!(decoded.contract, hash, "contract");
    assert_eq!(
        decoded.rehash().as_deref(),
        Some(hash),
        "re-hash reproduces the content hash"
    );
    let refs: Vec<&CoreFn> = decoded.group.iter().collect();
    let re = encode_def(&AnonEntry {
        group: &refs,
        target: decoded.target,
        hash: &decoded.contract,
        deps: &decoded.deps,
        meta: &decoded.meta,
    });
    assert_eq!(re, bytes, "re-encode is byte-identical");
}

fn assert_roundtrip(core: &Core, name: &str) {
    let (bytes, hash) = encode_member(core, name);
    assert_roundtrip_bytes(&bytes, &hash);
}

#[test]
fn identity_roundtrips() {
    let core = Core {
        fns: vec![func("id", &["x"], Comp::Return(Value::Var(sym("x"))))],
    };
    assert_roundtrip(&core, "id");
}

// A self-call must resolve to an intra-group reference, not a dependency hash, so
// a recursive definition re-hashes to its whole-program hash.
#[test]
fn self_recursion_roundtrips() {
    let step = Comp::Bind(
        Box::new(Comp::Prim(CoreOp::Eq, Value::Var(sym("n")), Value::Int(0))),
        sym("done"),
        Box::new(Comp::If(
            Value::Var(sym("done")),
            Box::new(Comp::Return(Value::Int(0))),
            Box::new(Comp::Bind(
                Box::new(Comp::Prim(CoreOp::Sub, Value::Var(sym("n")), Value::Int(1))),
                sym("m"),
                Box::new(Comp::Call(sym("countdown"), vec![Value::Var(sym("m"))])),
            )),
        )),
    );
    let core = Core {
        fns: vec![func("countdown", &["n"], step)],
    };
    assert_roundtrip(&core, "countdown");
}

// A mutually-recursive group: each member's hash folds in the other's body, so
// the whole group travels in each member's object and re-hashes as a unit. Both
// members' intra-group calls resolve to member references, not dependency hashes.
#[test]
fn mutual_recursion_roundtrips() {
    // is_even(n) = if n == 0 then true else is_odd(n - 1)
    // is_odd(n)  = if n == 0 then false else is_even(n - 1)
    let branch = |sibling: &str, base: Value| {
        Comp::Bind(
            Box::new(Comp::Prim(CoreOp::Eq, Value::Var(sym("n")), Value::Int(0))),
            sym("z"),
            Box::new(Comp::If(
                Value::Var(sym("z")),
                Box::new(Comp::Return(base)),
                Box::new(Comp::Bind(
                    Box::new(Comp::Prim(CoreOp::Sub, Value::Var(sym("n")), Value::Int(1))),
                    sym("m"),
                    Box::new(Comp::Call(sym(sibling), vec![Value::Var(sym("m"))])),
                )),
            )),
        )
    };
    let core = Core {
        fns: vec![
            func("is_even", &["n"], branch("is_odd", Value::Bool(true))),
            func("is_odd", &["n"], branch("is_even", Value::Bool(false))),
        ],
    };
    assert_eq!(
        scc_groups(&core).iter().filter(|g| g.len() == 2).count(),
        1,
        "is_even/is_odd form one two-member group"
    );
    assert_roundtrip(&core, "is_even");
    assert_roundtrip(&core, "is_odd");
}

// A call to another top-level definition serializes as that definition's content
// hash; decoding in isolation and re-hashing with only that dependency hash
// reproduces the caller's whole-program hash.
#[test]
fn dependency_substitution_roundtrips() {
    let f = func("f", &["x"], Comp::Return(Value::Var(sym("x"))));
    let g = func(
        "g",
        &["y"],
        Comp::Call(sym("f"), vec![Value::Var(sym("y"))]),
    );
    let core = Core { fns: vec![f, g] };
    assert_roundtrip(&core, "g");

    // The isolated entry carries exactly one dependency hash: f's.
    let hashes = hash_program(&core, &BTreeMap::new());
    let (bytes, _) = encode_member(&core, "g");
    let decoded = decode_def(&bytes).unwrap();
    assert_eq!(decoded.dep_hashes, vec![hashes[&sym("f")].clone()]);
}

// Case arms, constructor patterns, and their binders round-trip (the de Bruijn
// bookkeeping for pattern binders is the same on both sides).
#[test]
fn case_and_ctor_patterns_roundtrip() {
    let arm = (
        CorePat::Ctor(sym("Pair"), vec![Some(sym("a")), Some(sym("b"))]),
        Comp::Prim(CoreOp::Add, Value::Var(sym("a")), Value::Var(sym("b"))),
    );
    let wild = (CorePat::Wild, Comp::Return(Value::Int(0)));
    let body = Comp::Case(Value::Var(sym("p")), vec![arm, wild]);
    let core = Core {
        fns: vec![func("sum_pair", &["p"], body)],
    };
    assert_roundtrip(&core, "sum_pair");
}

// A handler with a return clause and an operation with a resume continuation: the
// trickiest binder shapes, all round-tripped.
#[test]
fn handler_roundtrips() {
    let op = HandleOp {
        name: sym("ask"),
        params: vec![],
        resume: sym("k"),
        body: Comp::App(
            Box::new(Comp::Force(Value::Var(sym("k")))),
            vec![Value::Int(42)],
        ),
    };
    let body = Comp::Handle {
        body: Box::new(Comp::Do(sym("ask"), vec![])),
        return_var: Some(sym("r")),
        return_body: Some(Box::new(Comp::Return(Value::Var(sym("r"))))),
        ops: vec![op],
    };
    let core = Core {
        fns: vec![func("run_ask", &[], body)],
    };
    assert_roundtrip(&core, "run_ask");
}

// The reuse-token and mutable-cell node shapes (produced by later passes, so not
// present in pre-optimization corpus Core) round-trip structurally. The term is
// artificial; only its node coverage matters.
#[test]
fn reuse_and_ref_nodes_roundtrip() {
    let inner = Comp::WithReuse {
        token: sym("tok"),
        freed: Value::Var(sym("x")),
        body: Box::new(Comp::Return(Value::Var(sym("x")))),
    };
    let body = Comp::Bind(
        Box::new(Comp::RefNew(Value::Var(sym("x")))),
        sym("cell"),
        Box::new(Comp::Bind(
            Box::new(Comp::RefGet(Value::Var(sym("cell")))),
            sym("y"),
            Box::new(Comp::Bind(
                Box::new(Comp::RefSet(Value::Var(sym("cell")), Value::Var(sym("y")))),
                sym("u1"),
                Box::new(Comp::Bind(
                    Box::new(Comp::Dup(Value::Var(sym("x")))),
                    sym("u2"),
                    Box::new(Comp::Bind(
                        Box::new(Comp::Drop(Value::Var(sym("y")))),
                        sym("u3"),
                        Box::new(Comp::Mask(vec![sym("St")], Box::new(inner))),
                    )),
                )),
            )),
        )),
    );
    let core = Core {
        fns: vec![func("plumbing", &["x"], body)],
    };
    assert_roundtrip(&core, "plumbing");
}

// A subexpression that occurs twice is one node-table entry: the two-occurrence
// term has the same node count as the one-occurrence term, and a distinct
// subexpression grows the table.
#[test]
fn shared_subexpression_is_one_entry() {
    // A closed value with internal structure, so sharing is unambiguous.
    let shared = || Value::Ctor(sym("Pair"), 0, vec![Value::Int(1), Value::Int(2)]);
    let other = Value::Ctor(sym("Pair"), 0, vec![Value::Int(3), Value::Int(4)]);

    let one = Core {
        fns: vec![func("one", &[], Comp::Return(Value::Tuple(vec![shared()])))],
    };
    let twice = Core {
        fns: vec![func(
            "twice",
            &[],
            Comp::Return(Value::Tuple(vec![shared(), shared()])),
        )],
    };
    let distinct = Core {
        fns: vec![func(
            "distinct",
            &[],
            Comp::Return(Value::Tuple(vec![shared(), other])),
        )],
    };

    let count =
        |core: &Core, name: &str| decode_def(&encode_member(core, name).0).unwrap().node_count;
    let n_one = count(&one, "one");
    let n_twice = count(&twice, "twice");
    let n_distinct = count(&distinct, "distinct");

    assert_eq!(n_twice, n_one, "a repeated subexpression is one entry");
    assert!(n_distinct > n_one, "distinct subexpressions are not merged");
}

// The whole standard library is a representative corpus: hundreds of real
// definitions covering every value and computation shape the front end produces,
// including at least one mutual-recursion group. Every one must satisfy the
// central invariant.
#[test]
fn stdlib_corpus_roundtrips() {
    let src = prism::with_prelude("import Replay (..)\nimport Concurrent (..)\n");
    let (core, hashes, metas) = prism::driver::store_def_inputs(&src).expect("front end");
    assert!(core.fns.len() > 50, "corpus should be substantial");

    let groups = scc_groups(&core);
    assert!(
        groups.iter().any(|g| g.len() > 1),
        "corpus should include a mutual-recursion group (exercises the group path)"
    );

    for group in groups {
        let members = member_refs(&core, &group);
        for (target, f) in members.iter().enumerate() {
            let Some(hash) = hashes.get(&f.name) else {
                continue;
            };
            let bytes = encode_def(&AnonEntry {
                group: &members,
                target,
                hash,
                deps: &hashes,
                meta: &metas,
            });
            let decoded =
                decode_def(&bytes).unwrap_or_else(|e| panic!("decode {}: {e}", f.name.as_str()));
            assert_eq!(&decoded.contract, hash, "{}: contract", f.name.as_str());
            assert_eq!(
                decoded.rehash().as_deref(),
                Some(hash.as_str()),
                "{}: re-hash reproduces the content hash",
                f.name.as_str()
            );
            let refs: Vec<&CoreFn> = decoded.group.iter().collect();
            let re = encode_def(&AnonEntry {
                group: &refs,
                target: decoded.target,
                hash: &decoded.contract,
                deps: &decoded.deps,
                meta: &decoded.meta,
            });
            assert_eq!(
                re,
                bytes,
                "{}: re-encode is byte-identical",
                f.name.as_str()
            );
        }
    }
}

// A tiny linear-congruential generator: deterministic hostile input, no dependency.
struct Lcg(u64);

impl Lcg {
    const fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0
    }
}

#[test]
fn random_bytes_never_panic() {
    let mut lcg = Lcg(0x1234_5678_9abc_def0);
    for _ in 0..20_000 {
        let len = (lcg.next() % 96) as usize;
        let bytes: Vec<u8> = (0..len).map(|_| (lcg.next() & 0xff) as u8).collect();
        // The assertion is that this returns rather than panics.
        let _ = decode_def(&bytes);
    }
}

#[test]
fn truncations_are_rejected() {
    let core = Core {
        fns: vec![func("id", &["x"], Comp::Return(Value::Var(sym("x"))))],
    };
    let (bytes, _) = encode_member(&core, "id");
    assert!(decode_def(&bytes).is_ok(), "the full frame decodes");
    for n in 0..bytes.len() {
        assert!(
            decode_def(&bytes[..n]).is_err(),
            "truncation at {n} must be rejected"
        );
    }
}

#[test]
fn trailing_bytes_and_foreign_scheme_rejected() {
    let core = Core {
        fns: vec![func("id", &["x"], Comp::Return(Value::Var(sym("x"))))],
    };
    let (bytes, _) = encode_member(&core, "id");

    let mut with_trailer = bytes.clone();
    with_trailer.push(0);
    assert!(matches!(
        decode_def(&with_trailer),
        Err(CodecError::TrailingBytes)
    ));

    // Corrupt a byte inside the scheme tag: caught on the header, before the body.
    let mut corrupt = bytes;
    corrupt[3] ^= 0xff;
    assert!(matches!(
        decode_def(&corrupt),
        Err(CodecError::Scheme | CodecError::Utf8)
    ));
}
