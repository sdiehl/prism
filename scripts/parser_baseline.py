#!/usr/bin/env python3
"""Generate the frozen parser-compaction accounting receipt.

The receipt has two deliberately separate ledgers:

* Ledger A reproduces the parser row in scripts/scoreboard.py.
* Ledger B gives the symmetric, transitive experiment boundary.

All baseline content is read from ORACLE_COMMIT's Git blobs.  The current
checkout is used only for this generator and its generated receipt, so
``--check`` remains stable after later parser edits and commits.
"""

from __future__ import annotations

import fnmatch
import re
import subprocess
import sys
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / "docs" / "internal" / "PARSER_COMPACTION_BASELINE.md"

ORACLE_COMMIT = "46886c1fa7064e4809020c1b788b3ee3531d6a63"
MARKERS = {".rs": "//", ".lalrpop": "//", ".pr": "--"}
TOTAL_CAP = 4_872
TOTAL_REDUCTION = Fraction(3, 4)
OUTPUT_EXPANSION = Fraction(11, 10)
FAMILIES = ("types", "patterns", "exprs", "decls")
SOURCE_BUCKETS = FAMILIES + ("all", "patterns+exprs", "exprs+decls")
BUCKET_REACH = {
    "types": ("types",),
    "patterns": ("patterns",),
    "exprs": ("exprs",),
    "decls": ("decls",),
    "all": FAMILIES,
    "patterns+exprs": ("patterns", "exprs"),
    "exprs+decls": ("exprs", "decls"),
}

# Ledger A is the exact parser row from scripts/scoreboard.py.  Keep the globs
# visible rather than silently replacing the scoreboard boundary with a hand
# maintained file list.
LEDGER_A_RUST_SPECS = (
    "crates/prism-syntax/src/grammar.lalrpop",
    "crates/prism-syntax/src/sugar.rs",
)
LEDGER_A_PRISM_SPECS = (
    "lib/std/Syntax/Parse.pr",
    "lib/std/Syntax/Parse/*.pr",
)
EXPECTED_LEDGER_A_RUST = (
    "crates/prism-syntax/src/grammar.lalrpop",
    "crates/prism-syntax/src/sugar.rs",
)
EXPECTED_LEDGER_A_PRISM = (
    "lib/std/Syntax/Parse.pr",
    "lib/std/Syntax/Parse/Build.pr",
    "lib/std/Syntax/Parse/Decl.pr",
    "lib/std/Syntax/Parse/DeclClass.pr",
    "lib/std/Syntax/Parse/DeclStable.pr",
    "lib/std/Syntax/Parse/Expr.pr",
    "lib/std/Syntax/Parse/Pattern.pr",
    "lib/std/Syntax/Parse/Support.pr",
    "lib/std/Syntax/Parse/Type.pr",
)

# Ledger B files are deduplicated paths.  The grammar and sugar files are
# allocated by symbol below; coeffect.rs is included because Type's grammar
# action calls its canonical row validator.
LEDGER_B_RUST_INCLUDE = (
    ("crates/prism-syntax/src/grammar.lalrpop", "per-production",
     "grammar root; allocated by every top-level production"),
    ("crates/prism-syntax/src/sugar.rs", "per-symbol",
     "parse-action root; allocated by every top-level definition"),
    ("crates/prism-syntax/src/parse/mod.rs", "all",
     "parser driver, item distribution, and LALRPOP fault conversion"),
    ("crates/prism-syntax/src/error/parse.rs", "all",
     "parse-fault representation and canonical expectation surface"),
    ("crates/prism-syntax/src/coeffect.rs", "types",
     "transitive Type/Decl action helper: row validation and noalloc lifting; "
     "conservatively charged whole-file to Type"),
)
LEDGER_B_PRISM_INCLUDE = (
    ("lib/std/Syntax/Parse.pr", "all", "public parser entry points"),
    ("lib/std/Syntax/Parse/Support.pr", "all",
     "outcome type, depth budget, and token classification"),
    ("lib/std/Syntax/Parse/Build.pr", "patterns+exprs",
     "span and synthetic-node builders reached by Pattern and Expr"),
    ("lib/std/Syntax/Parse/Type.pr", "types",
     "type grammar and the corresponding usage-row validation"),
    ("lib/std/Syntax/Parse/Pattern.pr", "patterns", "pattern grammar"),
    ("lib/std/Syntax/Parse/Expr.pr", "exprs", "expression grammar"),
    ("lib/std/Syntax/Parse/Decl.pr", "decls", "declaration grammar"),
    ("lib/std/Syntax/Parse/DeclClass.pr", "decls",
     "class/instance declaration grammar"),
    ("lib/std/Syntax/Parse/DeclStable.pr", "decls",
     "stable declaration grammar"),
    ("lib/std/Syntax/Cursor.pr", "all",
     "in-tree parser cursor/fault/Pratt substrate; Rust's counterpart is the "
     "out-of-tree lalrpop_util runtime"),
)

# Explicit dependency-edge inventory for the Rust grammar/action roots.  This
# is a symbol/module closure audit, not an assertion that every dependency is
# parser-specific.  Each referenced in-tree module is classified once.
# (source, target, disposition, family, evidence/reason)
RUST_DEPENDENCY_EDGES = (
    ("grammar.lalrpop", "sugar.rs", "include", "per-symbol",
     "crate::sugar imports and crate::sugar::StableItem"),
    ("grammar.lalrpop", "coeffect.rs", "include", "types",
     "CoeffectRow::new through ast.rs's public re-export"),
    ("grammar.lalrpop", "ast.rs", "exclude", "surface-ast",
     "surface model constructed by both parser implementations"),
    ("grammar.lalrpop", "kind.rs", "exclude", "surface-ast",
     "Kind values are surface type vocabulary"),
    ("grammar.lalrpop", "kw.rs", "exclude", "shared-vocabulary",
     "canonical keyword constants"),
    ("grammar.lalrpop", "lex/", "exclude", "lexer",
     "Token is the lexer/parser wire type"),
    ("grammar.lalrpop", "names.rs", "exclude", "shared-vocabulary",
     "canonical name classification"),
    ("grammar.lalrpop", "marginalia::Span", "exclude", "external",
     "external span substrate"),
    ("grammar.lalrpop", "lalrpop_util", "exclude", "external-runtime",
     "external generated-parser runtime and errors"),
    ("sugar.rs", "ast.rs", "exclude", "surface-ast",
     "surface model and constructors"),
    ("sugar.rs", "coeffect.rs", "include", "types",
     "CoeffectRow::is_noalloc_only through Ty::Coeffect"),
    ("sugar.rs", "kw.rs", "exclude", "shared-vocabulary",
     "canonical keyword constants"),
    ("sugar.rs", "names.rs", "exclude", "shared-vocabulary",
     "canonical name classification"),
    ("sugar.rs", "marginalia::Span", "exclude", "external",
     "external span substrate"),
)

LEDGER_B_PRISM_EXCLUDE = (
    ("lib/std/Syntax/{Token,Ast,Source,Diagnostic}.pr",
     "surface/token/diagnostic vocabulary, symmetric with Rust exclusions"),
    ("lib/std/Syntax/{Lex,Layout}.pr", "owned by the lexer/layout row"),
    ("lib/std/Syntax/Codec.pr", "owned by the codec row"),
    ("lib/std/Syntax/{Walk,Query,Analysis,Edit,Rename,Flow,Report,"
     "Identity,Resolved}.pr", "parser consumers, not parser source"),
)

# Every one of the oracle grammar's 133 top-level productions, including
# generic helpers and public entry productions, is classified here.
PRODUCTION_FAMILY = {
    "all": ["Comma"],
    "patterns+exprs": ["CommaPlus"],
    "exprs+decls": ["Param", "Params"],
    "decls": [
        "Program", "Items", "PubItem", "OpaqueItem", "Item", "DeprecatedD",
        "ImportD", "ModPath", "ImportName", "PatternD", "PatClauses",
        "PatClause", "StableD", "StableItem", "Migrations", "MigrationRow",
        "Route", "VersionArg", "Rung", "RungBody", "RungField",
        "FrozenBadge", "Converter", "ConvKw", "ConvBody", "ConvField",
        "DropLoss", "ClassD", "ClassSigs", "ClassSig", "InstanceD",
        "InstFns", "CanonicalD", "GivenClause", "ConstraintP", "Data",
        "Newtype", "CtorsRhs", "Derives",
        "DeriveName", "TyParams", "KindedTyParams", "KindedTyParam", "Ctors",
        "Ctor", "CtorArgs", "RecordField", "AliasOrSynonym", "AliasRhs",
        "ErrorD", "EffDecl", "EffOpSep", "EffOpList", "EffOp", "EffOpParam",
        "Fn", "DeclMods", "ReflectTarget", "Requires", "Ensures",
        "Decreases", "LogicFn", "FipKw", "ConstD", "WhereBlock",
        "WhereBind", "RetAnn", "RetType",
    ],
    "types": [
        "TypeArg", "DimTerm", "DimTail", "Ann", "Type", "TypeSig", "Arrow",
        "ArrowEff", "UType", "CoeffRowParts", "AType", "EffLabel",
    ],
    "patterns": [
        "Pattern", "PatAlt", "RecordPatFields", "RecordPatField", "PatAtom",
        "PatArgs",
    ],
    "exprs": [
        "ExprOrBlock", "BlockExpr", "Stmts", "Expr", "CompoundOp", "Default",
        "Qual", "IfElse", "OpenIfTail", "LetPat", "MatchArms", "HandleArms",
        "CatchArms", "CArms", "CatchArm", "HArms", "HandlerArm",
        "ResumeTail", "Pipe", "Compose", "ArmSep", "Arms", "Arm", "Or",
        "And", "Cmp", "CmpOp", "DotCmpOp", "DotAddOp", "DotMulOp", "Add",
        "Mul", "Neg", "Pow", "Call", "CallTight", "TrailerParams", "Atom",
        "PathIndex", "PathSeg", "PathSteps", "PathUpdate", "RecordExprField",
    ],
}

# All 34 top-level definitions in sugar.rs (constants, enums, and functions),
# not only public `fn` definitions.
SUGAR_SYMBOL_FAMILY = {
    "exprs+decls": ["param", "params"],
    "decls": [
        "FLIP_CLASS", "FLIP_INSTANCE", "FLIP_EFFECT", "MIGRATE_RET_ORDER",
        "StableItem", "grade_word_msg", "mig_dir", "build_stable",
        "decl_mods", "lift_noalloc", "pattern_decl",
    ],
    "types": ["DECLINE_DIM_ARITH"],
    "exprs": [
        "GRADE_MANY_CLAUSE", "MIGRATE_RESUME", "IfTail", "dot_op_removed",
        "reflect_expr", "with_sentinel", "with_rest", "dot_call", "with_stmt",
        "open_if", "let_pat", "interp_lit", "try_mark", "unwrap_try",
        "try_stmt", "seq_stmt", "let_stmt", "assign_stmt", "compound_stmt",
        "compound_assign",
    ],
}

# The generated implementation is compared with exactly these handwritten
# derived family modules. Parse/Support/Build/Cursor remain maintained source,
# not generated output.
GENERATED_REPLACEMENT_PATHS = {
    "types": ("lib/std/Syntax/Parse/Type.pr",),
    "patterns": ("lib/std/Syntax/Parse/Pattern.pr",),
    "exprs": ("lib/std/Syntax/Parse/Expr.pr",),
    "decls": (
        "lib/std/Syntax/Parse/Decl.pr",
        "lib/std/Syntax/Parse/DeclClass.pr",
        "lib/std/Syntax/Parse/DeclStable.pr",
    ),
}
EXPECTED_GENERATED_REPLACEMENT = (
    "lib/std/Syntax/Parse/Decl.pr",
    "lib/std/Syntax/Parse/DeclClass.pr",
    "lib/std/Syntax/Parse/DeclStable.pr",
    "lib/std/Syntax/Parse/Expr.pr",
    "lib/std/Syntax/Parse/Pattern.pr",
    "lib/std/Syntax/Parse/Type.pr",
)


def git(*args: str) -> str:
    result = subprocess.run(
        ["git", *args], cwd=ROOT, text=True, capture_output=True
    )
    if result.returncode:
        sys.exit(result.stderr.strip() or f"git {' '.join(args)} failed")
    return result.stdout


TREE_PATHS = tuple(
    git("ls-tree", "-r", "--name-only", ORACLE_COMMIT).splitlines()
)


def expand_specs(specs: tuple[str, ...]) -> tuple[str, ...]:
    paths: list[str] = []
    for spec in specs:
        matches = [p for p in TREE_PATHS if fnmatch.fnmatchcase(p, spec)]
        if not matches:
            sys.exit(f"oracle path specification matched nothing: {spec}")
        paths.extend(matches)
    if len(paths) != len(set(paths)):
        sys.exit(f"overlapping path specifications: {specs}")
    return tuple(sorted(paths))


def blob_text(rel: str) -> str:
    return git("show", f"{ORACLE_COMMIT}:{rel}")


def blob_oid(rel: str) -> str:
    oid = git("rev-parse", f"{ORACLE_COMMIT}:{rel}").strip()
    kind = git("cat-file", "-t", oid).strip()
    if kind != "blob":
        sys.exit(f"oracle object for {rel} is {kind}, not blob")
    return oid


def count_text(text: str, marker: str) -> tuple[int, int, int]:
    raw = code = 0
    for line in text.splitlines():
        raw += 1
        stripped = line.strip()
        if stripped and not stripped.startswith(marker):
            code += 1
    return raw, code, len(text.encode("utf-8"))


def file_receipt(rel: str) -> tuple[int, int, int, str]:
    marker = MARKERS[Path(rel).suffix]
    raw, code, size = count_text(blob_text(rel), marker)
    return raw, code, size, blob_oid(rel)


def invert(family_map: dict[str, list[str]], what: str) -> dict[str, str]:
    result: dict[str, str] = {}
    for family, names in family_map.items():
        for name in names:
            if name in result:
                sys.exit(f"{what} `{name}` is classified twice")
            result[name] = family
    return result


def definition_family_lines(
    rel: str, head: re.Pattern[str], classifications: dict[str, list[str]],
    expected_count: int, what: str, attributes: bool = False,
) -> tuple[dict[str, int], tuple[str, ...]]:
    """Allocate each top-level definition block and prove exact coverage."""
    text = blob_text(rel)
    family_of = invert(classifications, what)
    found: list[str] = []
    result = dict.fromkeys(SOURCE_BUCKETS, 0)
    current = "all"
    pending_attributes = 0
    for line in text.splitlines():
        if attributes and line.startswith("#["):
            pending_attributes += 1
            continue
        match = head.match(line)
        if match:
            name = match.group(1)
            found.append(name)
            if name not in family_of:
                sys.exit(
                    f"{what} `{name}` is unclassified; update "
                    f"scripts/parser_baseline.py"
                )
            current = family_of[name]
            result[current] += pending_attributes
            pending_attributes = 0
        elif pending_attributes and line.strip() and not line.startswith("//"):
            sys.exit(f"top-level attribute in {rel} is not followed by a {what}")
        stripped = line.strip()
        if stripped and not stripped.startswith("//"):
            result[current] += 1
    if pending_attributes:
        sys.exit(f"orphan top-level attribute at end of {rel}")
    expected = set(family_of)
    actual = set(found)
    if len(found) != expected_count:
        sys.exit(
            f"expected {expected_count} {what}s in oracle, found {len(found)}"
        )
    if len(found) != len(actual):
        sys.exit(f"duplicate top-level {what} name in oracle")
    if actual != expected:
        sys.exit(
            f"{what} coverage mismatch: missing={sorted(actual - expected)}, "
            f"stale={sorted(expected - actual)}"
        )
    return result, tuple(found)


def grammar_family_lines() -> tuple[dict[str, int], tuple[str, ...]]:
    return definition_family_lines(
        "crates/prism-syntax/src/grammar.lalrpop",
        re.compile(
            r"^(?:pub\s+)?([A-Za-z][A-Za-z0-9_]*)"
            r"(?:<[^>]+>)?\s*:"
        ),
        PRODUCTION_FAMILY,
        133,
        "grammar production",
    )


def sugar_family_lines() -> tuple[dict[str, int], tuple[str, ...]]:
    # Top-level only: nested helpers are indented in this oracle.  This covers
    # const values, enums/structs/type aliases/statics, and every fn visibility
    # and qualifier combination, including `const fn with_sentinel`.
    return definition_family_lines(
        "crates/prism-syntax/src/sugar.rs",
        re.compile(
            r"^(?:(?:pub(?:\([^)]*\))?\s+)?"
            r"(?:(?:const|async|unsafe)\s+)*)"
            r"(?:fn|const|static|enum|struct|type)\s+"
            r"([A-Za-z_][A-Za-z0-9_]*)"
        ),
        SUGAR_SYMBOL_FAMILY,
        34,
        "sugar definition",
        attributes=True,
    )


def validate_dependency_inventory() -> None:
    include_paths = [row[0] for row in LEDGER_B_RUST_INCLUDE]
    include_paths += [row[0] for row in LEDGER_B_PRISM_INCLUDE]
    if len(include_paths) != len(set(include_paths)):
        sys.exit("Ledger B include path appears more than once")

    edge_keys = [(source, target) for source, target, *_ in RUST_DEPENDENCY_EDGES]
    if len(edge_keys) != len(set(edge_keys)):
        sys.exit("dependency edge is classified more than once")

    grammar = blob_text("crates/prism-syntax/src/grammar.lalrpop")
    sugar = blob_text("crates/prism-syntax/src/sugar.rs")
    referenced_modules = set(re.findall(r"crate::([a-z_][a-z0-9_]*)", grammar))
    referenced_modules |= set(re.findall(r"crate::([a-z_][a-z0-9_]*)", sugar))
    # CoeffectRow reaches coeffect through ast's public re-export, so it is an
    # explicit transitive edge rather than a direct `crate::coeffect` spelling.
    if "CoeffectRow::new" not in grammar:
        sys.exit("frozen grammar no longer calls CoeffectRow::new")
    if "is_noalloc_only" not in sugar:
        sys.exit("frozen sugar no longer calls CoeffectRow::is_noalloc_only")
    covered_modules = {
        Path(target).name.removesuffix(".rs")
        for _, target, _, _, _ in RUST_DEPENDENCY_EDGES
        if target.endswith(".rs") or target.endswith("/")
    }
    # `lex/` normalizes to `lex`; external modules have `::`.
    covered_modules |= {
        target.rstrip("/").split("/")[-1]
        for _, target, _, _, _ in RUST_DEPENDENCY_EDGES
        if target.endswith("/")
    }
    missing = referenced_modules - covered_modules
    if missing:
        sys.exit(f"unclassified grammar/sugar crate modules: {sorted(missing)}")


def allocate_reach(source: dict[str, int]) -> dict[str, Fraction]:
    """Split each unit bucket equally across its nonempty frozen Reach set."""
    total = {family: Fraction(0) for family in FAMILIES}
    for bucket, units in source.items():
        reach = BUCKET_REACH[bucket]
        if not reach:
            sys.exit(f"source bucket {bucket} has empty Reach")
        share = Fraction(units, len(reach))
        for family in reach:
            total[family] += share
    if sum(total.values()) != sum(source.values()):
        sys.exit("reachability allocation does not sum exactly")
    return total


def format_fraction(value: Fraction) -> str:
    if value.denominator == 1:
        return f"{value.numerator:,}"
    # Current frozen reach sets produce quarters; show the exact terminating
    # decimal without binary floating-point.
    scaled = value.numerator * 100 // value.denominator
    return f"{scaled // 100:,}.{scaled % 100:02d}".rstrip("0").rstrip(".")


def table(header: list[str], rows: list[tuple[object, ...]]) -> str:
    rendered = ["| " + " | ".join(header) + " |"]
    rendered.append("|" + "|".join(" --- " for _ in header) + "|")
    for row in rows:
        rendered.append("| " + " | ".join(str(value) for value in row) + " |")
    return "\n".join(rendered)


def render() -> str:
    validate_dependency_inventory()
    ledger_a_rust = expand_specs(LEDGER_A_RUST_SPECS)
    ledger_a_prism = expand_specs(LEDGER_A_PRISM_SPECS)
    if ledger_a_rust != EXPECTED_LEDGER_A_RUST:
        sys.exit("Ledger A Rust expansion no longer matches the frozen scoreboard")
    if ledger_a_prism != EXPECTED_LEDGER_A_PRISM:
        sys.exit("Ledger A Prism expansion no longer matches the frozen scoreboard")

    a_rust = [(path, *file_receipt(path)) for path in ledger_a_rust]
    a_prism = [(path, *file_receipt(path)) for path in ledger_a_prism]
    a_rust_code = sum(row[2] for row in a_rust)
    a_prism_code = sum(row[2] for row in a_prism)

    b_rust = [
        (path, family, *file_receipt(path), reason)
        for path, family, reason in LEDGER_B_RUST_INCLUDE
    ]
    b_prism = [
        (path, family, *file_receipt(path), reason)
        for path, family, reason in LEDGER_B_PRISM_INCLUDE
    ]
    r_sym = sum(row[3] for row in b_rust)
    h_sym = sum(row[3] for row in b_prism)

    grammar_source, productions = grammar_family_lines()
    sugar_source, sugar_symbols = sugar_family_lines()
    rust_source = {
        bucket: grammar_source[bucket] + sugar_source[bucket]
        for bucket in SOURCE_BUCKETS
    }
    for _, family, _, code, _, _, _ in b_rust:
        if family not in ("per-production", "per-symbol"):
            rust_source[family] += code

    prism_source = dict.fromkeys(SOURCE_BUCKETS, 0)
    for _, family, _, code, _, _, _ in b_prism:
        prism_source[family] += code
    if sum(rust_source.values()) != r_sym:
        sys.exit("Rust source buckets do not sum to R_sym")
    if sum(prism_source.values()) != h_sym:
        sys.exit("Prism source buckets do not sum to H_sym")

    rust_family = allocate_reach(rust_source)
    prism_family = allocate_reach(prism_source)
    if sum(rust_family.values()) != r_sym or sum(prism_family.values()) != h_sym:
        sys.exit("four-family allocation does not sum to global ledgers")
    expected_rust_family = {
        "types": Fraction(1_921, 4),
        "patterns": Fraction(717, 4),
        "exprs": Fraction(3_427, 4),
        "decls": Fraction(2_699, 4),
    }
    expected_prism_family = {
        "types": Fraction(805),
        "patterns": Fraction(584),
        "exprs": Fraction(2_273),
        "decls": Fraction(3_095),
    }
    if rust_family != expected_rust_family:
        sys.exit(f"Rust reach allocation drifted: {rust_family}")
    if prism_family != expected_prism_family:
        sys.exit(f"Prism reach allocation drifted: {prism_family}")

    replacement_rows = []
    output_family_code: dict[str, int] = {}
    output_family_bytes: dict[str, int] = {}
    replacement_paths: list[str] = []
    for family in FAMILIES:
        paths = GENERATED_REPLACEMENT_PATHS[family]
        code = size = 0
        oids = []
        for path in paths:
            _, path_code, path_size, oid = file_receipt(path)
            code += path_code
            size += path_size
            oids.append(oid)
            replacement_paths.append(path)
        replacement_rows.append(
            (family, "<br>".join(paths), code, size, "<br>".join(oids))
        )
        output_family_code[family] = code
        output_family_bytes[family] = size
    if tuple(sorted(replacement_paths)) != EXPECTED_GENERATED_REPLACEMENT:
        sys.exit("generated replacement path set is not the frozen six-file set")

    whole_output_code = sum(output_family_code.values())
    whole_output_bytes = sum(output_family_bytes.values())

    total_gate = min(TOTAL_CAP, int(TOTAL_REDUCTION * h_sym))
    lines_gate = int(OUTPUT_EXPANSION * whole_output_code)
    bytes_gate = int(OUTPUT_EXPANSION * whole_output_bytes)

    out: list[str] = [
        "# Parser compaction baseline",
        "",
        "<!-- Generated by scripts/parser_baseline.py. Regenerate with "
        "`just parser-baseline`; `--check` fails on drift. -->",
        "",
        f"Frozen oracle commit: `{ORACLE_COMMIT}`. Every measured byte is read "
        "from that commit's Git blob, never from `HEAD` or the worktree; each "
        "row records its blob OID. Code lines are nonempty lines whose stripped "
        "form does not start with `//` (Rust/LALRPOP) or `--` (Prism). Raw is "
        "every line; bytes are UTF-8 blob bytes.",
        "",
        "## Ledger A: exact scoreboard continuity boundary",
        "",
        "Frozen scoreboard specs: Rust `crates/prism-syntax/src/grammar.lalrpop`, "
        "`crates/prism-syntax/src/sugar.rs`; Prism "
        "`lib/std/Syntax/Parse.pr`, `lib/std/Syntax/Parse/*.pr`. Their exact "
        "oracle-tree expansion is:",
        "",
        table(
            ["side", "file", "raw", "code", "blob OID"],
            [("rust", p, raw, code, oid) for p, raw, code, _, oid in a_rust]
            + [("prism", p, raw, code, oid)
               for p, raw, code, _, oid in a_prism],
        ),
        "",
        f"Ledger A totals: Rust {a_rust_code:,} code lines, Prism "
        f"{a_prism_code:,}, ratio {a_prism_code / a_rust_code:.2f}. The "
        "recorded handwritten verdict remains FAILED against the pre-registered "
        "0.50 stretch. Ledger A is historical and gates nothing.",
        "",
        "## Ledger B: symmetric transitive experiment",
        "",
        "Included paths are deduplicated. `coeffect.rs` is deliberately present "
        "once despite two reachable edges: the Rust Type grammar calls "
        "`CoeffectRow::new`, and `sugar.rs::lift_noalloc` calls "
        "`CoeffectRow::is_noalloc_only`; the handwritten Prism Type parser "
        "contains the corresponding validation. For conservative, reproducible "
        "whole-file accounting, all 250 code lines are credited to Rust Type, "
        "including non-parser methods and tests. This weakens the practical and "
        "Type-local gates only; the fixed 4,872 total-solution cap remains "
        "controlling and receives no such credit.",
        "",
        table(
            ["side", "file", "source bucket", "raw", "code", "bytes",
             "blob OID", "reason"],
            [("rust", p, fam, raw, code, size, oid, reason)
             for p, fam, raw, code, size, oid, reason in b_rust]
            + [("prism", p, fam, raw, code, size, oid, reason)
               for p, fam, raw, code, size, oid, reason in b_prism],
        ),
        "",
        "The dependency inventory below is exhaustive for in-tree modules named "
        "by `grammar.lalrpop` and `sugar.rs`, plus the transitive "
        "`CoeffectRow::new` edge. Included and excluded edges are both explicit; "
        "the oracle scan fails if that frozen inventory is incomplete. Later "
        "experiment sources require their own provenance/classification manifest; "
        "they do not mutate this historical receipt.",
        "",
        table(
            ["source", "target", "disposition", "family/owner", "evidence"],
            list(RUST_DEPENDENCY_EDGES),
        ),
        "",
        "Prism exclusions:",
        "",
        table(["path", "reason"], list(LEDGER_B_PRISM_EXCLUDE)),
        "",
        "## Coverage proofs",
        "",
        f"The grammar scanner recognizes generic and `pub` heads and found "
        f"exactly {len(productions)} classified top-level productions. The "
        f"sugar scanner found exactly {len(sugar_symbols)} classified top-level "
        "definitions across constants, enums, and functions (including "
        "`const fn with_sentinel`). The frozen names are:",
        "",
        f"- Grammar ({len(productions)}): " + ", ".join(f"`{x}`" for x in productions),
        "",
        f"- Sugar ({len(sugar_symbols)}): " + ", ".join(f"`{x}`" for x in sugar_symbols),
        "",
        "## Symbols and hard gates",
        "",
        table(
            ["symbol", "definition", "value"],
            [
                ("`R_sym`", "all included Rust Ledger-B code lines", f"{r_sym:,}"),
                ("`H_sym`", "all included handwritten Prism Ledger-B code lines",
                 f"{h_sym:,}"),
                ("`G_sym`", "maintained generated arm, excluding the generator",
                 "unmeasured"),
                ("`T_sym`", "`G_sym` plus parser-specific generator until reuse",
                 "unmeasured"),
            ],
        ),
        "",
        table(
            ["gate", "formula", "evaluated"],
            [
                ("practical maintained", "`G_sym / R_sym <= 1.00`",
                 f"`G_sym <= {r_sym:,}`"),
                ("total solution",
                 "`T_sym <= min(4,872, floor(0.75 * H_sym))`",
                 f"`T_sym <= {total_gate:,}`"),
                ("continuity stretch (non-blocking)",
                 "Ledger-A generated maintained / Ledger-A Rust `<= 0.50`",
                 f"`<= {a_rust_code // 2:,}` lines"),
                ("generated output lines",
                 "`generated lines <= floor(1.10 * handwritten lines)`",
                 f"`<= {lines_gate:,}` lines"),
                ("generated output bytes",
                 "`generated bytes <= floor(1.10 * handwritten bytes)`",
                 f"`<= {bytes_gate:,}` bytes"),
            ],
        ),
        "",
        "## Four-family allocation",
        "",
        "There is no `shared` pseudo-family budget or proportional residual. "
        "Every source unit has a frozen, nonempty `Reach(u)` set and contributes "
        "exactly `1 / |Reach(u)|` to each reached family. Fractions are preserved "
        "rather than rounded.",
        "",
        "The reach rules are:",
        "",
        "- `Comma`, grammar and sugar preambles, Rust driver and fault code, and "
        "Prism Parse/Support/Cursor reach all four families.",
        "- `CommaPlus` and Prism Build reach Pattern+Expr.",
        "- Grammar Param/Params and sugar param/params reach Expr+Decl.",
        "- Program, GivenClause/ConstraintP, and `lift_noalloc` reach Decl.",
        "- TypeSig and coeffect reach Type.",
        "- Expr reaches Expr.",
        "",
        "Every other production, symbol, or file has one named family.",
        "",
        table(
            ["source bucket", "Reach(u)", "Rust units", "Prism units"],
            [
                (
                    bucket,
                    ", ".join(BUCKET_REACH[bucket]),
                    rust_source[bucket],
                    prism_source[bucket],
                )
                for bucket in SOURCE_BUCKETS
            ],
        ),
        "",
        table(
            ["family", "Rust exact total", "integer maintained cap",
             "Prism exact total", "ratio"],
            [
                (
                    family,
                    format_fraction(rust_family[family]),
                    int(rust_family[family]),
                    format_fraction(prism_family[family]),
                    f"{float(prism_family[family] / rust_family[family]):.2f}",
                )
                for family in FAMILIES
            ],
        ),
        "",
        f"Exact sums: Rust `{format_fraction(sum(rust_family.values()))} = R_sym`; "
        f"Prism `{format_fraction(sum(prism_family.values()))} = H_sym`. A "
        "complete-family maintained "
        "slice must fit its Rust total and cannot borrow from another family. "
        "A vertical subset cannot claim the whole Expr or Decl budget: until a "
        "frozen per-production subset denominator exists, its size is reported "
        "but non-gating.",
        "",
        "## Generated replacement baseline",
        "",
        "The generated output comparison replaces exactly the six derived "
        "family modules below. `Parse.pr`, `Parse/Support.pr`, "
        "`Parse/Build.pr`, and `Cursor.pr` remain maintained parser/runtime "
        "source: they count in `G_sym`/`T_sym` but are not generated output and "
        "cannot enlarge these caps. The future numerator includes every emitted "
        "Prism source file transitively used by the generated parser regardless "
        "of path, including new `Generated/*` files or emitted code moved into "
        "Support/Build/Cursor. Generation must emit a provenance manifest, new "
        "paths fail until classified, and mixed generated/handwritten files are "
        "forbidden; retained handwritten support remains outside this output "
        "numerator while still counting in `G_sym`/`T_sym`.",
        "",
        table(
            ["source bucket", "exact paths", "code lines", "bytes", "blob OIDs"],
            replacement_rows,
        ),
        "",
        table(
            ["family", "baseline lines", "floor(1.10x)", "baseline bytes",
             "floor(1.10x)"],
            [
                (
                    family,
                    output_family_code[family],
                    int(OUTPUT_EXPANSION * output_family_code[family]),
                    output_family_bytes[family],
                    int(OUTPUT_EXPANSION * output_family_bytes[family]),
                )
                for family in FAMILIES
            ]
            + [(
                "whole parser",
                whole_output_code,
                lines_gate,
                whole_output_bytes,
                bytes_gate,
            )],
        ),
        "",
    ]
    return "\n".join(out)


def main() -> None:
    document = render()
    if "--check" in sys.argv:
        current = OUT.read_text() if OUT.exists() else ""
        if current != document:
            sys.exit(
                f"{OUT.relative_to(ROOT)} is stale; run `just parser-baseline`"
            )
        print(f"{OUT.relative_to(ROOT)} is current")
        return
    OUT.write_text(document)
    print(f"wrote {OUT.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
