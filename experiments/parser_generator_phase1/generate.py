#!/usr/bin/env python3
"""Deterministic phase-1 parser-generator analysis for Prism's frozen grammar.

This is deliberately a bootstrap tool, not a replacement parser generator.  It
turns the frozen LALRPOP grammar into a validated EBNF IR, checks the production
manifest, computes nullable/FIRST facts for every concrete generic
instantiation, validates direct-token predictive selections, and emits the
typed Type-family parser.
"""

from __future__ import annotations

import argparse
import ast
import hashlib
import json
import re
import subprocess
import sys
from collections import deque
from dataclasses import dataclass, field, replace
from enum import Enum
from pathlib import Path
from typing import Callable, Iterable, Iterator, Mapping, Sequence


ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
MANIFEST_PATH = ROOT / "docs/internal/PARSER_PRODUCTION_MANIFEST.json"
FROZEN_STORE = HERE / "frozen"
GRAMMAR_PATH = "crates/prism-syntax/src/grammar.lalrpop"
PLAN_PATH = HERE / "generated/plan.json"
ACTION_SCHEMA_PATH = HERE / "generated/action_schema.json"
TYPE_LEAF_PROJECT = HERE / "generated/type_leaf"
TYPE_LEAF_PATH = TYPE_LEAF_PROJECT / "src/GeneratedTypeLeaf.pr"
TYPE_LEAF_CONTROL_PATH = TYPE_LEAF_PROJECT / "src/GeneratedControl.pr"
PRODUCTION_TYPE_PATH = ROOT / "lib/std/Syntax/Parse/GeneratedType.pr"
SHARED_RUNTIME_PATH = ROOT / "lib/std/Syntax/Parse/GeneratedControl.pr"
PRODUCTION_CONTROL_PATH = SHARED_RUNTIME_PATH
PRODUCTION_PATTERN_PATH = ROOT / "lib/std/Syntax/Parse/GeneratedPattern.pr"
PRODUCTION_TYPE_CONSUMER = ROOT / "lib/std/Syntax/Parse/Type.pr"
PRODUCTION_PATTERN_CONSUMER = ROOT / "lib/std/Syntax/Parse/Pattern.pr"
TYPE_SEMANTICS_PATH = ROOT / "lib/std/Syntax/Parse/TypeSemantics.pr"
PATTERN_SEMANTICS_PATH = ROOT / "lib/std/Syntax/Parse/PatternSemantics.pr"
TYPE_LEAF_MAIN_PATH = TYPE_LEAF_PROJECT / "src/main.pr"
TYPE_LEAF_TEST_PATH = TYPE_LEAF_PROJECT / "tests/type_leaf.pr"
PATTERN_CONTRACT_PATH = TYPE_LEAF_PROJECT / "tests/pattern_contract.pr"
TYPE_LEAF_MANIFEST_PATH = TYPE_LEAF_PROJECT / "prism.toml"

ALLOWED_CLASSES = {"predictive", "Pratt", "escaped"}
ALLOWED_OWNERS = {"shared", "types", "patterns", "exprs", "decls"}
ALLOWED_EFFECTS = {"cursor", "fault", "span", "synth", "value"}
ALLOWED_DEPTH_ENTRIES = {"spend", "nonspend"}
ALLOWED_DEPTH_SHAPES = {
    "child-spends",
    "leaf",
    "mixed",
    "self-spends",
    "siblings-nonspending",
}
PRODUCTION_FIELDS = {
    "class",
    "consumers",
    "cuts",
    "decision",
    "depth",
    "handwritten",
    "hooks",
    "line",
    "name",
    "owner",
}
REQUIRED_PRODUCTION_FIELDS = PRODUCTION_FIELDS - {"consumers"}


class GeneratorError(RuntimeError):
    """A deterministic input or validation failure."""


def fail(message: str) -> None:
    raise GeneratorError(message)


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def stable_json(value: object, *, pretty: bool = False) -> str:
    if pretty:
        return json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
    return json.dumps(value, separators=(",", ":"), sort_keys=True, ensure_ascii=False)


# The generated `.pr` files are committed, so `prism fmt --check` holds them to
# the same canonical layout as every other source file in the tree. Emitting
# anything else makes the two gates contradict each other: whichever one is
# satisfied leaves the other reporting drift. Canonicalizing here, before the
# line accounting reads the text, also keeps the generator's budget measured in
# the same units as the hand-written baseline it is judged against.
PRISM_BINARIES = (ROOT / "target/release/prism", ROOT / "target/debug/prism")


def canonical_pr(text: str) -> str:
    binary = next((p for p in PRISM_BINARIES if p.is_file()), None)
    if binary is None:
        fail(
            "generating Prism sources needs a built compiler to canonicalize "
            "them; run `cargo build` first"
        )
    result = subprocess.run(
        [str(binary), "fmt", "-"],
        input=text,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    if result.returncode != 0:
        fail(f"generated source did not format: {result.stderr.strip()}")
    return result.stdout


def code_lines(text: str, comment_prefix: str) -> int:
    return sum(
        bool(line.strip()) and not line.strip().startswith(comment_prefix)
        for line in text.splitlines()
    )


def blob_oid(data: bytes) -> str:
    """The git blob OID of `data`, computed without git.

    Same construction git uses, so the value is comparable to the OIDs the
    manifest pins, and it stays available in a shallow clone or a source
    tarball.
    """
    header = f"blob {len(data)}\0".encode("utf-8")
    return hashlib.sha1(header + data, usedforsecurity=False).hexdigest()


def read_frozen_blob(oid: str, path: str) -> str:
    """Read a pinned oracle source from the vendored store.

    The oracle is a commit on a pre-release branch, so it cannot be fetched
    from the published history, which carries one squashed commit per release.
    The blobs are vendored instead, each named by its own OID: re-hashing the
    bytes and comparing against the filename is the integrity check, and it is
    the same guarantee `git show <oracle>:<path>` used to give.
    """
    blob = FROZEN_STORE / oid
    if not blob.is_file():
        fail(f"frozen blob for {path} is missing: {blob.relative_to(ROOT)}")
    data = blob.read_bytes()
    actual = blob_oid(data)
    if actual != oid:
        fail(f"frozen blob for {path} hashes to {actual}, not {oid}")
    return data.decode("utf-8")


@dataclass(frozen=True)
class Node:
    """A normalized RHS expression."""

    kind: str
    value: str | None = None
    children: tuple["Node", ...] = ()
    args: tuple["Node", ...] = ()
    label: str | None = None
    mutable: bool = False

    def as_dict(self) -> dict[str, object]:
        result: dict[str, object] = {"kind": self.kind}
        if self.value is not None:
            result["value"] = self.value
        if self.label is not None:
            result["label"] = self.label
        if self.mutable:
            result["mutable"] = True
        if self.args:
            result["args"] = [arg.as_dict() for arg in self.args]
        if self.children:
            result["children"] = [child.as_dict() for child in self.children]
        return result


@dataclass(frozen=True)
class Identifier:
    value: str


@dataclass(frozen=True)
class ModuleRef:
    name: Identifier


@dataclass(frozen=True)
class TokenWire:
    value: str


class PatternAction(Enum):
    IDENTITY = "identity"
    CTOR = "ctor"
    TUPLE = "tuple"
    OR = "or"
    RECORD = "record"
    FIELDS = "fields"
    FIELD = "field"
    NAME = "name"
    NUMBER = "number"
    CHAR = "char"
    BOOL = "bool"
    LIST = "list"
    ARGS = "args"


class ActionFlag(Enum):
    NEGATIVE = "negative"
    TRUE = "true"
    FALSE = "false"
    SPREAD = "spread"
    EMPTY = "empty"
    INTEGER = "integer"
    FLOATING = "floating"


class OperandRole(Enum):
    START = "start"
    END = "end"
    TOKEN = "token"
    CHILD = "child"
    OPTIONAL = "optional"
    REPEAT = "repeat"
    STATIC = "static"


@dataclass(frozen=True)
class OperandRef:
    role: OperandRole
    name: Identifier


@dataclass(frozen=True)
class ActionRef:
    op: PatternAction
    operands: tuple[OperandRef, ...]
    flags: tuple[ActionFlag, ...] = ()
    tokens: tuple[TokenWire, ...] = ()


class PatternCompletion(Enum):
    ARGS = "args"
    BARE_QUAL_OR_PLAIN = "bare-qual-or-plain"
    BARE_UID_OR_PLAIN = "bare-uid-or-plain"
    FIELD_EXPLICIT = "field-explicit"
    FIELD_SHORTHAND = "field-shorthand"
    LET_CLOSED = "let-closed"
    LET_NAMED_OR_CLOSED = "let-named-or-closed"
    PLAIN = "plain"
    PRESERVE_CHILD = "preserve-child"
    PRESERVE_LAST = "preserve-last"
    RECORD_CLOSED = "record-closed"
    RECORD_SPREAD = "record-spread"


@dataclass(frozen=True)
class CompletionRef:
    op: PatternCompletion


class PatternResult(Enum):
    PATTERN = "pattern"
    LET = "let"
    FIELDS = "fields"
    FIELD = "field"
    ARGS = "args"


class ControlOp(Enum):
    EPSILON = "epsilon"
    TAKE = "take"
    CALL = "call"
    SEQ = "seq"
    OPTIONAL = "optional"
    REPEAT = "repeat"
    CAPTURE = "capture"
    MARKER = "marker"
    GROUP = "group"
    DISPATCH = "dispatch"
    DELIMITED = "delimited"
    COMPLETE = "complete"
    ACTION = "action"


@dataclass(frozen=True)
class ControlNode:
    op: ControlOp
    children: tuple["ControlNode", ...] = ()
    token: TokenWire | None = None
    target: Identifier | None = None
    label: Identifier | None = None
    minimum: int = 0
    separator: TokenWire | None = None
    close: TokenWire | None = None
    wrong_close: TokenWire | None = None
    trailing: bool = False
    recovery: Identifier | None = None


def lower_rhs_control(node: Node) -> ControlNode:
    """Lower normalized grammar RHS data into the family-neutral control IR."""
    children = tuple(lower_rhs_control(child) for child in node.children)
    if node.kind == "terminal":
        return ControlNode(ControlOp.TAKE, token=TokenWire(node.value or ""))
    if node.kind == "reference":
        return ControlNode(ControlOp.CALL,
                           tuple(lower_rhs_control(arg) for arg in node.args),
                           target=Identifier(node.value or ""))
    operations = {
        "epsilon": ControlOp.EPSILON, "sequence": ControlOp.SEQ,
        "optional": ControlOp.OPTIONAL, "zero_or_more": ControlOp.REPEAT,
        "one_or_more": ControlOp.REPEAT, "capture": ControlOp.CAPTURE,
        "marker": ControlOp.MARKER, "group": ControlOp.GROUP,
    }
    if node.kind not in operations:
        fail(f"cannot lower RHS node kind {node.kind!r} to control IR")
    return ControlNode(
        operations[node.kind], children,
        token=TokenWire(node.value) if node.kind == "marker" and node.value else None,
        label=Identifier(node.label) if node.label else None,
        minimum=1 if node.kind == "one_or_more" else 0,
    )


def walk_control(node: ControlNode) -> Iterator[ControlNode]:
    yield node
    for child in node.children:
        yield from walk_control(child)


def first_token_wires(node: ControlNode) -> tuple[TokenWire, ...]:
    if node.op is ControlOp.TAKE:
        return (node.token,) if node.token else ()
    if node.op in {ControlOp.CAPTURE, ControlOp.GROUP}:
        return first_token_wires(node.children[0])
    if node.op is ControlOp.SEQ:
        for child in node.children:
            wires = first_token_wires(child)
            if wires:
                return wires
        return ()
    if node.op in {ControlOp.OPTIONAL, ControlOp.REPEAT}:
        return first_token_wires(node.children[0])
    return ()


@dataclass(frozen=True)
class PatternControlSpec:
    production: Identifier
    result: PatternResult
    spend: bool
    alternatives: tuple[ControlNode, ...]
    actions: tuple[ActionRef, ...]
    completions: tuple[CompletionRef, ...]


@dataclass(frozen=True)
class PatternReceiptSpec:
    receipt: Identifier
    menu: tuple[TokenWire, ...]


@dataclass(frozen=True)
class PatternPhaseSpec:
    name: Identifier
    item: Identifier
    mode: Identifier
    close: TokenWire
    wrong_close: TokenWire | None
    recovery: Identifier


@dataclass(frozen=True)
class PatternModuleSpec:
    imports: tuple[ModuleRef, ...]
    controls: tuple[PatternControlSpec, ...]
    receipt_menus: tuple[PatternReceiptSpec, ...]
    suppression: tuple[TokenWire, ...]
    phases: tuple[PatternPhaseSpec, ...]


GENERATED_PATTERN_SPEC = PatternModuleSpec((), (), (), (), ())


def seq_node(nodes: Iterable[Node]) -> Node:
    items = tuple(nodes)
    if not items:
        return Node("epsilon")
    if len(items) == 1:
        return items[0]
    return Node("sequence", children=items)


@dataclass(frozen=True)
class Lexeme:
    kind: str
    value: str
    offset: int


def lex_rhs(text: str) -> list[Lexeme]:
    tokens: list[Lexeme] = []
    i = 0
    while i < len(text):
        ch = text[i]
        if ch.isspace():
            i += 1
            continue
        if text.startswith("//", i):
            end = text.find("\n", i + 2)
            i = len(text) if end < 0 else end + 1
            continue
        if text.startswith("/*", i):
            depth = 1
            j = i + 2
            while j < len(text) and depth:
                if text.startswith("/*", j):
                    depth += 1
                    j += 2
                elif text.startswith("*/", j):
                    depth -= 1
                    j += 2
                else:
                    j += 1
            if depth:
                fail(f"unterminated block comment in RHS at byte {i}")
            i = j
            continue
        if ch == '"':
            j = i + 1
            escaped = False
            while j < len(text):
                if escaped:
                    escaped = False
                elif text[j] == "\\":
                    escaped = True
                elif text[j] == '"':
                    break
                j += 1
            if j >= len(text):
                fail(f"unterminated terminal string in RHS at byte {i}")
            raw = text[i : j + 1]
            try:
                value = ast.literal_eval(raw)
            except (SyntaxError, ValueError) as exc:
                fail(f"invalid terminal literal {raw!r}: {exc}")
            tokens.append(Lexeme("string", value, i))
            i = j + 1
            continue
        if ch == "@":
            match = re.match(r"@[A-Za-z_][A-Za-z0-9_]*", text[i:])
            if not match:
                fail(f"invalid location marker at byte {i}: {text[i:i + 16]!r}")
            value = match.group(0)
            tokens.append(Lexeme("marker", value, i))
            i += len(value)
            continue
        if ch.isalpha() or ch == "_":
            match = re.match(r"[A-Za-z_][A-Za-z0-9_]*", text[i:])
            assert match is not None
            value = match.group(0)
            tokens.append(Lexeme("ident", value, i))
            i += len(value)
            continue
        if ch in "<>()?:*+,":
            tokens.append(Lexeme(ch, ch, i))
            i += 1
            continue
        fail(f"unrecognized RHS character {ch!r} at byte {i} in {text!r}")
    tokens.append(Lexeme("eof", "", len(text)))
    return tokens


class RhsParser:
    def __init__(self, text: str):
        self.text = text
        self.tokens = lex_rhs(text)
        self.pos = 0

    def current(self) -> Lexeme:
        return self.tokens[self.pos]

    def take(self, kind: str) -> Lexeme:
        token = self.current()
        if token.kind != kind:
            fail(
                f"expected {kind!r}, found {token.kind!r} at byte {token.offset} "
                f"in RHS {self.text!r}"
            )
        self.pos += 1
        return token

    def maybe(self, kind: str) -> Lexeme | None:
        if self.current().kind != kind:
            return None
        return self.take(kind)

    def parse(self) -> Node:
        result = self.parse_sequence({"eof"})
        self.take("eof")
        return result

    def parse_sequence(self, stops: set[str]) -> Node:
        children: list[Node] = []
        while self.current().kind not in stops:
            children.append(self.parse_postfix())
        return seq_node(children)

    def parse_postfix(self) -> Node:
        node = self.parse_primary()
        token = self.current()
        if token.kind in {"?", "*", "+"}:
            self.pos += 1
            kind = {"?": "optional", "*": "zero_or_more", "+": "one_or_more"}[token.kind]
            node = Node(kind, children=(node,))
        return node

    def parse_primary(self) -> Node:
        token = self.current()
        if token.kind == "string":
            self.pos += 1
            return Node("terminal", value=token.value)
        if token.kind == "marker":
            self.pos += 1
            return Node("marker", value=token.value)
        if token.kind == "ident":
            self.pos += 1
            args: list[Node] = []
            # Generic application is lexically adjacent (`Comma<T>`). A
            # following capture such as `DimTail <r:@R>` is a new sequence
            # element, not an argument list.
            if (
                self.current().kind == "<"
                and self.current().offset == token.offset + len(token.value)
            ):
                self.take("<")
                while True:
                    args.append(self.parse_sequence({",", ">"}))
                    if not self.maybe(","):
                        break
                self.take(">")
            return Node("reference", value=token.value, args=tuple(args))
        if token.kind == "(":
            self.pos += 1
            child = self.parse_sequence({")"})
            self.take(")")
            if child.kind == "epsilon":
                return child
            return Node("group", children=(child,))
        if token.kind == "<":
            self.pos += 1
            mutable = self.maybe("ident")
            is_mut = mutable is not None and mutable.value == "mut"
            if mutable is not None and not is_mut:
                self.pos -= 1
            label: str | None = None
            if self.current().kind == "ident" and self.tokens[self.pos + 1].kind == ":":
                label = self.take("ident").value
                self.take(":")
            child = self.parse_sequence({">"})
            self.take(">")
            return Node("capture", children=(child,), label=label, mutable=is_mut)
        fail(
            f"unexpected {token.kind!r} at byte {token.offset} "
            f"in RHS {self.text!r}"
        )


@dataclass
class Alternative:
    rhs_text: str
    rhs: Node
    action: str
    checked: bool


@dataclass
class Production:
    name: str
    params: tuple[str, ...]
    result_type: str
    public: bool
    line: int
    alternatives: list[Alternative]
    action_text: str
    manifest: dict[str, object]


@dataclass(frozen=True)
class ActionSpec:
    """One typed lowering row pinned to a frozen grammar alternative."""

    production: str
    alternative: int
    rhs_sha256: str
    action_sha256: str
    token_kind: str
    token_wire: str
    lowering_kind: str
    target_value: str
    completion: str
    hook: str

    def as_dict(self, rhs: str, action_source: str) -> dict[str, object]:
        return {
            "action": {
                "kind": self.lowering_kind,
                "source": action_source,
                "source_sha256": self.action_sha256,
                "target_value": self.target_value,
            },
            "alternative": self.alternative,
            "completion": self.completion,
            "hook": self.hook or None,
            "production": self.production,
            "rhs": rhs,
            "rhs_sha256": self.rhs_sha256,
            "token": {"kind": self.token_kind, "wire": self.token_wire},
        }


@dataclass(frozen=True)
class HelperSpec:
    """One typed factored-child row pinned to its frozen production."""

    production: str
    rhs_sha256: str
    action_sha256: str
    lowering_kind: str
    instances: tuple[str, ...]

    def as_dict(self, rhs: str, action_source: str) -> dict[str, object]:
        return {
            "action_source": action_source,
            "action_sha256": self.action_sha256,
            "instances": list(self.instances),
            "lowering": self.lowering_kind,
            "production": self.production,
            "rhs": rhs,
            "rhs_sha256": self.rhs_sha256,
        }


def pin_digest(label: str, value: object) -> str:
    if not isinstance(value, str) or re.fullmatch(r"[0-9a-f]{64}", value) is None:
        fail(f"{label} must be one lowercase 64-hex SHA-256 digest")
    return value


def action_row(
    production: object, alternative: object, rhs_sha256: object,
    action_sha256: object, token_kind: object, token_wire: object,
    lowering_kind: object, target_value: object, completion: object,
    hook: object = "",
) -> ActionSpec:
    if (
        not isinstance(production, str) or not production
        or not isinstance(alternative, int) or isinstance(alternative, bool)
        or alternative < 0
    ):
        fail("action row requires a production and nonnegative integer alternative")
    strings = (token_kind, token_wire, lowering_kind, target_value, completion, hook)
    if any(not isinstance(value, str) or not value for value in strings[:-1]):
        fail(f"{production}[{alternative}] action row has an empty/non-string column")
    if not isinstance(hook, str):
        fail(f"{production}[{alternative}] hook must be a string")
    return ActionSpec(
        production, alternative, pin_digest("RHS pin", rhs_sha256),
        pin_digest("action pin", action_sha256), token_kind, token_wire,
        lowering_kind, target_value, completion, hook,
    )


def helper_row(
    production: object, rhs_sha256: object, action_sha256: object,
    lowering_kind: object, instances: object,
) -> HelperSpec:
    if not isinstance(production, str) or not production:
        fail("helper row requires a production")
    if not isinstance(lowering_kind, str) or not lowering_kind:
        fail(f"{production} helper lowering must be a nonempty string")
    if (
        not isinstance(instances, tuple)
        or any(not isinstance(item, str) or not item for item in instances)
    ):
        fail(f"{production} helper instances must be a tuple of nonempty strings")
    return HelperSpec(
        production, pin_digest("helper RHS pin", rhs_sha256),
        pin_digest("helper action pin", action_sha256), lowering_kind, instances,
    )


# production, alt, RHS pin, action pin, selector class/wire, lowering, target,
# completion, hook. Frozen RHS/action text is serialized only after validation.
TYPE_LEAF_ACTIONS: tuple[ActionSpec, ...] = (
    action_row("AType", 0, "27c352773b4d52b383c596acf93c7066f46f2828d97b557c578a2603945c8456", "f6dac80b1e5890c0cf45d3f0034447653af84aa325f11690d789e9a4656e2c73", "fixed", "Int", "construct-nullary", "TyInt", "GATPlain"),
    action_row("AType", 1, "b12ca366e6b51b121639e8c182bd5bc5b45672d5663668c3336321e3b352819b", "0cc879939f310e7116d573054545a44c8ee3488e4179dc8c769f1f1e9dbada05", "fixed", "I64", "construct-nullary", "TyI64", "GATPlain"),
    action_row("AType", 2, "37dfb9d82db320c0a924f52e9a073179cf95d821683bf3cf249578ae77c1b274", "8f2c937ed182a72a72dfa66b45de1f0beb8529ce2e89fac3efb6b84155536d2b", "fixed", "U64", "construct-nullary", "TyU64", "GATPlain"),
    action_row("AType", 3, "71c28aab754f8a10f64bfc50b86bbbcd842e0f87403776277a09d2394cd4c999", "97aad09de0c91fa13ee9d4c743f20daef205fa65f89475b9227917403653f9e9", "fixed", "Bool", "construct-nullary", "TyBool", "GATPlain"),
    action_row("AType", 4, "29e2d7a02beb8b5aec022570de02d063e88ec5566f8f6ed572fdbac60fef8508", "b1ac7395a3738b2df32e632c16b8f4a33085e8f2eac4ae52e0ca13b9bc3ba5bf", "fixed", "Unit", "construct-nullary", "TyUnit", "GATPlain"),
    action_row("AType", 5, "2446e184340b489502bf6eea8ecbf352e1e1eec483fb1478cc054fa69858e104", "4c936ab2f99a873fd8dbb729147923b8d9c049f62a67b2c84d0d9acdab9f5d72", "fixed", "Float", "construct-nullary", "TyFloat", "GATPlain"),
    action_row("AType", 6, "3658dee3f7fbf2c2e098282caac65fc546faa03dc1d471cc806041963b3df438", "d83f4a48c5595c78386a38a93793c709091da416bb42773a2e7378749dce3565", "fixed", "Char", "construct-nullary", "TyChar", "GATPlain"),
    action_row("AType", 7, "7d4e7d7755f12ec1b669687786ea1233d301c0dc851cafd67f7ae6ffcde5f4ef", "399c103fa8c6b91918a82b249dcb0213c3ff61a15316cc7161fded60769c7673", "fixed", "String", "construct-nullary", "TyStr", "GATPlain"),
    action_row("AType", 8, "ae3783978cbc6f5522b5f333fb5d8609f3bf47bcdca7235935e60f8dfa8f43a6", "d4cc92268160e522a8d1bc6b6a97dfd9c9e054a0ddd1710058295a0be5772cc5", "fixed", "[", "construct-list", 'TyCon("List", [t])', "GATPlain"),
    action_row("AType", 9, "f9dc7743942893866be94d1fb913fcea92f79757108a8155dd0bfffc1e78e800", "53488815d073619ddd4c09c9cf57add9494151cfab9a490326ceff2b6ba2931f", "kind", "ident", "construct-applied-name", "TyApp(v, args)", "GATPlain"),
    action_row("AType", 10, "956205c76d6b2ebca607c931a888d85c95ed0dffd5e9993d3db2da6ac619fc63", "eed2752879137bcadd40740bb53bde3ff60d1cbf6258a45541c43195c372bbaa", "kind", "ident", "construct-name", "TyVar(v)", "GATNamed"),
    action_row("AType", 11, "d4913715cbd8f5ba62ae96d7ddbcb52812448b472260877113adcb0cee3686c8", "6a5b45c681097bec5cafbfbc98f1b68bd8b0368b4dbf1db53695f36f003ef9ae", "kind", "uid", "construct-optional-constructor", "TyCon(n, args)", "GATNamedOrPlain"),
    action_row("AType", 12, "eb07b17032672687c8e2752b5a3aed3618d2661ccc82181c6561bb91dc9bbdfd", "ab8fb5fe9967bba7425a60ff697125a866a14987cdd17626b9a8e6cd817d6c2b", "kind", "qual", "construct-optional-constructor", "TyCon(q, args)", "GATNamedOrPlain"),
    action_row("AType", 13, "95324034bdb6ac4729dc5ca56ace8fd3d1942ba0cc9886c5cb95eac007540dde", "e3b98a4da31a127d4bde6e43033f66ba274cab0eb7eb1c70ec41402bf6273dd8", "fixed", "(", "identity-parenthesized", "t", "GATPlain"),
    action_row("AType", 14, "3033563a518384fdb5ef1da42c63b539ead6e168c5883f9e8eca3de13b7bb4b3", "13cdc54d60adb743f0a521dabcb4695a911b7df0996dae41f8de15d2757280db", "fixed", "(", "construct-tuple", "TyTuple(ts)", "GATPlain"),
    action_row("AType", 15, "fb3cb7c84f79930286aa409357463f7cfbaaf14092d8c04822a0cc8d9338732f", "40ff13289fa393325f91d0eea0beec7ab35868d8fd11e251427d2fd1333f8c02", "fixed", "#", "construct-unboxed-tuple", "TyUnboxedTuple(ts)", "GATPlain"),
    action_row("AType", 16, "30f80998e2eb660006c1d46a229e8e98920d40a52a022bada760a9c94d180749", "a5b10a5a7d68bf3e946b06367e338e32db787c8e9f2f9ade154ec09e6ef7da01", "fixed", "#", "construct-unboxed-record", "TyUnboxedRecord(fs)", "GATPlain"),
    action_row("DimTerm", 0, "4eae51016934df14a3df522568830b296bf071cc0fb697612f2dd6999b527d35", "2e38e77b22c314a449e91fafed92a43826ac6aa403ae6a8acb6cf58239fbaf5d", "kind", "int", "return-unit", "()", "GTCDimensionNatural"),
    action_row("DimTerm", 1, "9c41367c666943ee997072edcdb2a4244ff63ac3ba9729b99bde52e0b7b80331", "2e38e77b22c314a449e91fafed92a43826ac6aa403ae6a8acb6cf58239fbaf5d", "kind", "ident", "return-unit", "()", "GTCDimensionVariable"),
    action_row("TypeArg", 0, "f729623995653982f10cf77a3952a70f8c317db502ae4c038028bfb756367184", "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", "reference", "Type", "identity-type", "type", "GTAOrdinary"),
    action_row("TypeArg", 1, "55d961539585e4fae149093d13a01b512999be2df393c5a06346b3050293e806", "6b78637c0c62b1ab306074035e94f8e17d9b44bc0b9dbec853f489d87dd3d3af", "fixed", "{", "construct-row-literal", "TyRowLit(row)", "GTARow"),
    action_row("TypeArg", 2, "3ae156cb6020132463a9c08e087526cc9323ff524f232874c445ce589229ea4d", "52db3aeb51c2963e845f48310279f6a48f9684fe09250496b3410da98453ed8a", "kind", "int", "checked-natural", "TyNat(n)", "GTANatural", "typearg-natural"),
    action_row("TypeArg", 3, "ae5d6f9558be9bb8cd4c3fd3f6417183c6ec25f9fd6ae93a38d0d0c652cfdf49", "843ae16f3bf0c6e8307edf99547c529f24be94ab4e1136df530a1b99e9b1e348", "selector", "DimTerm +", "checked-dimension-decline", "PFault(DECLINE_DIM_ARITH)", "GTADimensionFault", "dimension-decline"),
    action_row("DimTail", 0, "991e21c76cc747b4c217b3bf6a063974bb56186264814199033c87efa511f4b3", "2e38e77b22c314a449e91fafed92a43826ac6aa403ae6a8acb6cf58239fbaf5d", "reference", "DimTerm", "dimension-tail", "()", "GTADimensionTail"),
    action_row("DimTail", 1, "044eeedb4c7b5fae36160e2be79d4092d792695315e0d5fe169c369d82819fdc", "2e38e77b22c314a449e91fafed92a43826ac6aa403ae6a8acb6cf58239fbaf5d", "selector", "DimTerm +", "dimension-tail", "()", "GTADimensionTail"),
    action_row("Type", 0, "bd738bf63311908fb88e300e40d0a445c7fc71fb6fa27df7277278ff89484468", "ac8421266ad9a851a44929f996a0b0580d2be5a82559e755340513188f1b5397", "fixed", "forall", "construct-forall", "TyForall", "GTTypeForall"),
    action_row("Type", 1, "d744e9ca2ab489158d069897b29f434c6a042fa8ff52e349d88629c65d76fd57", "b51498b01bc9cbce6ea7b6b1aaca83efc424465fa97a97fffeea6cee4939582f", "reference", "Arrow", "checked-effect-attach", "TyFun", "GTType", "type-effect-attach"),
    action_row("Type", 2, "504aafc6cc013bccfb1f4a1f7353178fe4b3ceddfd6a2e8c6a944e2c750b2e82", "5e8dfe1dfbb852908a244c141486358a7a32c7d40586f57fe3d9392d6b9836e4", "selector", "Arrow ArrowEff @", "checked-effect-attach", "PFault", "GTTypeFault", "type-effect-attach"),
    action_row("Arrow", 0, "e41e45bf021dea83c3bc73f32affc373e0d8349721c5b3e8ddb3a5f8510cd0d7", "4aa36ec4924073925eb16f42e0edce433a65cce4f359a02bd1a4dcd988fa0f3b", "fixed", "(", "construct-empty-arrow", "TyFun", "GTArrow"),
    action_row("Arrow", 1, "38c004a51684bfcb4dc379c0ede8229690b443373d3c4f55a48f4f157f54ae63", "e4ac8b7985fa09ff719c42d4852ef5a579e9e563e936a3b2f9322ffaeb019efa", "reference", "UType", "construct-arrow", "TyFun", "GTArrow"),
    action_row("Arrow", 2, "a55a8007a79711827637f966f73c9da02ce1d4cca3214488989839e72caeb119", "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", "reference", "UType", "identity-type", "type", "GTArrow"),
    action_row("ArrowEff", 0, "fdc94084638909767005b476b032b5b6963550d766fddc3a3858f7fe5a3e195a", "f85d2b5334f819c329ce88e99efd09fe90aad88672e8ef09f4db09243f25863f", "fixed", "!", "construct-effect-row", "Row", "GTEffect"),
    action_row("ArrowEff", 1, "f1a9b0832cca328191be0458c3d85ca8313e615c3b2ec069b188b368028bb68a", "ec24b561bfd5e926b5700a22404144109f2a6a4330bfc3c79e2fe8c1bff3baaf", "fixed", "!", "construct-empty-effect", "Row", "GTEffect"),
    action_row("UType", 0, "1b5e3e864700f423e815dc55e086f563b193275f9c6a2b0227c0b037ccdfddb7", "a0f179b1c99b3a3e763882975c2ee3ce8b5c7ff6ae1e91c3442a5ad0d3129a67", "reference", "AType", "checked-usage-validate", "TyUsage", "GTUsage", "usage-validate"),
    action_row("UType", 1, "9658ab644fc59e7743d938c1e767631f0f8806fe8346f4f7027674dc679a480b", "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", "reference", "AType", "identity-type", "type", "GTUsage"),
    action_row("CoeffRowParts", 0, "2cf0de8b711c6c541e4906b8b158787dbbd8b8e8be59cc67fca1fffec4d9a737", "44b3bae6076d4418bd1ef0990a502b6632fd0d9aa42f5b5eb5f312716e8c43b4", "fixed", "{", "construct-usage-row", "UsageParts", "GTCoeffectRow"),
    action_row("CoeffRowParts", 1, "cd1d0a82edb771ad7101b620cb11d409e615be29b2741e9de9719c6e13f3d498", "0b643ef745d6ec996451f999b6b37a5b3c60570395f65e253705de5d3fbe6069", "kind", "ident", "construct-usage-row", "UsageParts", "GTCoeffectRow"),
    action_row("EffLabel", 0, "f5379c96cba376691683e5bae3a3cb0820fb3bbca75b0fd9e4e85b739d07d5bf", "bead7530221f4c9e2dff3477cae363e471f594185559667e79da179fda9ed04e", "kind", "ident", "construct-effect-label", "EffLabel", "GTEffectLabel"),
    action_row("EffLabel", 1, "e00173be4fdc332a817020a3e7ef6d1d5b0613e62bab3fdc92f559e7bb6e77dc", "0f092b2038abf1d82951283531319c747035f9504c2ea6a14036f6820197e79e", "kind", "uid", "construct-effect-label", "EffLabel", "GTEffectLabel"),
    action_row("EffLabel", 2, "63c0bf4148d01e16c3601aac77b56c876ae44bffe9463576cc5b06d3c9e2eafe", "0f092b2038abf1d82951283531319c747035f9504c2ea6a14036f6820197e79e", "kind", "qual", "construct-effect-label", "EffLabel", "GTEffectLabel"),
)

PATTERN_ACTIONS: tuple[ActionSpec, ...] = (
    action_row("LetPat", 0, "79c46c9e838441a73c7b96b2fbb7658f29e12f31a4a74f18ed62d73c7df7f347", "66c1e6f8c0f534156d5c9cbe704ffcd92d199004d1bd938d26a4e8599bebbfe1", "kind", "uid", "construct-optional-constructor", "PCtor(n,args)", "GPLetNamedOrClosed"),
    action_row("LetPat", 1, "12521a2f1f9807c119480a96663d48a12df08978298f6a6673f821df77b47d43", "815abe384437783ef77beefd8da390126f40694cb48c745b744df91c193ebfcc", "kind", "qual", "construct-optional-constructor", "PCtor(q,args)", "GPLetNamedOrClosed"),
    action_row("LetPat", 2, "265ddf2d1e3210f49c7c15a6f06b319f446de871f7893dc52514052affe972ae", "a45dfa265959027541f984fbfbe124411d0ee49ccda4769d7a58edc5a9fd4c05", "fixed", "(", "construct-pattern-tuple", "PTuple(ps)", "GPLetClosed"),
    action_row("Pattern", 0, "cba3247ad2fd0a83eed51881ae93421999a38b95debc850564d7f21f8403b3ca", "fa3ecda68df0ff728aa5789c3b7ab93c8f1d0afb7387176e909af7f188c17551", "reference", "PatAlt | PatAlt", "construct-pattern-or", "POr(ps)", "GPPreserveLast"),
    action_row("Pattern", 1, "e603d5e05f729d5a5fae8aed3dfa9d14ca05120c338846616224304f4266064d", "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", "reference", "PatAlt", "identity-pattern", "pat", "GPPreserveChild"),
    action_row("PatAlt", 0, "79c46c9e838441a73c7b96b2fbb7658f29e12f31a4a74f18ed62d73c7df7f347", "66c1e6f8c0f534156d5c9cbe704ffcd92d199004d1bd938d26a4e8599bebbfe1", "kind", "uid", "construct-optional-constructor", "PCtor(n,args)", "GPBareUidOrPlain"),
    action_row("PatAlt", 1, "12521a2f1f9807c119480a96663d48a12df08978298f6a6673f821df77b47d43", "815abe384437783ef77beefd8da390126f40694cb48c745b744df91c193ebfcc", "kind", "qual", "construct-optional-constructor", "PCtor(q,args)", "GPBareQualOrPlain"),
    action_row("PatAlt", 2, "15eadf48b4e577031c6e992c2b7d4082add62eb51b685eec79e85beecc1c2a28", "7486139b2de019ca71b4c916103cfee184030020bdae5b0d28c1e73d8884bea0", "selector", "uid {", "construct-pattern-record", "PRecord(n,fields,spread)", "GPPlain"),
    action_row("PatAlt", 3, "bc7a310402d14d3c710aee3546f8b15b5960d1a5d2f240064c86485613e60819", "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", "reference", "PatAtom", "identity-pattern", "pat", "GPPreserveChild"),
    action_row("RecordPatFields", 0, "c16a72b70c10e0992d8ac4795c66603ca8e0a50e98fd01a23157d14afc814c77", "72f47b68d4bda3b2de6bd192c6e3c47560e489b93bee0448763cedb8544d61f5", "selector", "RecordPatField , ..", "construct-pattern-fields", "(fields,true)", "GPRecordSpread"),
    action_row("RecordPatFields", 1, "d487a5ad85a7c76f0a6056321f03e52600ff9e04d1f9579bc56415d9a9cb02c9", "6c96fb8f66f91f2acda2f0e8c4ece6af9dc0b0fa29bf8fbf7dd9cb70dccc96bf", "reference", "Comma<RecordPatField>", "construct-pattern-fields", "(fields,false)", "GPRecordClosed"),
    action_row("RecordPatField", 0, "bd9601c8c22e7fe8e3e7348ee4fea75de72461e6b1cf0d4baee479e4852113a3", "3fc78834e463657a4e64c0a43c1fc9e7c41b7a631ee2336e0a0ae4eb75eebaa8", "selector", "ident =", "construct-pattern-field", "PatField(n,p)", "GPFieldExplicit"),
    action_row("RecordPatField", 1, "f0f8d93c896971fb39aafb797478dfb865e749167df21d11752f15ab328e8cf7", "93fb6f6e35f8ec3fe9d9e23051eaf835b11be56027d70d21049cc6594b3cd608", "kind", "ident", "construct-pattern-field", "PatField(n,PVar(n))", "GPFieldShorthand"),
    action_row("PatAtom", 0, "1bf3ab028ca44d38e36f1171f6facda4d6caed8c182ed3035ba00cf287afef6b", "393174c56b0465010a5be041a28a8b371afb75847dcfaa9f23a986b3379b1ad7", "kind", "ident", "construct-pattern-name", "PWild|PVar(v)", "GPPlain"),
    action_row("PatAtom", 1, "3ae156cb6020132463a9c08e087526cc9323ff524f232874c445ce589229ea4d", "30f3cfdb0d070e05fa93395a2c53e34b71e5834f9508844281be431a09376ea6", "kind", "int", "construct-pattern-int", "PInt(n)", "GPPlain"),
    action_row("PatAtom", 2, "2ad4ea832e58b597bdab8b99851bbdbcd5932a03786ff7519f4043acee4aa31d", "cc160ef519916ad53e5381f1c386162497341c3712ccd7d2a80ba26c7ae7487d", "kind", "float", "construct-pattern-float", "PFloat(f)", "GPPlain"),
    action_row("PatAtom", 3, "8a962b69c1178e09caf6c7d0a83da2bd352819adb15e4fab0362db8d2a75996b", "af28f2ffda86f464484fc2ac9f5027c0a3f033104998838858e698375f8cca94", "selector", "- int", "construct-pattern-int", "PInt(-n)", "GPPlain"),
    action_row("PatAtom", 4, "f069c678f57674f84f553e18f90adbbaa129745f25db68da18291793da3d11b0", "2556a6985670cb5f6df0ef0a93a2313423c69156b57bb3008c7d5f174164905a", "selector", "- float", "construct-pattern-float", "PFloat(-f)", "GPPlain"),
    action_row("PatAtom", 5, "0a652ce8cda36b6ec79edc094a6bd70fbf020de59ef00371ff93d8fad9ed613a", "b8b486090139d81782a731b48b6e136cc476b821c4cb72c7e7af01621ad8af3b", "kind", "char", "construct-pattern-char", "PChar(c)", "GPPlain"),
    action_row("PatAtom", 6, "40a274eb771d0a08bef82314b68f150689ff93dc4bb5cee8b0baaa0b57f7523d", "4042cf4c9ffbd1bb8ed51a3a5e899e2a77e49763622b6a6bf9643bceea83f953", "fixed", "true", "construct-pattern-bool", "PBool(true)", "GPPlain"),
    action_row("PatAtom", 7, "678eab73f76ff75564cedf742840255d214ffa86aeda543c4aaf94f9defa683e", "60b994214051fd1fbbdc244356b2da48a3ca7864fe17a3f6a34d17b7f4fdb681", "fixed", "false", "construct-pattern-bool", "PBool(false)", "GPPlain"),
    action_row("PatAtom", 8, "9dbca0c5c02a6966c31432c68f64a25fc448d10e5980e5ac3b744fafa9184259", "91d24fc9631f090c63ca0f01d6934584e89dc8b1f514985067641907d5354471", "fixed", "[", "construct-pattern-list", "PCtor(Nil)", "GPPlain"),
    action_row("PatAtom", 9, "0a8e19ddafc17b0884f80dbab77daf57663cbd1831d8222590c1b28aefe84c10", "8ceb77a8af64920a72e652dc8649b4ccd91834506c6f131745586af3e623790d", "selector", "[ CommaPlus<Pattern>", "construct-pattern-list", "PCtor(Cons)", "GPPlain"),
    action_row("PatAtom", 10, "265ddf2d1e3210f49c7c15a6f06b319f446de871f7893dc52514052affe972ae", "b7b843aac6d29c1c6ad451f4418effcae50d2632866392004b163395b7e84d03", "fixed", "(", "construct-pattern-tuple", "PTuple(ps)", "GPPlain"),
    action_row("PatArgs", 0, "db67a13a2d937dcbee0ac1b93a7022e342f9cc22502a4ebe1f90489ef0987453", "6527c9361a2f469c5275afcb5d06e53013367cd231995de13dc7218711388382", "fixed", "(", "delimited-pattern-args", "args", "GPArgs"),
)

# production, RHS pin, action pin, lowering, concrete generic instances.
ATYPE_HELPERS: tuple[HelperSpec, ...] = (
    helper_row("CtorArgs", "b7ada90db32c81aa47488e557e9f2680cf29d469b61aec964f2f7ed746776797", "44ad63f60af0f6db6fdde6d5186ef78176367df261fa06be3079b6c80c8adba4", "delimited-comma", ("Comma<TypeArg>",)),
    helper_row("RecordField", "4ed40f265f54e3fdbd63585425af0eef7e194578bd2198d5415ccd913c2b3c85", "d0dddf8e39db2a94a3ac9440242593543766a3b55de392227b5df11691d7da6d", "record-field", ()),
    helper_row("Comma", "25ee51873cc8e878923f228a8bee0d2b23680120433c33082c204d9f27389c1a", "c98858f1840a7da7e61ef47c564d2beec4d308a7b9e1a8724caaba6d8ebded70", "comma-zero-or-more-trailing", ("Comma<EffLabel>", "Comma<Pattern>", "Comma<RecordField>", "Comma<Type>", "Comma<TypeArg>", 'Comma<"ident">')),
)

PATTERN_HELPERS: tuple[HelperSpec, ...] = (
    helper_row("CommaPlus", "eb0619c765d23b529b29d3256721647948c70c2e7a7bcc23964488689c4df115", "901bfd8caeb5c4dca5096f92254f47ff76b926e6b954ed7d3e0a78320c7e688a", "comma-one-or-more-trailing", ("CommaPlus<Pattern>",)),
)

PATTERN_RECEIPT_MENUS = {
    "PRPlain": ("|",),
    "PRBareUid": ("(", "{", "|"),
    "PRBareQual": ("(", "|"),
}
PATTERN_RECEIPT_SUPPRESSION = (":", ":=", "if", "=>", ")", "]", "}")
PATTERN_PHASE_ROWS = {
    "args": ("comma-zero-or-more", ")", "wrong-square-after-local-item"),
    "list": ("comma-one-or-more-or-empty-atom", "]", "wrong-round-after-local-item"),
    "tuple": ("mandatory-first-and-comma", ")", "wrong-square-after-local-item"),
    "record": ("field-comma-or-spread", "}", "shorthand-and-child-receipts"),
}
PATTERN_PHASE_ITEMS = {
    "args": "Pattern", "list": "Pattern", "tuple": "Pattern",
    "record": "RecordPatField",
}
PATTERN_WRONG_CLOSE = {"args": "]", "list": ")", "tuple": "]", "record": ""}

PATTERN_PRODUCTIONS = (
    "LetPat", "Pattern", "PatAlt", "RecordPatFields",
    "RecordPatField", "PatAtom", "PatArgs",
)
PATTERN_ACTION_OPS = {
    "construct-optional-constructor": PatternAction.CTOR,
    "construct-pattern-tuple": PatternAction.TUPLE,
    "construct-pattern-or": PatternAction.OR,
    "construct-pattern-record": PatternAction.RECORD,
    "construct-pattern-fields": PatternAction.FIELDS,
    "construct-pattern-field": PatternAction.FIELD,
    "construct-pattern-name": PatternAction.NAME,
    "construct-pattern-int": PatternAction.NUMBER,
    "construct-pattern-float": PatternAction.NUMBER,
    "construct-pattern-char": PatternAction.CHAR,
    "construct-pattern-bool": PatternAction.BOOL,
    "construct-pattern-list": PatternAction.LIST,
    "delimited-pattern-args": PatternAction.ARGS,
    "identity-pattern": PatternAction.IDENTITY,
}
PATTERN_COMPLETIONS = {
    name: completion for name, completion in zip(
        (
            "GPArgs", "GPBareQualOrPlain", "GPBareUidOrPlain",
            "GPFieldExplicit", "GPFieldShorthand", "GPLetClosed",
            "GPLetNamedOrClosed", "GPPlain", "GPPreserveChild",
            "GPPreserveLast", "GPRecordClosed", "GPRecordSpread",
        ),
        PatternCompletion,
    )
}


def pattern_operand(node: Node) -> OperandRef:
    child = node.children[0]
    role = (
        OperandRole.START if child.kind == "marker" and child.value == "@L"
        else OperandRole.END if child.kind == "marker"
        else OperandRole.TOKEN if child.kind == "terminal"
        else OperandRole.OPTIONAL if child.kind == "optional"
        else OperandRole.REPEAT if child.kind in {"zero_or_more", "one_or_more"}
        else OperandRole.CHILD
    )
    return OperandRef(role, Identifier(node.label or "child"))


def generic_delimited_call(node: ControlNode) -> ControlNode | None:
    if node.op is ControlOp.CALL and node.target and node.target.value in {
        "Comma", "CommaPlus",
    }:
        return node
    if node.op in {ControlOp.CAPTURE, ControlOp.GROUP} and len(node.children) == 1:
        return generic_delimited_call(node.children[0])
    return None


def replace_control(node: ControlNode, old: ControlNode,
                    new: ControlNode) -> ControlNode:
    if node is old:
        return new
    return replace(node, children=tuple(
        replace_control(child, old, new) for child in node.children
    ))


def normalize_pattern_delimited(
    node: ControlNode, phases: tuple[PatternPhaseSpec, ...],
    following: tuple[TokenWire, ...] = (),
    seeded: bool = False,
) -> ControlNode:
    if node.op is ControlOp.SEQ:
        normalized: list[ControlNode] = []
        for index, child in enumerate(node.children):
            suffix = tuple(
                wire for part in node.children[index + 1:]
                for wire in first_token_wires(part)
            ) or following
            call = generic_delimited_call(child)
            item_target = (
                call.children[0].target if call and call.children else None
            )
            has_seed = bool(item_target) and any(
                part.target == item_target
                for prefix in node.children[:index]
                for part in walk_control(prefix)
                if part.op is ControlOp.CALL
            )
            normalized.append(normalize_pattern_delimited(
                child, phases, suffix, has_seed
            ))
        return replace(node, children=tuple(normalized))
    if node.op in {ControlOp.CAPTURE, ControlOp.GROUP}:
        return replace(node, children=tuple(
            normalize_pattern_delimited(child, phases, following, seeded)
            for child in node.children
        ))
    call = generic_delimited_call(node)
    if call is None or not call.children:
        return replace(node, children=tuple(
            normalize_pattern_delimited(child, phases)
            for child in node.children
        ))
    item = call.children[0]
    candidates = tuple(
        phase for phase in phases
        if item.target and phase.item == item.target
        and (not following or phase.close in following)
    )
    if len(candidates) > 1:
        candidates = tuple(
            phase for phase in candidates
            if (phase.mode.value == "mandatory-first-and-comma") == seeded
        )
    if not candidates:
        fail("concrete comma call has no typed Pattern phase")
    phase = candidates[0]
    delimited = ControlNode(
        ControlOp.DELIMITED, (item,), target=call.target,
        minimum=1 if call.target.value == "CommaPlus" else 0,
        separator=TokenWire(","), close=phase.close,
        wrong_close=phase.wrong_close, trailing=True,
        recovery=phase.name,
    )
    return replace_control(node, call, delimited)


def pattern_module_spec(
    productions: Mapping[str, Production],
) -> PatternModuleSpec:
    """Join parsed Pattern RHS graphs to their validated typed action rows."""
    rows = {(row.production, row.alternative): row for row in PATTERN_ACTIONS}
    phases = tuple(PatternPhaseSpec(
        Identifier(name), Identifier(PATTERN_PHASE_ITEMS[name]),
        Identifier(row[0]), TokenWire(row[1]),
        TokenWire(PATTERN_WRONG_CLOSE[name])
        if PATTERN_WRONG_CLOSE[name] else None,
        Identifier(row[2]),
    ) for name, row in PATTERN_PHASE_ROWS.items())
    controls: list[PatternControlSpec] = []
    for name in PATTERN_PRODUCTIONS:
        production = productions[name]
        actions: list[ActionRef] = []
        completions: list[CompletionRef] = []
        for index, alternative in enumerate(production.alternatives):
            row = rows[(name, index)]
            op = PATTERN_ACTION_OPS[row.lowering_kind]
            operands = tuple(pattern_operand(node) for node in walk(alternative.rhs)
                             if node.kind == "capture" and node.label)
            if op is PatternAction.IDENTITY and not operands:
                operands = (OperandRef(OperandRole.CHILD, Identifier("child")),)
            terminal_values = tuple(dict.fromkeys(
                node.value for node in walk(alternative.rhs)
                if node.kind == "terminal" and node.value is not None
            ))
            terminals = set(terminal_values)
            flags = tuple(flag for token, flag in (
                ("-", ActionFlag.NEGATIVE), ("true", ActionFlag.TRUE),
                ("false", ActionFlag.FALSE), ("..", ActionFlag.SPREAD),
                ("int", ActionFlag.INTEGER), ("float", ActionFlag.FLOATING),
            ) if token in terminals)
            has_list_items = any(
                node.kind == "reference" and node.value == "CommaPlus"
                for node in walk(alternative.rhs)
            )
            if op is PatternAction.LIST and not has_list_items:
                flags += (ActionFlag.EMPTY,)
            static = tuple(map(TokenWire, terminal_values))
            actions.append(ActionRef(op, operands, flags, static))
            completions.append(CompletionRef(PATTERN_COMPLETIONS[row.completion]))
        result = (
            PatternResult.LET if any(
                completion.op in {
                    PatternCompletion.LET_CLOSED,
                    PatternCompletion.LET_NAMED_OR_CLOSED,
                } for completion in completions
            )
            else PatternResult.FIELDS if production.result_type.startswith("(Vec")
            else PatternResult.FIELD if production.result_type.startswith("(String")
            else PatternResult.ARGS if production.result_type.startswith("Vec")
            else PatternResult.PATTERN
        )
        controls.append(PatternControlSpec(
            Identifier(name), result,
            production.manifest["depth"]["entry"] == "spend",
            tuple(normalize_pattern_delimited(
                lower_rhs_control(alt.rhs), phases
            ) for alt in production.alternatives),
            tuple(actions), tuple(completions),
        ))
    return PatternModuleSpec(
        tuple(ModuleRef(Identifier(name)) for name in (
            "Data.List", "Syntax.Token", "Syntax.Ast", "Syntax.Cursor",
            "Syntax.Parse.Support", "Syntax.Parse.Build",
            "Syntax.Parse.GeneratedControl", "Syntax.Parse.PatternSemantics",
        )),
        tuple(controls),
        tuple(PatternReceiptSpec(
            Identifier(receipt), tuple(map(TokenWire, menu))
        ) for receipt, menu in PATTERN_RECEIPT_MENUS.items()),
        tuple(map(TokenWire, PATTERN_RECEIPT_SUPPRESSION)),
        phases,
    )

TYPEARG_COMPLETION_SCHEMA = {
    "GTAOrdinary": {
        "default": "preserve-child-receipt",
        "when_entry_is_TIdent_and_child_consumes_exactly_one_token": "TRDimIdent",
    },
    "GTARow": {"target": "TRRow"},
    "GTANatural": {"target": "TRNat"},
    "GTADimensionFault": {"target": "PFault"},
}
TYPE_RECEIPT_MENUS = {
    "TRPlain": ("!", "->", "@"),
    "TRNamed": ("(", "!", "->", "@"),
    "TRUsage": ("!", "->"),
    "TRBareEffect": ("{", "@"),
    "TRClosedEffect": ("@",),
    "TRNat": ("+",),
    "TRRow": (),
    "TRDimIdent": ("(", "!", "->", "@", "+"),
}
TYPE_RECEIPT_ALWAYS_LIVE = ("TRNat", "TRDimIdent")
TYPE_RECEIPT_SUPPRESSION = (
    ("end", ""),
    ("kind", "ident"),
    ("kind", "vsemi"),
    ("kind", "vopen"),
    ("kind", "vclose"),
    *(("fixed", wire) for wire in (
        ":=", "=", ")", "]", "}", ",", "given", "requires", "ensures", "decreases",
    )),
)

# The template is authorized only for this exact typed control/receipt table.
# The last column is the completion transition used by malformed-input menus.
TYPE_SPINE_EXPECTATIONS = (
    ("Type", 0, "fixed", "forall", "construct-forall", "TyForall", "GTTypeForall", "", "preserve-body"),
    ("Type", 1, "reference", "Arrow", "checked-effect-attach", "TyFun", "GTType", "type-effect-attach", "preserve-arrow-or-retag-effect"),
    ("Type", 2, "selector", "Arrow ArrowEff @", "checked-effect-attach", "PFault", "GTTypeFault", "type-effect-attach", "fault-after-complete-usage"),
    ("Arrow", 0, "fixed", "(", "construct-empty-arrow", "TyFun", "GTArrow", "", "preserve-codomain"),
    ("Arrow", 1, "reference", "UType", "construct-arrow", "TyFun", "GTArrow", "", "preserve-codomain"),
    ("Arrow", 2, "reference", "UType", "identity-type", "type", "GTArrow", "", "preserve-utype"),
    ("ArrowEff", 0, "fixed", "!", "construct-effect-row", "Row", "GTEffect", "", "TRClosedEffect"),
    ("ArrowEff", 1, "fixed", "!", "construct-empty-effect", "Row", "GTEffect", "", "TRBareEffect"),
    ("UType", 0, "reference", "AType", "checked-usage-validate", "TyUsage", "GTUsage", "usage-validate", "TRUsage"),
    ("UType", 1, "reference", "AType", "identity-type", "type", "GTUsage", "", "preserve-atype"),
    ("CoeffRowParts", 0, "fixed", "{", "construct-usage-row", "UsageParts", "GTCoeffectRow", "", "usage-parts-preserve-open-tail"),
    ("CoeffRowParts", 1, "kind", "ident", "construct-usage-row", "UsageParts", "GTCoeffectRow", "", "usage-parts-closed"),
    ("EffLabel", 0, "kind", "ident", "construct-effect-label", "EffLabel", "GTEffectLabel", "", "GRClosedItem"),
    ("EffLabel", 1, "kind", "uid", "construct-effect-label", "EffLabel", "GTEffectLabel", "", "GROptionalArgs-or-GRClosedItem"),
    ("EffLabel", 2, "kind", "qual", "construct-effect-label", "EffLabel", "GTEffectLabel", "", "GROptionalArgs-or-GRClosedItem"),
)


def scan_balanced_brace(source: str, opening: int) -> int:
    if source[opening] != "{":
        fail(f"expected opening brace at byte {opening}")
    depth = 0
    for position, ch in iter_code_chars(source[opening:]):
        if ch == "{":
            depth += 1
        elif ch == "}":
            depth -= 1
            if depth == 0:
                return opening + position
    fail(f"unterminated production body starting at byte {opening}")
    raise AssertionError("unreachable")


def iter_code_chars(text: str) -> Iterator[tuple[int, str]]:
    """Yield code characters, replacing strings/comments with whitespace."""

    i = 0
    while i < len(text):
        if text.startswith("//", i):
            end = text.find("\n", i + 2)
            i = len(text) if end < 0 else end
            continue
        if text.startswith("/*", i):
            depth = 1
            i += 2
            while i < len(text) and depth:
                if text.startswith("/*", i):
                    depth += 1
                    i += 2
                elif text.startswith("*/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            continue
        if text[i] in {'"', "'"}:
            quote = text[i]
            i += 1
            escaped = False
            while i < len(text):
                if escaped:
                    escaped = False
                elif text[i] == "\\":
                    escaped = True
                elif text[i] == quote:
                    i += 1
                    break
                i += 1
            continue
        yield i, text[i]
        i += 1


def split_alternatives(body: str) -> list[str]:
    parts: list[str] = []
    start = 0
    paren = bracket = brace = angle = 0
    action = False
    code = list(iter_code_chars(body))
    code_positions = {position: ch for position, ch in code}
    for position, ch in code:
        nxt = code_positions.get(position + 1, "")
        if not action and ch == "=" and nxt == ">" and not any((paren, bracket, brace, angle)):
            action = True
            continue
        if ch == "(":
            paren += 1
        elif ch == ")":
            paren -= 1
        elif ch == "[":
            bracket += 1
        elif ch == "]":
            bracket -= 1
        elif ch == "{":
            brace += 1
        elif ch == "}":
            brace -= 1
        elif not action and ch == "<":
            angle += 1
        elif not action and ch == ">" and code_positions.get(position - 1) != "=":
            angle -= 1
        elif ch == "," and not any((paren, bracket, brace, angle)):
            part = body[start:position].strip()
            if part:
                parts.append(part)
            start = position + 1
            action = False
        if min(paren, bracket, brace, angle) < 0:
            fail(f"unbalanced delimiter while splitting production body near {body[position:position+20]!r}")
    tail = body[start:].strip()
    if tail:
        parts.append(tail)
    if any((paren, bracket, brace, angle)):
        fail(f"unbalanced production body: {body[:120]!r}")
    return parts


def split_action(alternative: str) -> tuple[str, str, bool]:
    paren = bracket = brace = angle = 0
    code_positions = {position: ch for position, ch in iter_code_chars(alternative)}
    for position in sorted(code_positions):
        ch = code_positions[position]
        nxt = code_positions.get(position + 1, "")
        if ch == "=" and nxt == ">" and not any((paren, bracket, brace, angle)):
            checked = code_positions.get(position + 2, "") == "?"
            action_start = position + (3 if checked else 2)
            return alternative[:position].strip(), alternative[action_start:].strip(), checked
        if ch == "(":
            paren += 1
        elif ch == ")":
            paren -= 1
        elif ch == "[":
            bracket += 1
        elif ch == "]":
            bracket -= 1
        elif ch == "{":
            brace += 1
        elif ch == "}":
            brace -= 1
        elif ch == "<":
            angle += 1
        elif ch == ">":
            angle -= 1
    return alternative.strip(), "", False


HEADER = re.compile(
    r"(?P<public>pub\s+)?"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_]*)"
    r"(?:<(?P<params>[^>]*)>)?"
    r"\s*:\s*(?P<result>.*?)\s*=\s*"
)


def parse_productions(
    source: str, manifest_productions: Sequence[dict[str, object]]
) -> dict[str, Production]:
    lines = source.splitlines(keepends=True)
    actual_headers = [
        (match.group(1), source.count("\n", 0, match.start()) + 1)
        for match in re.finditer(
            r"^(?:pub\s+)?([A-Za-z_][A-Za-z0-9_]*)(?:<[^>\n]*>)?\s*:",
            source,
            re.MULTILINE,
        )
    ]
    expected_headers = [
        (str(row["name"]), int(row["line"])) for row in manifest_productions
    ]
    if actual_headers != expected_headers:
        actual_map = dict(actual_headers)
        expected_map = dict(expected_headers)
        missing = sorted(set(actual_map) - set(expected_map))
        extra = sorted(set(expected_map) - set(actual_map))
        moved = sorted(
            name
            for name in set(actual_map) & set(expected_map)
            if actual_map[name] != expected_map[name]
        )
        fail(
            "manifest is not an exact ordered grammar inventory: "
            f"unmanifested={missing}, absent={extra}, line_mismatches={moved}"
        )
    offsets: list[int] = []
    total = 0
    for line in lines:
        offsets.append(total)
        total += len(line)

    result: dict[str, Production] = {}
    for row in manifest_productions:
        line = int(row["line"])
        if line < 1 or line > len(lines):
            fail(f"manifest line out of range for {row['name']}: {line}")
        offset = offsets[line - 1]
        match = HEADER.match(source, offset)
        if match is None:
            fail(f"no production header for {row['name']} at line {line}")
        if match.group("name") != row["name"]:
            fail(
                f"manifest/header name mismatch at line {line}: "
                f"{row['name']} != {match.group('name')}"
            )
        body_start = match.end()
        if source[body_start : body_start + 1] == "{":
            close_brace = scan_balanced_brace(source, body_start)
            body = source[body_start + 1 : close_brace]
        else:
            # LALRPOP also permits a single unbraced alternative terminated by
            # `;` (the frozen PathIndex production uses this form).
            line_end = source.find("\n", body_start)
            statement_end = source.find(";", body_start, None if line_end < 0 else line_end)
            if statement_end < 0:
                fail(f"unbraced production {row['name']} has no same-line semicolon")
            body = source[body_start:statement_end]
        alternatives: list[Alternative] = []
        action_texts: list[str] = []
        for raw_alt in split_alternatives(body):
            rhs_text, action, checked = split_action(raw_alt)
            if not rhs_text:
                fail(f"empty RHS alternative in {row['name']} at line {line}")
            rhs = RhsParser(rhs_text).parse()
            alternatives.append(Alternative(rhs_text, rhs, action, checked))
            action_texts.append(action)
        if not alternatives:
            fail(f"production {row['name']} has no alternatives")
        params = tuple(
            item.strip()
            for item in (match.group("params") or "").split(",")
            if item.strip()
        )
        production = Production(
            name=str(row["name"]),
            params=params,
            result_type=match.group("result").strip(),
            public=bool(match.group("public")),
            line=line,
            alternatives=alternatives,
            action_text="\n".join(action_texts),
            manifest=dict(row),
        )
        if production.name in result:
            fail(f"duplicate production {production.name}")
        result[production.name] = production
    return result


def parse_terminal_aliases(source: str) -> set[str]:
    aliases: set[str] = set()
    # The two alternatives must stay disjoint: a backslash belongs to the escape
    # branch only. Letting `[^"]` also match it makes every character ambiguous
    # and the match exponential on an unterminated literal.
    line_pattern = re.compile(r'^\s*("(?:\\.|[^"\\])*")\s*=>\s*Token::')
    for line in source.splitlines():
        match = line_pattern.match(line)
        if match:
            aliases.add(ast.literal_eval(match.group(1)))
    if not aliases:
        fail("no extern terminal aliases found")
    return aliases


def walk(node: Node) -> Iterator[Node]:
    yield node
    for arg in node.args:
        yield from walk(arg)
    for child in node.children:
        yield from walk(child)


def validate_manifest(
    manifest: dict[str, object],
    productions: Mapping[str, Production],
    terminals: set[str],
    frozen_sources: Mapping[str, str],
) -> dict[str, object]:
    errors: list[str] = []
    expected_manifest_fields = {
        "cuts",
        "hooks",
        "oracle_commit",
        "productions",
        "schema",
        "sources",
    }
    if set(manifest) != expected_manifest_fields:
        errors.append(
            "manifest top-level fields mismatch: "
            f"expected={sorted(expected_manifest_fields)}, found={sorted(manifest)}"
        )
    rows = manifest.get("productions")
    hooks = manifest.get("hooks")
    if manifest.get("schema") != "prism-parser-production-manifest-v1":
        errors.append(f"unsupported manifest schema {manifest.get('schema')!r}")
    if not isinstance(rows, list) or len(rows) != 133:
        errors.append(f"expected 133 production rows, found {len(rows) if isinstance(rows, list) else 'non-list'}")
    if not isinstance(hooks, dict):
        errors.append("manifest hooks must be an object")
        hooks = {}

    names = set(productions)
    hook_owners: dict[str, list[str]] = {str(name): [] for name in hooks}
    hook_evidence: dict[str, dict[str, object]] = {}
    reference_count = 0
    terminal_use_count = 0
    handwritten_uses = 0
    handwritten_symbols: set[str] = set()
    for production in productions.values():
        row = production.manifest
        row_fields = set(row)
        missing_fields = sorted(REQUIRED_PRODUCTION_FIELDS - row_fields)
        extra_fields = sorted(row_fields - PRODUCTION_FIELDS)
        if missing_fields or extra_fields:
            errors.append(
                f"{production.name}: manifest fields missing={missing_fields}, extra={extra_fields}"
            )
        cls = row.get("class")
        owner = row.get("owner")
        if cls not in ALLOWED_CLASSES:
            errors.append(f"{production.name}: invalid class {cls!r}")
        if owner not in ALLOWED_OWNERS:
            errors.append(f"{production.name}: invalid owner {owner!r}")
        if not isinstance(row.get("decision"), str) or not row["decision"].strip():
            errors.append(f"{production.name}: decision must be a nonempty string")
        depth = row.get("depth")
        if not isinstance(depth, dict) or set(depth) != {"entry", "shape", "detail"}:
            errors.append(f"{production.name}: malformed depth accounting")
        else:
            if depth["entry"] not in ALLOWED_DEPTH_ENTRIES:
                errors.append(f"{production.name}: invalid depth entry {depth['entry']!r}")
            if depth["shape"] not in ALLOWED_DEPTH_SHAPES:
                errors.append(f"{production.name}: invalid depth shape {depth['shape']!r}")
            if not isinstance(depth["detail"], str) or not depth["detail"].strip():
                errors.append(f"{production.name}: depth detail must be nonempty")
        consumers = row.get("consumers", [])
        if not isinstance(consumers, list) or any(
            consumer not in ALLOWED_OWNERS - {"shared"} for consumer in consumers
        ):
            errors.append(f"{production.name}: invalid consumers {consumers!r}")
        handwritten = row.get("handwritten")
        if not isinstance(handwritten, list) or not handwritten or any(
            not isinstance(symbol, str) or not symbol for symbol in handwritten
        ):
            errors.append(f"{production.name}: handwritten symbols must be a nonempty list")
            handwritten = []
        for symbol in handwritten:
            handwritten_uses += 1
            handwritten_symbols.add(symbol)
            declaration = re.compile(
                rf"(?m)^\s*(?:pub\s+)?fn\s+{re.escape(symbol)}\s*\("
            )
            if not any(
                path.endswith(".pr") and declaration.search(text)
                for path, text in frozen_sources.items()
            ):
                errors.append(
                    f"{production.name}: handwritten function {symbol!r} is absent "
                    "from the pinned Prism parser sources"
                )
        row_hooks = row.get("hooks")
        row_cuts = row.get("cuts")
        if not isinstance(row_hooks, list):
            errors.append(f"{production.name}: hooks must be a list")
            row_hooks = []
        if not isinstance(row_cuts, list):
            errors.append(f"{production.name}: cuts must be a list")
        if cls == "escaped" and not row_hooks:
            errors.append(f"{production.name}: escaped production has no named hook")
        for hook_name in row_hooks:
            if hook_name not in hooks:
                errors.append(f"{production.name}: unknown hook {hook_name!r}")
                continue
            hook_owners[str(hook_name)].append(production.name)

        params = set(production.params)
        for alt in production.alternatives:
            for node in walk(alt.rhs):
                if node.kind == "terminal":
                    terminal_use_count += 1
                    if node.value not in terminals:
                        errors.append(
                            f"{production.name}: terminal alias {node.value!r} is absent from extern Token"
                        )
                elif node.kind == "marker" and node.value not in {"@L", "@R"}:
                    errors.append(f"{production.name}: unsupported marker {node.value!r}")
                elif node.kind == "reference":
                    reference_count += 1
                    assert node.value is not None
                    if node.value in params:
                        if node.args:
                            errors.append(
                                f"{production.name}: parameter {node.value} cannot take arguments"
                            )
                        continue
                    target = productions.get(node.value)
                    if target is None:
                        errors.append(f"{production.name}: unknown production reference {node.value}")
                    elif len(node.args) != len(target.params):
                        errors.append(
                            f"{production.name}: {node.value} expects {len(target.params)} "
                            f"arguments, found {len(node.args)}"
                        )

    for hook_name, owners in sorted(hook_owners.items()):
        hook = hooks[hook_name]
        if not owners:
            errors.append(f"hook {hook_name!r} is not owned by any production")
            continue
        if not isinstance(hook, dict):
            errors.append(f"hook {hook_name!r} is not an object")
            continue
        if set(hook) != {"effects", "purpose", "symbols"}:
            errors.append(
                f"hook {hook_name!r}: expected fields effects/purpose/symbols, "
                f"found {sorted(hook)}"
            )
        effects = hook.get("effects")
        symbols = hook.get("symbols")
        if not isinstance(effects, list) or not effects:
            errors.append(f"hook {hook_name!r} has no effects")
        else:
            unknown_effects = sorted(set(effects) - ALLOWED_EFFECTS)
            if unknown_effects:
                errors.append(f"hook {hook_name!r}: unknown effects {unknown_effects}")
        if not isinstance(symbols, list) or not symbols:
            errors.append(f"hook {hook_name!r} has no symbols")
            continue
        if not isinstance(hook.get("purpose"), str) or not hook["purpose"].strip():
            errors.append(f"hook {hook_name!r} has no purpose")
        for symbol in symbols:
            if not isinstance(symbol, str) or "#" not in symbol:
                errors.append(f"hook {hook_name!r}: invalid symbol locator {symbol!r}")
                continue
            path, anchor = symbol.rsplit("#", 1)
            source_text = frozen_sources.get(path)
            if source_text is None:
                errors.append(f"hook {hook_name!r}: unpinned symbol source {path!r}")
            elif not re.search(rf"\b{re.escape(anchor)}\b", source_text):
                errors.append(
                    f"hook {hook_name!r}: anchor {anchor!r} absent from pinned {path}"
                )

        grammar_anchors = {
            symbol.rsplit("#", 1)[1]
            for symbol in symbols
            if isinstance(symbol, str)
            and symbol.startswith(f"{GRAMMAR_PATH}#")
            and "#" in symbol
        }
        for anchor in sorted(grammar_anchors):
            if anchor not in names:
                errors.append(f"hook {hook_name!r}: unknown grammar anchor {anchor!r}")
            elif anchor not in owners:
                errors.append(
                    f"hook {hook_name!r}: grammar anchor {anchor!r} is not among owners {owners}"
                )

        external_symbols = [
            symbol.rsplit("#", 1)[1]
            for symbol in symbols
            if isinstance(symbol, str)
            and "#" in symbol
            and not symbol.startswith("lib/std/")
            and not symbol.startswith(f"{GRAMMAR_PATH}#")
        ]
        evidence_roots = set(grammar_anchors) & set(owners)
        for owner in owners:
            evidence = any(
                re.search(rf"\b{re.escape(symbol)}\b", productions[owner].action_text)
                for symbol in external_symbols
            )
            if evidence:
                evidence_roots.add(owner)
        reachable = set(evidence_roots)
        queue = deque(sorted(evidence_roots))
        while queue:
            current = queue.popleft()
            dependencies = {
                node.value
                for alternative in productions[current].alternatives
                for node in walk(alternative.rhs)
                if node.kind == "reference" and node.value in owners
            }
            for dependency in sorted(dependencies - reachable):
                reachable.add(str(dependency))
                queue.append(str(dependency))
        hook_evidence[hook_name] = {
            "evidence_roots": sorted(evidence_roots),
            "feed_path_owners": sorted(reachable - evidence_roots),
        }
        for owner in owners:
            if owner not in reachable:
                errors.append(
                    f"hook {hook_name!r}: owner {owner!r} has neither its own grammar "
                    "anchor, direct action-symbol evidence, nor a same-hook feed path "
                    f"to an evidenced owner (roots={sorted(evidence_roots)})"
                )

    if manifest.get("cuts") != {}:
        errors.append("phase-1 expects the manifest-wide cut table to be empty")
    if any(production.manifest.get("cuts") for production in productions.values()):
        errors.append("phase-1 expects every production cut list to be empty")
    if errors:
        fail("manifest/grammar validation failed:\n  - " + "\n  - ".join(errors))

    return {
        "classes": count_values(p.manifest["class"] for p in productions.values()),
        "hook_count": len(hooks),
        "hook_evidence": dict(sorted(hook_evidence.items())),
        "hook_owners": {name: sorted(owners) for name, owners in sorted(hook_owners.items())},
        "handwritten_symbol_count": len(handwritten_symbols),
        "handwritten_use_count": handwritten_uses,
        "owners": count_values(p.manifest["owner"] for p in productions.values()),
        "production_count": len(productions),
        "reference_count": reference_count,
        "terminal_alias_count": len(terminals),
        "terminal_use_count": terminal_use_count,
    }


def count_values(values: Iterable[object]) -> dict[str, int]:
    counts: dict[str, int] = {}
    for value in values:
        key = str(value)
        counts[key] = counts.get(key, 0) + 1
    return dict(sorted(counts.items()))


def canonical(node: Node) -> str:
    if node.kind == "terminal":
        return json.dumps(node.value, ensure_ascii=False)
    if node.kind == "reference":
        suffix = ""
        if node.args:
            suffix = "<" + ",".join(canonical(arg) for arg in node.args) + ">"
        return f"{node.value}{suffix}"
    if node.kind == "marker":
        return str(node.value)
    if node.kind == "epsilon":
        return "()"
    if node.kind == "sequence":
        return " ".join(canonical(child) for child in node.children)
    if node.kind == "group":
        return f"({canonical(node.children[0])})"
    if node.kind == "capture":
        prefix = ("mut " if node.mutable else "") + (f"{node.label}:" if node.label else "")
        return f"<{prefix}{canonical(node.children[0])}>"
    suffix = {"optional": "?", "zero_or_more": "*", "one_or_more": "+"}.get(node.kind)
    if suffix is not None:
        return f"{canonical(node.children[0])}{suffix}"
    fail(f"cannot canonicalize node kind {node.kind}")
    raise AssertionError("unreachable")


def substitute(node: Node, env: Mapping[str, Node]) -> Node:
    if node.kind == "reference" and node.value in env and not node.args:
        return env[str(node.value)]
    return Node(
        node.kind,
        value=node.value,
        children=tuple(substitute(child, env) for child in node.children),
        args=tuple(substitute(arg, env) for arg in node.args),
        label=node.label,
        mutable=node.mutable,
    )


@dataclass(frozen=True)
class InstanceKey:
    name: str
    args: tuple[Node, ...] = ()

    def display(self) -> str:
        if not self.args:
            return self.name
        return f"{self.name}<" + ",".join(canonical(arg) for arg in self.args) + ">"


@dataclass(frozen=True)
class Fact:
    nullable: bool = False
    first: frozenset[str] = frozenset()

    def sequence(self, other: "Fact") -> "Fact":
        first = set(self.first)
        if self.nullable:
            first.update(other.first)
        return Fact(self.nullable and other.nullable, frozenset(first))

    def union(self, other: "Fact") -> "Fact":
        return Fact(self.nullable or other.nullable, self.first | other.first)


@dataclass
class Instance:
    key: InstanceKey
    production: Production
    env: dict[str, Node]


def instance_for(
    key: InstanceKey, productions: Mapping[str, Production]
) -> Instance:
    production = productions[key.name]
    if len(key.args) != len(production.params):
        fail(
            f"internal arity mismatch for {key.display()}: "
            f"{len(key.args)} != {len(production.params)}"
        )
    return Instance(key, production, dict(zip(production.params, key.args)))


def referenced_instance(
    node: Node,
    env: Mapping[str, Node],
    productions: Mapping[str, Production],
) -> InstanceKey | None:
    node = substitute(node, env)
    if node.kind != "reference":
        return None
    assert node.value is not None
    if node.value not in productions:
        return None
    return InstanceKey(node.value, node.args)


def build_instances(
    productions: Mapping[str, Production],
) -> dict[InstanceKey, Instance]:
    instances: dict[InstanceKey, Instance] = {}
    queue: deque[InstanceKey] = deque(
        InstanceKey(production.name)
        for production in productions.values()
        if not production.params
    )
    while queue:
        key = queue.popleft()
        if key in instances:
            continue
        instance = instance_for(key, productions)
        instances[key] = instance
        for alternative in instance.production.alternatives:
            for node in walk(alternative.rhs):
                dependency = referenced_instance(node, instance.env, productions)
                if dependency is not None and dependency not in instances:
                    queue.append(dependency)
    return instances


def eval_node(
    node: Node,
    env: Mapping[str, Node],
    facts: Mapping[InstanceKey, Fact],
    productions: Mapping[str, Production],
) -> Fact:
    if node.kind == "terminal":
        assert node.value is not None
        return Fact(False, frozenset({node.value}))
    if node.kind in {"epsilon", "marker"}:
        return Fact(True, frozenset())
    if node.kind in {"group", "capture"}:
        return eval_node(node.children[0], env, facts, productions)
    if node.kind == "optional" or node.kind == "zero_or_more":
        child = eval_node(node.children[0], env, facts, productions)
        return Fact(True, child.first)
    if node.kind == "one_or_more":
        return eval_node(node.children[0], env, facts, productions)
    if node.kind == "sequence":
        result = Fact(True, frozenset())
        for child in node.children:
            result = result.sequence(eval_node(child, env, facts, productions))
        return result
    if node.kind == "reference":
        if node.value in env and not node.args:
            return eval_node(env[str(node.value)], {}, facts, productions)
        key = referenced_instance(node, env, productions)
        if key is None:
            fail(f"cannot evaluate reference {canonical(node)}")
        return facts[key]
    fail(f"cannot evaluate node kind {node.kind}")
    raise AssertionError("unreachable")


def compute_facts(
    instances: Mapping[InstanceKey, Instance],
    productions: Mapping[str, Production],
    terminal_count: int,
) -> tuple[dict[InstanceKey, Fact], dict[InstanceKey, list[Fact]], int]:
    facts = {key: Fact() for key in instances}
    alternatives: dict[InstanceKey, list[Fact]] = {}
    limit = len(instances) * (terminal_count + 2)
    # The finite lattice is much smaller in practice; the explicit limit turns
    # a future malformed dependency graph into a diagnostic rather than a hang.
    for iteration in range(1, max(limit, 64) + 1):
        changed = False
        next_alternatives: dict[InstanceKey, list[Fact]] = {}
        for key in sorted(instances, key=lambda item: item.display()):
            instance = instances[key]
            alt_facts = [
                eval_node(alt.rhs, instance.env, facts, productions)
                for alt in instance.production.alternatives
            ]
            combined = Fact()
            for fact in alt_facts:
                combined = combined.union(fact)
            next_alternatives[key] = alt_facts
            if combined != facts[key]:
                facts[key] = combined
                changed = True
        alternatives = next_alternatives
        if not changed:
            return facts, alternatives, iteration
    fail(f"nullable/FIRST analysis did not converge in {max(limit, 64)} iterations")
    raise AssertionError("unreachable")


def direct_lead(node: Node) -> str | None:
    if node.kind == "terminal":
        return node.value
    if node.kind in {"capture", "group"}:
        return direct_lead(node.children[0])
    if node.kind == "sequence":
        for child in node.children:
            lead = direct_lead(child)
            if lead is not None:
                return lead
            if not marker_only(child):
                return None
    return None


def marker_only(node: Node) -> bool:
    if node.kind in {"epsilon", "marker"}:
        return True
    if node.kind in {"capture", "group"}:
        return marker_only(node.children[0])
    if node.kind == "sequence":
        return all(marker_only(child) for child in node.children)
    return False


def direct_selection(production: Production, fact: Fact) -> tuple[str, ...] | None:
    if production.params:
        return None
    if production.manifest["class"] != "predictive":
        return None
    if production.manifest["hooks"]:
        return None
    if fact.nullable:
        return None
    leads = tuple(direct_lead(alt.rhs) or "" for alt in production.alternatives)
    if not leads or any(not lead for lead in leads) or len(set(leads)) != len(leads):
        return None
    return leads


def validate_action_schema(
    productions: Mapping[str, Production],
) -> dict[str, object]:
    errors: list[str] = []
    validated_entries: list[dict[str, object]] = []
    seen: set[tuple[str, int]] = set()
    allowed_lowerings = {
        "construct-applied-name",
        "construct-list",
        "construct-name",
        "construct-nullary",
        "construct-optional-constructor",
        "construct-tuple",
        "construct-unboxed-record",
        "construct-unboxed-tuple",
        "construct-forall",
        "construct-empty-arrow",
        "construct-arrow",
        "construct-effect-row",
        "construct-empty-effect",
        "construct-usage-row",
        "construct-effect-label",
        "checked-effect-attach",
        "checked-usage-validate",
        "checked-dimension-decline",
        "checked-natural",
        "construct-row-literal",
        "dimension-tail",
        "identity-type",
        "identity-parenthesized",
        "return-unit",
        "construct-pattern-bool",
        "construct-pattern-char",
        "construct-pattern-field",
        "construct-pattern-fields",
        "construct-pattern-float",
        "construct-pattern-int",
        "construct-pattern-list",
        "construct-pattern-name",
        "construct-pattern-or",
        "construct-pattern-record",
        "construct-pattern-tuple",
        "delimited-pattern-args",
        "identity-pattern",
    }
    allowed_completions = {
        "GATNamed",
        "GATNamedOrPlain",
        "GATPlain",
        "GTCDimensionNatural",
        "GTCDimensionVariable",
        "GTADimensionFault",
        "GTADimensionTail",
        "GTANatural",
        "GTAOrdinary",
        "GTARow",
        "GTTypeForall",
        "GTType",
        "GTTypeFault",
        "GTArrow",
        "GTEffect",
        "GTUsage",
        "GTCoeffectRow",
        "GTEffectLabel",
        "GPArgs",
        "GPBareQualOrPlain",
        "GPBareUidOrPlain",
        "GPFieldExplicit",
        "GPFieldShorthand",
        "GPLetClosed",
        "GPLetNamedOrClosed",
        "GPPlain",
        "GPPreserveChild",
        "GPPreserveLast",
        "GPRecordClosed",
        "GPRecordSpread",
    }
    action_rows = TYPE_LEAF_ACTIONS + PATTERN_ACTIONS
    for spec in action_rows:
        key = (spec.production, spec.alternative)
        if key in seen:
            errors.append(f"duplicate action schema entry {key}")
            continue
        seen.add(key)
        production = productions.get(spec.production)
        if production is None:
            errors.append(f"schema references unknown production {spec.production}")
            continue
        expected_owner = "patterns" if spec in PATTERN_ACTIONS else "types"
        if production.manifest["owner"] != expected_owner:
            errors.append(
                f"{spec.production}: action schema requires {expected_owner} ownership"
            )
        is_type_arg = spec.production == "TypeArg"
        escaped = spec.production in {"TypeArg", "Type", "UType"}
        if escaped:
            if production.manifest["class"] != "escaped":
                errors.append(f"{spec.production} schema must preserve escaped strategy")
            expected_hooks = {
                "TypeArg": ["typearg-natural", "dimension-decline"],
                "Type": ["type-effect-attach"],
                "UType": ["usage-validate"],
            }[spec.production]
            if production.manifest["hooks"] != expected_hooks:
                errors.append("TypeArg schema must preserve both named hooks")
        elif expected_owner == "types":
            if production.manifest["class"] != "predictive":
                errors.append(f"{spec.production}: leaf schema requires predictive strategy")
            if production.manifest["hooks"]:
                errors.append(f"{spec.production}: leaf schema cannot lower a hooked production")
        elif production.manifest["class"] != "predictive" or production.manifest["hooks"]:
            errors.append(
                f"{spec.production}: Pattern schema requires predictive hook-free ownership"
            )
        if spec.alternative >= len(production.alternatives):
            errors.append(
                f"{spec.production}: alternative {spec.alternative} is out of range"
            )
            continue
        alternative = production.alternatives[spec.alternative]
        actual_rhs = canonical(alternative.rhs)
        actual_rhs_sha = sha256_text(stable_json(alternative.rhs.as_dict()))
        actual_action = alternative.action.strip()
        actual_action_sha = sha256_text(alternative.action)
        lead = direct_lead(alternative.rhs)
        if actual_rhs_sha != spec.rhs_sha256:
            errors.append(
                f"{spec.production}[{spec.alternative}]: RHS fingerprint drift "
                f"({actual_rhs!r}, {actual_rhs_sha})"
            )
        if actual_action_sha != spec.action_sha256:
            errors.append(
                f"{spec.production}[{spec.alternative}]: action fingerprint drift "
                f"({actual_action!r}, {actual_action_sha})"
            )
        expected_checked = (
            (is_type_arg and spec.alternative in {2, 3})
            or (spec.production == "Type" and spec.alternative in {1, 2})
            or (spec.production == "UType" and spec.alternative == 0)
        )
        if alternative.checked != expected_checked:
            errors.append(
                f"{spec.production}[{spec.alternative}]: checked-action status drift"
            )
        expected_hook = (
            {2: "typearg-natural", 3: "dimension-decline"}.get(spec.alternative, "")
            if is_type_arg else
            "type-effect-attach"
            if spec.production == "Type" and spec.alternative in {1, 2} else
            "usage-validate"
            if spec.production == "UType" and spec.alternative == 0 else ""
        )
        if spec.hook != expected_hook:
            errors.append(
                f"{spec.production}[{spec.alternative}]: hook provenance drift"
            )
        direct_token_schema = spec.token_kind in {"fixed", "kind"}
        if direct_token_schema and lead != spec.token_wire:
            errors.append(
                f"{spec.production}[{spec.alternative}]: token {spec.token_wire!r} "
                f"does not match direct lead {lead!r}"
            )
        expected_token_kind = (
            "kind"
            if spec.token_wire in {"char", "float", "ident", "int", "qual", "uid"}
            else "fixed"
        )
        if direct_token_schema and spec.token_kind != expected_token_kind:
            errors.append(
                f"{spec.production}[{spec.alternative}]: invalid token class "
                f"{spec.token_kind!r}"
            )
        if spec.lowering_kind not in allowed_lowerings:
            errors.append(
                f"{spec.production}[{spec.alternative}]: invalid lowering "
                f"{spec.lowering_kind!r}"
            )
        if spec.completion not in allowed_completions:
            errors.append(
                f"{spec.production}[{spec.alternative}]: invalid completion "
                f"{spec.completion!r}"
            )
        validated_entries.append(spec.as_dict(actual_rhs, actual_action))

    expected_keys = {(row.production, row.alternative) for row in action_rows}
    expected_production_sizes = {
        name: sum(row.production == name for row in action_rows)
        for name in {row.production for row in action_rows}
    }
    for name, expected_size in expected_production_sizes.items():
        actual_size = len(productions[name].alternatives)
        if actual_size != expected_size:
            errors.append(
                f"{name}: frozen alternative count drift "
                f"({actual_size} != {expected_size})"
            )
    if seen != expected_keys:
        errors.append(
            f"leaf schema coverage mismatch: missing={sorted(expected_keys - seen)}, "
            f"extra={sorted(seen - expected_keys)}"
        )

    helper_seen: set[str] = set()
    validated_helpers: list[dict[str, object]] = []
    expected_helper_instances = {
        "Comma": ("Comma<EffLabel>", "Comma<Pattern>", "Comma<RecordField>", "Comma<Type>", "Comma<TypeArg>", 'Comma<"ident">'),
        "CommaPlus": ("CommaPlus<Pattern>",),
        "CtorArgs": ("Comma<TypeArg>",),
        "RecordField": (),
    }
    for spec in ATYPE_HELPERS + PATTERN_HELPERS:
        if spec.production in helper_seen:
            errors.append(f"duplicate AType helper schema {spec.production}")
            continue
        helper_seen.add(spec.production)
        if spec.instances != expected_helper_instances.get(spec.production):
            errors.append(
                f"{spec.production}: unauthorized concrete helper instances "
                f"{spec.instances!r}"
            )
        production = productions.get(spec.production)
        if production is None:
            errors.append(f"{spec.production}: unknown helper production")
            continue
        actual_rhs = "\n".join(canonical(alt.rhs) for alt in production.alternatives)
        actual_action = "\n".join(alt.action for alt in production.alternatives)
        actual_rhs_sha = sha256_text("\n".join(
            stable_json(alt.rhs.as_dict()) for alt in production.alternatives
        ))
        if actual_rhs_sha != spec.rhs_sha256:
            errors.append(
                f"{spec.production}: helper RHS fingerprint drift "
                f"({actual_rhs!r}, {actual_rhs_sha})"
            )
        if sha256_text(actual_action) != spec.action_sha256:
            errors.append(f"{spec.production}: helper action fingerprint drift")
        validated_helpers.append(spec.as_dict(actual_rhs, actual_action.strip()))
    if helper_seen != {"Comma", "CommaPlus", "CtorArgs", "RecordField"}:
        errors.append(f"AType helper coverage mismatch: {sorted(helper_seen)}")

    if errors:
        fail("typed action schema validation failed:\n  - " + "\n  - ".join(errors))

    return {
        "entries": validated_entries,
        "helper_productions": validated_helpers,
        "typearg_completion_mapping": TYPEARG_COMPLETION_SCHEMA,
        "type_receipt_protocol": {
            "always_live": list(TYPE_RECEIPT_ALWAYS_LIVE),
            "menus": {
                receipt: list(menu)
                for receipt, menu in TYPE_RECEIPT_MENUS.items()
            },
            "suppression": [
                {"kind": kind, "wire": wire}
                for kind, wire in TYPE_RECEIPT_SUPPRESSION
            ],
        },
        "type_spine_receipt_transitions": {
            f"{row[0]}[{row[1]}]": row[8]
            for row in TYPE_SPINE_EXPECTATIONS
        },
        "pattern_receipt_protocol": {
            "menus": {
                receipt: list(menu)
                for receipt, menu in PATTERN_RECEIPT_MENUS.items()
            },
            "suppression": list(PATTERN_RECEIPT_SUPPRESSION),
            "phase_rows": PATTERN_PHASE_ROWS,
            "let": {"GLNamed": ["("], "GLClosed": []},
            "record_field": {
                "GFShorthand": ["=", ",", "}"],
                "GFExplicit": ["child-receipt", ",", "}"],
            },
        },
        "schema": "prism-parser-typed-action-schema-v1",
    }


def prism_string(value: str) -> str:
    escaped = (
        value.replace("\\", "\\\\")
        .replace('"', '\\"')
        .replace("{", "\\{")
        .replace("}", "\\}")
        .replace("\n", "\\n")
        .replace("\t", "\\t")
    )
    return f'"{escaped}"'


def token_pattern(spec: ActionSpec) -> str:
    if spec.token_kind == "fixed":
        return f'TFixed({prism_string(spec.token_wire)})'
    special = {
        "char": "TChar",
        "float": "TFloat",
        "ident": "TIdent",
        "int": "TInt",
        "qual": "TQual",
        "uid": "TUid",
    }
    if spec.token_wire not in special:
        fail(f"no Prism token constructor for schema wire {spec.token_wire!r}")
    return special[spec.token_wire]


def token_wire_pattern(wire: TokenWire) -> str:
    special = {
        "char": "TChar", "float": "TFloat", "ident": "TIdent",
        "int": "TInt", "qual": "TQual", "uid": "TUid",
    }
    return special.get(wire.value, f"TFixed({prism_string(wire.value)})")


def render_type_leaf(
    action_schema_sha256: str, control_module: str = "GeneratedControl"
) -> str:
    atype = {
        spec.alternative: spec
        for spec in TYPE_LEAF_ACTIONS
        if spec.production == "AType"
    }

    primitives = [
        atype[index] for index in range(8)
    ]
    miss_patterns = list(
        dict.fromkeys(token_pattern(atype[index]) for index in range(17))
    )
    miss_rows = [
        "      " + ", ".join(miss_patterns[index : index + 4]) + ","
        for index in range(0, len(miss_patterns), 4)
    ]
    dimensions = [
        spec for spec in TYPE_LEAF_ACTIONS if spec.production == "DimTerm"
    ]
    receipt_rows = []
    for receipt, menu in TYPE_RECEIPT_MENUS.items():
        expression = "c"
        for wire in menu:
            expression = f"cursor_note({expression}, TFixed({prism_string(wire)}))"
        receipt_rows.append(f"    {receipt} => {expression}")
    kind_names = {
        "ident": "TIdent", "vsemi": "TVSemi", "vopen": "TVOpen", "vclose": "TVClose",
    }
    suppression_rows = []
    for index, (kind, wire) in enumerate(TYPE_RECEIPT_SUPPRESSION):
        prefix = "  " if index == 0 else "    || "
        if kind == "end":
            condition = "cursor_at_end(c)"
        elif kind == "kind":
            condition = f"at_kind(c, {kind_names[wire]})"
        else:
            condition = f"at_fixed(c, {prism_string(wire)})"
        suppression_rows.append(prefix + condition)
    lines = [
        "-- GENERATED by experiments/parser_generator_phase1/generate.py.",
        f"-- Typed action schema SHA-256: {action_schema_sha256}",
        "-- Complete frozen AType and TypeArg lowering, with explicit receipts.",
        "-- Checked TypeArg hooks remain pinned in the typed action schema.",
        "",
        "-- lint: allow-file(L0101, L0102, L0103, L0105, L0108, L0202, L0203, L0204)",
        "",
        "import Data.List (..)",
        "",
        "import Data.Maybe (..)",
        "",
        "import Data.String (ends_with)",
        "",
        "import Syntax.Token (..)",
        "",
        "import Syntax.Ast (..)",
        "",
        "import Syntax.Cursor (..)",
        "",
        "import Syntax.Parse.Support (..)",
        "",
        f"import {control_module} (..)",
        "",
        "import Syntax.Parse.TypeSemantics (..)",
        "",
        "-- | Exact completed-Type state used by generated delimiters.",
        "pub type GeneratedTypeReceipt =",
        "  TRPlain | TRNamed | TRUsage | TRBareEffect | TRClosedEffect",
        "  | TRNat | TRRow | TRDimIdent",
        "",
        "-- | Child value and the grammar state completed at its right edge.",
        "-- The TypeDone constructor keeps the private Type parser seam source-compatible.",
        "pub type GeneratedChild(a) = TypeDone(a, GeneratedTypeReceipt)",
        "",
        "fn generated_child_value(item : GeneratedChild(a)) : a =",
        "  match item of",
        "    TypeDone(value, _) => value",
        "",
        "fn generated_child_receipt(",
        "  item : GeneratedChild(a)",
        ") : GeneratedTypeReceipt =",
        "  match item of",
        "    TypeDone(_, receipt) => receipt",
        "",
        "-- | Parse the complete 17-alternative AType production.",
        "pub fn generated_parse_atype(",
        "  c : Cursor, depth : Int,",
        "  parse_type : (Cursor, Int) -> Parsed(GeneratedChild(Ty)),",
        "  parse_type_arg : (Cursor, Int) -> Parsed(GeneratedChild(Ty))",
        ") : Parsed(GeneratedChild(Ty)) =",
        "  match cursor_kind(c) of",
        "    Some(TFixed(spelling)) =>",
        "      generated_fixed(spelling, c, depth, parse_type)",
        f"    Some({token_pattern(atype[9])}) => generated_name(c, depth, false, parse_type_arg)",
        f"    Some({token_pattern(atype[11])}) => generated_name(c, depth, true, parse_type_arg)",
        f"    Some({token_pattern(atype[12])}) => generated_name(c, depth, true, parse_type_arg)",
        "    _ => generated_atype_miss(c)",
        "",
        "fn generated_fixed(",
        "  spelling : String, c : Cursor, depth : Int,",
        "  parse_type : (Cursor, Int) -> Parsed(GeneratedChild(Ty))",
        ") : Parsed(GeneratedChild(Ty)) =",
    ]
    for index, spec in enumerate(primitives):
        keyword = "if" if index == 0 else "elif"
        lines.append(
            f"  {keyword} spelling == {prism_string(spec.token_wire)} then "
            f"generated_plain({spec.target_value}, cursor_advance(c))"
        )
    lines.extend(
        [
            f"  elif spelling == {prism_string(atype[8].token_wire)} then",
            "    generated_bind(parse_type(cursor_advance(c), depth), \\(item, c1) ->",
            "      let t = generated_child_value(item) in",
            "      let receipt = generated_child_receipt(item) in",
            '      if at_fixed(c1, "]") then',
            '        generated_plain(TyCon("List", [t]), cursor_advance(c1))',
            '      else PStuck(generated_type_note_close_follow(c1, receipt, "]")))',
            f"  elif spelling == {prism_string(atype[13].token_wire)} then generated_paren(c, depth, parse_type)",
            f"  elif spelling == {prism_string(atype[15].token_wire)} then generated_unboxed(c, depth, parse_type)",
            "  else generated_atype_miss(c)",
            "",
            "fn generated_name(",
            "  c : Cursor, depth : Int, constructor : Bool,",
            "  parse_type_arg : (Cursor, Int) -> Parsed(GeneratedChild(Ty))",
            ") : Parsed(GeneratedChild(Ty)) =",
            "  let name = peek_word(c)",
            "  let c1 = cursor_advance(c)",
            '  if at_fixed(c1, "(") then',
            "    generated_bind(",
            "        generated_parse_ctor_args(c1, depth, parse_type_arg),",
            "        \\(args, c2) -> generated_plain(",
            "          if constructor then TyCon(name, args) else TyApp(name, args),",
            "          c2),",
            "      )",
            "  elif constructor then generated_named(TyCon(name, Nil), c1)",
            "  else generated_named(TyVar(name), c1)",
            "",
            "-- | Complete CtorArgs child production, shared by AType and effect labels.",
            "pub fn generated_parse_ctor_args(",
            "  c : Cursor, depth : Int,",
            "  parse_type_arg : (Cursor, Int) -> Parsed(GeneratedChild(Ty))",
            ") : Parsed(List(Ty)) =",
            '  if at_fixed(c, "(") then',
            '    generated_type_separated(cursor_advance(c), depth, ")", parse_type_arg, Nil)',
            '  else PStuck(cursor_note(c, TFixed("(")))',
            "",
            "fn generated_paren(",
            "  c : Cursor, depth : Int,",
            "  parse_type : (Cursor, Int) -> Parsed(GeneratedChild(Ty))",
            ") : Parsed(GeneratedChild(Ty)) =",
            "  generated_bind(parse_type(cursor_advance(c), depth), \\(first, c1) ->",
            "    let t = generated_child_value(first) in",
            "    let receipt = generated_child_receipt(first) in",
            '    if at_fixed(c1, ",") then',
            "      generated_bind(",
            '          generated_type_separated(cursor_advance(c1), depth, ")", parse_type, [t]),',
            "          \\(types, c2) -> generated_plain(TyTuple(types), c2),",
            "        )",
            '    elif at_fixed(c1, ")") then',
            "      generated_plain(t, cursor_advance(c1))",
            '    else PStuck(generated_type_note_list_follow(c1, receipt, ")")))',
            "",
            "fn generated_unboxed(",
            "  c : Cursor, depth : Int,",
            "  parse_type : (Cursor, Int) -> Parsed(GeneratedChild(Ty))",
            ") : Parsed(GeneratedChild(Ty)) =",
            "  let c1 = cursor_advance(c)",
            '  if at_fixed(c1, "(") then',
            "    generated_bind(",
            '        generated_type_separated(cursor_advance(c1), depth, ")", parse_type, Nil),',
            "        \\(types, c2) -> generated_plain(TyUnboxedTuple(types), c2),",
            "      )",
            '  elif at_fixed(c1, "\\{") then',
            "    generated_bind(",
            '        generated_type_separated(cursor_advance(c1), depth, "\\}",',
            "          \\(x, d) -> generated_record_field(x, d, parse_type), Nil),",
            "        \\(fields, c2) -> generated_plain(TyUnboxedRecord(fields), c2),",
            "      )",
            "  else PStuck(cursor_note(cursor_note(c1, TFixed(\"(\")), TFixed(\"\\{\")))",
            "",
            "fn generated_record_field(",
            "  c : Cursor, depth : Int,",
            "  parse_type : (Cursor, Int) -> Parsed(GeneratedChild(Ty))",
            ") : Parsed(GeneratedChild(CField)) =",
            "  generated_bind(take_word(c, TIdent), \\(name, c1) ->",
            '    generated_bind(take_fixed(c1, ":"), \\(_colon, c2) ->',
            "      generated_bind(parse_type(c2, depth), \\(item, c3) ->",
            "        let t = generated_child_value(item) in",
            "        PTook(TypeDone(CField { name = name, ty = t },",
            "          generated_child_receipt(item)), c3))))",
            "",
            "fn generated_type_separated(",
            "  c : Cursor, depth : Int, close : String,",
            "  parse_item : (Cursor, Int) -> Parsed(GeneratedChild(a)), rev : List(a)",
            ") : Parsed(List(a)) =",
            "  generated_separated(c, depth, close, GSInitial, parse_item,",
            "    generated_child_value, generated_child_receipt, generated_type_before_item,",
            "    generated_type_separated_follow, rev)",
            "",
            "fn generated_type_before_item(",
            "  _phase : GeneratedSeparatedPhase, _c : Cursor, _close : String",
            ") : GeneratedSeparatedDecision = GSEnter",
            "",
            "fn generated_type_separated_follow(",
            "  _phase : GeneratedSeparatedPhase, c : Cursor,",
            "  receipt : GeneratedTypeReceipt, close : String",
            ") : Cursor =",
            "  generated_type_note_list_follow(c, receipt, close)",
            "",
            "fn generated_plain(value : Ty, c : Cursor) : Parsed(GeneratedChild(Ty)) =",
            "  PTook(TypeDone(value, TRPlain), c)",
            "",
            "fn generated_named(value : Ty, c : Cursor) : Parsed(GeneratedChild(Ty)) =",
            "  PTook(TypeDone(value, TRNamed), c)",
            "",
            "fn generated_atype_miss(c : Cursor) : Parsed(GeneratedChild(Ty)) =",
            "  PStuck(foldl(cursor_note, c, [",
            *miss_rows,
            "    ]))",
            "",
            "-- | Whether this completed state remains live on a Type FOLLOW token.",
            "pub fn generated_type_receipt_always_live(",
            "  receipt : GeneratedTypeReceipt",
            ") : Bool =",
            "  match receipt of",
            *[f"    {receipt} => true" for receipt in TYPE_RECEIPT_ALWAYS_LIVE],
            "    _ => false",
            "",
            "-- | Frozen Type FOLLOW set that suppresses an ordinary receipt menu.",
            "pub fn generated_type_suppress_receipt(c : Cursor) : Bool =",
            *suppression_rows,
            "",
            "-- | Exact wanted-token menu for each completed Type state.",
            "pub fn generated_type_note_receipt(",
            "  c : Cursor, receipt : GeneratedTypeReceipt",
            ") : Cursor =",
            "  match receipt of",
            *receipt_rows,
            "",
            "pub fn generated_type_note_if_live(",
            "  c : Cursor, receipt : GeneratedTypeReceipt",
            ") : Cursor =",
            "  if generated_type_receipt_always_live(receipt)",
            "      || not(generated_type_suppress_receipt(c)) then",
            "    generated_type_note_receipt(c, receipt)",
            "  else c",
            "",
            "pub fn generated_type_note_close_follow(",
            "  c : Cursor, receipt : GeneratedTypeReceipt, close : String",
            ") : Cursor =",
            "  generated_type_note_if_live(cursor_note(c, TFixed(close)), receipt)",
            "",
            "pub fn generated_type_note_list_follow(",
            "  c : Cursor, receipt : GeneratedTypeReceipt, close : String",
            ") : Cursor =",
            '  generated_type_note_close_follow(cursor_note(c, TFixed(",")), receipt, close)',
            "",
            "-- | Parse the complete frozen DimTerm production.",
            "-- The caller decides whether a following `+` enters the declined fault path.",
            "pub type GeneratedDimCompletion",
            "  = GTCDimensionNatural | GTCDimensionVariable",
            "",
            "pub fn generated_parse_dim_term(",
            "  c : Cursor",
            ") : Parsed(GeneratedDimCompletion) =",
            "  match cursor_kind(c) of",
        ]
    )
    for spec in dimensions:
        lines.extend(
            [
                f"    Some({token_pattern(spec)}) =>",
                f"      generated_dim_done(c, {spec.completion})",
            ]
        )
    lines.extend(
        [
            "    _ =>",
            f"      let c1 = cursor_note(c, {token_pattern(dimensions[0])})",
            f"      PStuck(cursor_note(c1, {token_pattern(dimensions[1])}))",
            "",
            "fn generated_dim_done(",
            "  c : Cursor,",
            "  completion : GeneratedDimCompletion",
            ") : Parsed(GeneratedDimCompletion) =",
            "  PTook(completion, cursor_advance(c))",
            "",
            "-- | Injectable TypeArg entry used by the isolated behavior fixture.",
            "-- Like every public TypeArg entry, it spends exactly once.",
            "pub fn generated_parse_type_arg_with(",
            "  c : Cursor, depth : Int,",
            "  parse_type_body : (Cursor, Int) -> Parsed(GeneratedChild(Ty)),",
            "  parse_row_body : (Cursor, Int) -> Parsed(Row)",
            ") : Parsed(GeneratedChild(Ty)) =",
            "  match descend(depth, c) of",
            "    PStuck(c1) => PStuck(c1)",
            "    PFault(d) => PFault(d)",
            "    PTook(d, c1) =>",
            "      generated_parse_type_arg_body(c1, d, parse_type_body, parse_row_body)",
            "",
            "fn generated_parse_type_arg_body(",
            "  c : Cursor, depth : Int,",
            "  parse_type_body : (Cursor, Int) -> Parsed(GeneratedChild(Ty)),",
            "  parse_row_body : (Cursor, Int) -> Parsed(Row)",
            ") : Parsed(GeneratedChild(Ty)) =",
            '  if at_fixed(c, "\\{") then',
            "    generated_bind(parse_row_body(cursor_advance(c), depth), \\(row, c1) ->",
            "      PTook(TypeDone(TyRowLit(row), TRRow), c1))",
            "  elif at_kind(c, TInt) || at_kind(c, TIdent) then",
            "    match generated_parse_dim_term(c) of",
            "      PTook(_term, c1) =>",
            '        if at_fixed(c1, "+") then',
            "          generated_decline_dimension(c, cursor_advance(c1))",
            "        elif at_kind(c, TInt) then generated_parse_natural(c)",
            "        else generated_type_arg_fallback(c, depth, parse_type_body)",
            "      PStuck(c1) => PStuck(c1)",
            "      PFault(d) => PFault(d)",
            "  else generated_type_arg_fallback(c, depth, parse_type_body)",
            "",
            "fn generated_type_arg_fallback(",
            "  c : Cursor, depth : Int,",
            "  parse_type_body : (Cursor, Int) -> Parsed(GeneratedChild(Ty))",
            ") : Parsed(GeneratedChild(Ty)) =",
            "  match parse_type_body(c, depth) of",
            "    PStuck(c1) =>",
            "      if c1.pos == c.pos then",
            '        PStuck(cursor_note(cursor_note(c1, TInt), TFixed("\\{")))',
            "      else PStuck(c1)",
            "    PFault(d) => PFault(d)",
            "    PTook(done, c1) =>",
            "      match done of",
            "        TypeDone(t, receipt) =>",
            "          if at_kind(c, TIdent) && c1.pos == c.pos + 1 then",
            "            PTook(TypeDone(t, TRDimIdent), c1)",
            "          else PTook(TypeDone(t, receipt), c1)",
            "",
            "-- checked action hook: typearg-natural",
            "fn generated_parse_natural(c : Cursor) : Parsed(GeneratedChild(Ty)) =",
            "  match cursor_peek(c) of",
            "    None => PStuck(cursor_note(c, TInt))",
            "    Some(t) =>",
            "      let raw = token_text(t)",
            "      let c1 = cursor_advance(c)",
            '      if ends_with("i64", raw) || ends_with("u64", raw) then',
            "        PFault(refuse(t.span,",
            '          "a dimension is a plain natural literal; drop the width suffix"))',
            "      else",
            "        match parse_int(raw) of",
            "          Some(n) =>",
            "            if n <= 18446744073709551615 then",
            "              PTook(TypeDone(TyNat(n), TRNat), c1)",
            '            else PFault(refuse(t.span, "dimension literal is too large"))',
            '          None => PFault(refuse(t.span, "dimension literal is too large"))',
            "",
            "-- checked action hook: dimension-decline",
            "fn generated_decline_dimension(",
            "  saved : Cursor, tail : Cursor",
            ") : Parsed(GeneratedChild(Ty)) =",
            "  match generated_parse_dim_tail(tail) of",
            "    PStuck(c) => PStuck(c)",
            "    PFault(d) => PFault(d)",
            "    PTook(_, c) => PFault(refuse(cursor_since(saved, c),",
            '      "arithmetic on dimensions is not supported: a dimension is a plain natural literal (`0`, `1`, `2`, ...) or a type variable, and dimensions unify by equality only"))',
            "",
            "fn generated_parse_dim_tail(c : Cursor) : Parsed(Unit) =",
            "  match generated_parse_dim_term(c) of",
            "    PStuck(c1) => PStuck(c1)",
            "    PFault(d) => PFault(d)",
            "    PTook(_, c1) =>",
            '      if at_fixed(c1, "+") then',
            "        generated_parse_dim_tail(cursor_advance(c1))",
            "      else PTook((), c1)",
            "",
        ]
    )
    return "\n".join(lines) + TYPE_SPINE_TEMPLATE


# The compact Prism control template is shared by the fifteen pinned Type,
# Arrow, ArrowEff, UType, CoeffRowParts, and EffLabel action rows. Grammar
# identity and checked-action ownership are validated before it is rendered.
TYPE_SPINE_TEMPLATE = r"""
-- -------------------------------------------------------------------------
-- Complete generated Type-family control flow
-- -------------------------------------------------------------------------

-- These are the only recursive entries. Each spends exactly once; body
-- functions are deliberately nonspending so TypeArg does not double-charge
-- its ordinary-Type alternative.
pub fn generated_parse_type(c : Cursor, depth : Int) : Parsed(GeneratedChild(Ty)) =
  generated_spend(c, depth, generated_parse_type_body_done)

pub fn generated_parse_type_head(c : Cursor, depth : Int) : Parsed(GeneratedChild(Ty)) =
  generated_spend(c, depth, generated_parse_type_head_body_done)

pub fn generated_parse_type_arg(c : Cursor, depth : Int) : Parsed(GeneratedChild(Ty)) =
  generated_parse_type_arg_with(c, depth, generated_parse_type_body_done,
    generated_parse_eff_labels_body)

fn generated_parse_type_body_done(c : Cursor, depth : Int) : Parsed(GeneratedChild(Ty)) =
  generated_parse_type_mode(c, depth, false)

fn generated_parse_type_head_body_done(c : Cursor, depth : Int) : Parsed(GeneratedChild(Ty)) =
  generated_parse_type_mode(c, depth, true)

fn generated_parse_type_mode(c : Cursor, depth : Int, head : Bool) : Parsed(GeneratedChild(Ty)) =
  if at_fixed(c, "forall") then
    generated_parse_forall(c, depth, head)
  else
    let saved = c
    match generated_parse_arrow_done(c, depth) of
      PStuck(c1) =>
        if c1.pos == c.pos then
          PStuck(cursor_note(c1, TFixed("forall")))
        else PStuck(c1)
      PFault(d) => PFault(d)
      PTook(done, c1) =>
        if head then PTook(done, c1)
        else generated_parse_arrow_effect_done(saved, done, c1, depth)

fn generated_parse_forall(c : Cursor, depth : Int, head : Bool) : Parsed(GeneratedChild(Ty)) =
  generated_bind(take_fixed(c, "forall"), \(_kw, c1) ->
    generated_forall_binders(c1, depth, head))

fn generated_forall_binders(c : Cursor, depth : Int, head : Bool) : Parsed(GeneratedChild(Ty)) =
  generated_bind(take_word(c, TIdent), \(first, c1) ->
    generated_forall_tail(first, c1, depth, head))

fn generated_forall_tail(first : String, c : Cursor, depth : Int, head : Bool) : Parsed(GeneratedChild(Ty)) =
  let (more, c1) = generated_ident_run(c, Nil)
  match take_fixed(c1, ".") of
    PStuck(c2) => PStuck(generated_note_same(c1, c2, TIdent))
    PFault(d) => PFault(d)
    PTook(_, c2) =>
      let parsed = if head then generated_parse_type_head(c2, depth)
                   else generated_parse_type(c2, depth)
      generated_bind(parsed, \(done, c3) -> match done of {
        TypeDone(body, receipt) =>
          PTook(TypeDone(TyForall(Cons(first, more), body), receipt), c3)
      })

fn generated_ident_run(c : Cursor, rev : List(String)) : (List(String), Cursor) =
  match cursor_peek(c) of
    Some(t) =>
      if t.kind == TIdent then
        generated_ident_run(cursor_advance(c), Cons(token_text(t), rev))
      else (reverse(rev), c)
    None => (reverse(rev), c)

fn generated_note_same(saved : Cursor, failed : Cursor, wanted : TokenKind) : Cursor =
  if failed.pos == saved.pos then cursor_note(failed, wanted) else failed

-- Commit after the two-token `()` prefix. This left-factor preserves the LR
-- state's exact lone `->` expectation when the arrow token is missing.
fn generated_parse_arrow_done(c : Cursor, depth : Int) : Parsed(GeneratedChild(Ty)) =
  if at_fixed(c, "(") && at_fixed(cursor_advance(c), ")") then
    let c1 = cursor_advance(cursor_advance(c))
    generated_bind(take_fixed(c1, "->"), \(_arrow, c2) ->
      generated_bind(generated_parse_arrow_nested(c2, depth), \(done, c3) ->
        match done of {
          TypeDone(cod, receipt) =>
            PTook(TypeDone(TyFun(Nil, generated_empty_row(), cod), receipt), c3)
        }))
  else
    match generated_parse_usage_type_done(c, depth) of
      PStuck(c1) => PStuck(c1)
      PFault(d) => PFault(d)
      PTook(done, c1) =>
        if at_fixed(c1, "->") then
          generated_bind(generated_parse_arrow_nested(cursor_advance(c1), depth),
            \(cod_done, c2) -> match done of {
              TypeDone(dom, _) => match cod_done of {
                TypeDone(cod, receipt) =>
                  PTook(TypeDone(TyFun(generated_domain_types(dom),
                    generated_empty_row(), cod), receipt), c2)
              }
            })
        else PTook(done, c1)

fn generated_parse_arrow_nested(c : Cursor, depth : Int) : Parsed(GeneratedChild(Ty)) =
  generated_spend(c, depth, generated_parse_arrow_done)

fn generated_domain_types(t : Ty) : List(Ty) =
  match t of
    TyTuple(ts) => ts
    _ => [t]

fn generated_empty_row() : Row = Row { labels = Nil, tail = None }

fn generated_parse_usage_type_done(c : Cursor, depth : Int) : Parsed(GeneratedChild(Ty)) =
  let saved = c
  match generated_parse_atype(c, depth, generated_parse_type, generated_parse_type_arg) of
    PStuck(c1) => PStuck(c1)
    PFault(d) => PFault(d)
    PTook(done, c1) =>
      match done of
        TypeDone(t, _) =>
          if at_fixed(c1, "@") then
            generated_bind(generated_parse_usage_parts(cursor_advance(c1)),
              \(parts, c2) -> match validate_usage(saved, t, parts.facts,
                parts.open_tail, c2) of {
                  PStuck(c3) => PStuck(c3),
                  PFault(d) => PFault(d),
                  PTook(used, c3) => PTook(TypeDone(used, TRUsage), c3)
              })
          else PTook(done, c1)

fn generated_parse_arrow_effect_done(saved : Cursor, done : GeneratedChild(Ty), c : Cursor, depth : Int) : Parsed(GeneratedChild(Ty)) =
  if at_fixed(c, "!") then
    let braced = at_fixed(cursor_advance(c), "\{")
    generated_bind(generated_parse_effect_row(c, depth), \(row, c1) ->
      if at_fixed(c1, "@") then
        generated_bind(generated_parse_usage_parts(cursor_advance(c1)),
          \(_parts, c2) -> PFault(refuse(cursor_since(saved, c2),
            "parenthesize the function type before `@`: write `((a) -> b ! \{E\}) @ fact`")))
      else
        match done of {
          TypeDone(t, _) =>
            match t of {
              TyFun(ps, _, cod) => PTook(TypeDone(TyFun(ps, row, cod),
                if braced then TRClosedEffect else TRBareEffect), c1),
              _ => PFault(refuse(cursor_since(saved, c1),
                "effect row `! \{..\}` only applies to a function type"))
            }
        })
  else PTook(done, c)

-- -------------------------------------------------------------------------
-- Effect rows and the optional-argument completion state of labels
-- -------------------------------------------------------------------------

pub type GeneratedRowReceipt = GRClosedItem | GROptionalArgs
pub type GeneratedRowItem(a) = GeneratedRowItem(a, GeneratedRowReceipt)
type GeneratedDelimited(a) = GDClosed(List(a)) | GDOpen(List(a), String)

type GeneratedUsageParts = GeneratedUsageParts {
  facts: List(String),
  open_tail: Bool
}

pub fn generated_parse_effect_row(c : Cursor, depth : Int) : Parsed(Row) =
  generated_bind(take_fixed(c, "!"), \(_bang, c1) ->
    if at_fixed(c1, "\{") then
      generated_parse_eff_labels_body(cursor_advance(c1), depth)
    else PTook(generated_empty_row(), c1))

pub fn generated_parse_eff_label(c : Cursor, depth : Int) : Parsed(EffLabel) =
  match generated_parse_eff_label_done(c, depth) of
    PStuck(c1) => PStuck(c1)
    PFault(d) => PFault(d)
    PTook(done, c1) =>
      match done of
        GeneratedRowItem(label, _) => PTook(label, c1)

fn generated_parse_eff_label_done(c : Cursor, depth : Int) : Parsed(GeneratedRowItem(EffLabel)) =
  match cursor_peek(c) of
    Some(t) =>
      match t.kind of
        TIdent =>
          PTook(GeneratedRowItem(EffLabel { name = token_text(t), args = Nil },
            GRClosedItem), cursor_advance(c))
        TUid => generated_parse_named_eff_label(t, c, depth)
        TQual => generated_parse_named_eff_label(t, c, depth)
        _ => generated_eff_label_miss(c)
    None => generated_eff_label_miss(c)

fn generated_parse_named_eff_label(t : Token, c : Cursor, depth : Int) : Parsed(GeneratedRowItem(EffLabel)) =
  let c1 = cursor_advance(c)
  if at_fixed(c1, "(") then
    generated_bind(generated_parse_ctor_args(c1, depth, generated_parse_type_arg),
      \(args, c2) -> PTook(GeneratedRowItem(
        EffLabel { name = token_text(t), args = args }, GRClosedItem), c2))
  else
    PTook(GeneratedRowItem(EffLabel { name = token_text(t), args = Nil },
      GROptionalArgs), c1)

fn generated_eff_label_miss(c : Cursor) : Parsed(GeneratedRowItem(EffLabel)) =
  PStuck(cursor_note(cursor_note(cursor_note(c, TIdent), TUid), TQual))

fn generated_parse_eff_labels_body(c : Cursor, depth : Int) : Parsed(Row) =
  match generated_parse_delimited(c, depth, generated_parse_eff_label_done) of
    PStuck(c1) => PStuck(c1)
    PFault(d) => PFault(d)
    PTook(items, c1) =>
      match items of
        GDClosed(labels) =>
          PTook(Row { labels = labels, tail = None }, c1)
        GDOpen(labels, tail) =>
          PTook(Row { labels = labels, tail = Some(tail) }, c1)

fn generated_parse_delimited(c : Cursor, depth : Int, parse_item : (Cursor, Int) -> Parsed(GeneratedRowItem(a))) : Parsed(GeneratedDelimited(a)) =
  if at_fixed(c, "\}") then
    PTook(GDClosed(Nil), cursor_advance(c))
  elif at_fixed(c, "|") then
    generated_parse_delimited_tail(cursor_advance(c), Nil)
  else
    match parse_item(c, depth) of
      PStuck(c1) => PStuck(generated_note_row_entry(c, c1))
      PFault(d) => PFault(d)
      PTook(item, c1) =>
        match item of
          GeneratedRowItem(value, receipt) =>
            generated_parse_delimited_more(c1, depth, parse_item, [value], receipt)

fn generated_parse_delimited_more(c : Cursor, depth : Int, parse_item : (Cursor, Int) -> Parsed(GeneratedRowItem(a)), rev : List(a), receipt : GeneratedRowReceipt) : Parsed(GeneratedDelimited(a)) =
  if at_fixed(c, "\}") then
    PTook(GDClosed(reverse(rev)), cursor_advance(c))
  elif at_fixed(c, "|") then
    generated_parse_delimited_tail(cursor_advance(c), rev)
  elif at_fixed(c, ",") then
    let c1 = cursor_advance(c)
    if at_fixed(c1, "\}") then
      PTook(GDClosed(reverse(rev)), cursor_advance(c1))
    elif at_fixed(c1, "|") then
      generated_parse_delimited_tail(cursor_advance(c1), rev)
    else
      match parse_item(c1, depth) of
        PStuck(c2) => PStuck(generated_note_row_entry(c1, c2))
        PFault(d) => PFault(d)
        PTook(item, c2) =>
          match item of
            GeneratedRowItem(value, next_receipt) =>
              generated_parse_delimited_more(c2, depth, parse_item,
                Cons(value, rev), next_receipt)
  else
    PStuck(generated_note_row_follow(c, receipt))

fn generated_note_row_entry(saved : Cursor, failed : Cursor) : Cursor =
  if failed.pos == saved.pos then
    cursor_note(cursor_note(failed, TFixed("|")), TFixed("\}"))
  else failed

fn generated_note_row_follow(c : Cursor, receipt : GeneratedRowReceipt) : Cursor =
  let c1 = cursor_note(cursor_note(cursor_note(c, TFixed(",")), TFixed("|")), TFixed("\}"))
  match receipt of
    GROptionalArgs => cursor_note(c1, TFixed("("))
    _ => c1

fn generated_parse_delimited_tail(c : Cursor, rev : List(a)) : Parsed(GeneratedDelimited(a)) =
  generated_bind(take_word(c, TIdent), \(tail, c1) ->
    generated_bind(take_fixed(c1, "\}"), \(_close, c2) ->
      PTook(GDOpen(reverse(rev), tail), c2)))

-- -------------------------------------------------------------------------
-- Usage rows
-- -------------------------------------------------------------------------

fn generated_parse_usage_parts(c : Cursor) : Parsed(GeneratedUsageParts) =
  if at_fixed(c, "\{") then
    generated_parse_usage_braces(cursor_advance(c))
  else
    match take_word(c, TIdent) of
      PStuck(c1) => PStuck(generated_note_same(c, c1, TFixed("\{")))
      PFault(d) => PFault(d)
      PTook(fact, c1) => PTook(
        GeneratedUsageParts { facts = [fact], open_tail = false }, c1)

fn generated_parse_usage_braces(c : Cursor) : Parsed(GeneratedUsageParts) =
  match generated_parse_delimited(c, 0, generated_parse_usage_item) of
    PStuck(c1) => PStuck(c1)
    PFault(d) => PFault(d)
    PTook(items, c1) =>
      match items of
        GDClosed(facts) => PTook(
          GeneratedUsageParts { facts = facts, open_tail = false }, c1)
        GDOpen(facts, _) => PTook(
          GeneratedUsageParts { facts = facts, open_tail = true }, c1)

fn generated_parse_usage_item(c : Cursor, _depth : Int) : Parsed(GeneratedRowItem(String)) =
  match take_word(c, TIdent) of
    PStuck(c1) => PStuck(c1)
    PFault(d) => PFault(d)
    PTook(fact, c1) => PTook(GeneratedRowItem(fact, GRClosedItem), c1)
"""



@dataclass
class BuildResult:
    plan_text: str
    action_schema_text: str
    shared_runtime_text: str
    type_leaf_text: str
    production_type_text: str
    type_leaf_manifest_text: str
    type_leaf_main_text: str
    type_leaf_test_text: str
    plan: dict[str, object]

    @property
    def control_text(self) -> str:
        """Compatibility name for the read-only shared runtime snapshot."""
        return self.shared_runtime_text

    def outputs(self) -> tuple[tuple[Path, str], ...]:
        return (
            (PLAN_PATH, self.plan_text),
            (ACTION_SCHEMA_PATH, self.action_schema_text),
            (TYPE_LEAF_PATH, self.type_leaf_text),
            (TYPE_LEAF_MANIFEST_PATH, self.type_leaf_manifest_text),
            (TYPE_LEAF_MAIN_PATH, self.type_leaf_main_text),
            (PRODUCTION_TYPE_PATH, self.production_type_text),
        )


def candidate_type_consumer_integrated(source: str) -> bool:
    required = (
        "import Syntax.Parse.GeneratedType (..)",
        "strip_type_done(generated_parse_type(c, depth))",
        "strip_type_done(generated_parse_type_head(c, depth))",
        "strip_type_done(generated_parse_type_arg(c, depth))",
        "generated_parse_effect_row(c, depth)",
        "generated_parse_eff_label(c, depth)",
        "generated_type_note_if_live(c, receipt)",
    )
    return all(marker in source for marker in required)


# The maintained-T baseline: the generator's own size plus the hand-written
# Type and Pattern families it set out to replace, as they stood before any
# generation. These are frozen numbers rather than a live measurement, which is
# the point (the target must not move), but it also means they were counted in
# the layout of the day. Both sides are formatted the same way now, so the
# comparison is like-for-like going forward; be aware that recounting the
# baseline sources today gives slightly smaller figures, because canonical
# layout compacts the verbose hand-written original.
BASELINE_GENERATOR_LINES = 2559
BASELINE_TYPE_LINES = 668
BASELINE_PATTERN_LINES = 505


def compact_plan(c: Mapping[str, object]) -> dict[str, object]:
    """Return the source/freshness receipts and the complete maintained ledger."""
    generator = int(c["generator_lines"])
    control = int(c["control_lines"])
    type_parts = {
        "facade": int(c["production_facade_lines"]),
        "semantics": code_lines(TYPE_SEMANTICS_PATH.read_text(), "--"),
        "generated": int(c["production_type_lines"]),
    }
    pattern_parts = {
        "facade": code_lines(PRODUCTION_PATTERN_CONSUMER.read_text(), "--"),
        "semantics": code_lines(PATTERN_SEMANTICS_PATH.read_text(), "--"),
        "generated": int(c.get("production_pattern_lines", 0)),
    }
    current = generator + control + sum(type_parts.values()) + sum(pattern_parts.values())
    baseline = (
        BASELINE_GENERATOR_LINES + BASELINE_TYPE_LINES + BASELINE_PATTERN_LINES
    )
    return {
        "schema": "prism-parser-generator-plan-v2",
        "source": {
            "grammar_blob_oid": c["grammar_oid"],
            "grammar_path": GRAMMAR_PATH,
            "manifest_oracle_commit": c["commit"],
            "source_pins_verified": len(c["source_pins"]),
        },
        "manifest_validation": c["validation"],
        "analysis": {"convergence_iterations": c["iterations"],
                     "concrete_instance_count": len(c["instances"])},
        "predictive_validation": {
            "production_count": len(c["selected"]),
            "productions": [production.name for production, _ in c["selected"]],
        },
        "type_leaf_emission": {
            "artifact": str(TYPE_LEAF_PATH.relative_to(ROOT)),
            "production_artifact": str(PRODUCTION_TYPE_PATH.relative_to(ROOT)),
            "artifact_sha256": sha256_text(str(c["type_leaf_text"])),
            "action_schema": {
                "artifact": str(ACTION_SCHEMA_PATH.relative_to(ROOT)),
                "entry_count": len(TYPE_LEAF_ACTIONS + PATTERN_ACTIONS),
                "helper_production_count": len(ATYPE_HELPERS + PATTERN_HELPERS),
                "sha256": sha256_text(str(c["action_schema_text"])),
            },
            "test_fixture": {
                "artifact": str(TYPE_LEAF_TEST_PATH.relative_to(ROOT)),
                "classification": "independent-handwritten",
                "generated": False,
                "sha256": sha256_text(str(c["type_leaf_test_text"])),
                "test_count": c["type_leaf_test_count"],
                "transitive": False,
            },
        },
        "shared_runtime": {
            "artifact": str(SHARED_RUNTIME_PATH.relative_to(ROOT)),
            "classification": "handwritten-family-neutral-runtime",
            "sha256": sha256_text(str(c["shared_runtime_text"])),
            "code_lines": control,
            "api_markers": [
                "generated_bind",
                "generated_spend",
                "generated_separated",
                "GSRequiredFirst",
                "GSAfterSeparator",
            ],
            "test_fixture": {
                "artifact": str(PATTERN_CONTRACT_PATH.relative_to(ROOT)),
                "classification": "independent-handwritten",
                "generated": False,
                "sha256": sha256_text(PATTERN_CONTRACT_PATH.read_text()),
                "test_count": 1,
                "transitive": False,
            },
        },
        "accounting": {
            "baseline": {"generator": BASELINE_GENERATOR_LINES,
                         "type": BASELINE_TYPE_LINES,
                         "pattern": BASELINE_PATTERN_LINES,
                         "maintained_t_lines": baseline},
            "generator_code_lines": generator,
            "shared_control_code_lines": control,
            "type": type_parts,
            "pattern": pattern_parts,
            "maintained_t_lines": current,
            "maintained_t_delta": current - baseline,
            # The experiment's own question, answered in the artifact so an
            # unfavorable result is recorded rather than hidden or asserted away.
            "maintained_t_verdict":
                "compacted" if current < baseline else "regressed",
            "status": "full-type-pattern-authority"
                if pattern_parts["generated"] else "pattern-scaffold",
        },
    }


def build() -> BuildResult:
    manifest_text = MANIFEST_PATH.read_text(encoding="utf-8")
    manifest = json.loads(manifest_text)
    commit = str(manifest["oracle_commit"])
    source_pins: dict[str, str] = dict(manifest["sources"])
    if GRAMMAR_PATH not in source_pins:
        fail(f"manifest pins no OID for {GRAMMAR_PATH}")
    grammar_oid = source_pins[GRAMMAR_PATH]
    frozen_sources = {
        path: read_frozen_blob(oid, path)
        for path, oid in sorted(source_pins.items())
    }
    grammar = frozen_sources[GRAMMAR_PATH]

    productions = parse_productions(grammar, manifest["productions"])
    terminals = parse_terminal_aliases(grammar)
    validation = validate_manifest(
        manifest, productions, terminals, frozen_sources
    )
    action_schema = validate_action_schema(productions)
    action_schema["source"] = {
        "grammar_blob_oid": grammar_oid,
        "grammar_path": GRAMMAR_PATH,
        "manifest_oracle_commit": commit,
    }
    action_schema_text = stable_json(action_schema, pretty=True)
    action_schema_sha256 = sha256_text(action_schema_text)

    instances = build_instances(productions)
    facts, alternative_facts, iterations = compute_facts(
        instances, productions, len(terminals)
    )
    keys_by_production: dict[str, list[InstanceKey]] = {
        name: [] for name in productions
    }
    for key in instances:
        keys_by_production[key.name].append(key)

    missing_generic_instances = [
        name
        for name, production in productions.items()
        if production.params and not keys_by_production[name]
    ]
    if missing_generic_instances:
        fail(f"generic productions have no concrete call sites: {missing_generic_instances}")

    selected: list[tuple[Production, tuple[str, ...]]] = []
    for name in sorted(productions):
        production = productions[name]
        key = InstanceKey(name)
        if key not in facts:
            continue
        leads = direct_selection(production, facts[key])
        if leads is not None:
            selected.append((production, leads))

    if not SHARED_RUNTIME_PATH.is_file():
        fail(f"shared parser runtime is missing: {SHARED_RUNTIME_PATH.relative_to(ROOT)}")
    shared_runtime_text = SHARED_RUNTIME_PATH.read_text(encoding="utf-8")
    type_leaf_text = canonical_pr(
        render_type_leaf(action_schema_sha256, "Syntax.Parse.GeneratedControl")
    )
    production_type_text = canonical_pr(
        render_type_leaf(action_schema_sha256, "Syntax.Parse.GeneratedControl")
    )
    if not TYPE_LEAF_TEST_PATH.is_file():
        fail(
            "independent Type behavior fixture is missing: "
            f"{TYPE_LEAF_TEST_PATH.relative_to(ROOT)}"
        )
    type_leaf_test_text = TYPE_LEAF_TEST_PATH.read_text(encoding="utf-8")
    type_leaf_manifest_text = (
        '[package]\n'
        'name = "parser_generator_type_leaf"\n'
        'version = "0.0.0"\n'
        'authors = ["Stephen Diehl <stephen.m.diehl@gmail.com>"]\n'
        'maintainers = ["stephen.m.diehl@gmail.com"]\n'
        'license = "MIT"\n'
        "\n"
        "[bin]\n"
        'entry = "src/main.pr"\n'
    )
    type_leaf_main_text = "fn main() = ()\n"
    generator_text = Path(__file__).read_text(encoding="utf-8")
    production_type_consumer_text = PRODUCTION_TYPE_CONSUMER.read_text(
        encoding="utf-8"
    )
    production_promoted = candidate_type_consumer_integrated(
        production_type_consumer_text
    )
    if not production_promoted:
        fail("production GeneratedType ownership requires promoted Type consumer "
             "markers; refusing to silently disable freshness")
    production_type_lines = code_lines(production_type_text, "--")
    production_facade_lines = code_lines(production_type_consumer_text, "--")
    control_lines = code_lines(shared_runtime_text, "--")
    type_leaf_lines = code_lines(type_leaf_text, "--")
    type_leaf_test_count = sum(
        line.startswith("test fn ") for line in type_leaf_test_text.splitlines()
    )
    if type_leaf_test_count != 55:
        fail(
            "independent Type behavior fixture must contain exactly 55 tests "
            f"(found {type_leaf_test_count})"
        )
    generator_lines = code_lines(generator_text, "#")
    plan = compact_plan(locals())
    return BuildResult(
        stable_json(plan, pretty=True),
        action_schema_text,
        shared_runtime_text,
        type_leaf_text,
        production_type_text,
        type_leaf_manifest_text,
        type_leaf_main_text,
        type_leaf_test_text,
        plan,
    )


def verify_build() -> BuildResult:
    first = build()
    if first.outputs() != build().outputs():
        fail("rendering is not deterministic across two in-process builds")
    if first.plan["manifest_validation"]["production_count"] != 133:
        fail("self-test expected 133 frozen productions")
    selected = first.plan["predictive_validation"]["productions"]
    if len(selected) != 45 or not {"CmpOp", "Program"} <= set(selected):
        fail("direct-FIRST validation must retain exactly 45 safe productions")
    if {"Expr", "Type", "Call"} & set(selected):
        fail("contextual/Pratt productions entered direct-FIRST selection")
    schema = json.loads(first.action_schema_text)
    if len(schema["entries"]) != 65:
        fail("typed Type/Pattern schema must contain all sixty-five pinned action rows")
    source = first.type_leaf_text
    production_source = first.production_type_text
    control = first.shared_runtime_text
    if source.count("pub fn generated_parse_type_arg(") != 1:
        fail("TypeArg must expose exactly one production entry")
    for marker in (
        "pub fn generated_parse_type(", "pub fn generated_parse_type_head(",
        "pub fn generated_parse_type_arg_with(",
        "pub fn generated_parse_effect_row(", "pub fn generated_parse_eff_label(",
        "GROptionalArgs", "generated_parse_delimited(",
    ):
        if marker not in source:
            fail(f"generated Type-spine marker is missing: {marker}")
    for marker in (
        "pub type GeneratedSeparatedPhase",
        "pub fn generated_bind(",
        "pub fn generated_spend(",
        "pub fn generated_separated(",
        "GSRequiredFirst",
        "GSAfterSeparator",
    ):
        if marker not in control:
            fail(f"shared parser runtime marker is missing: {marker}")
    if "import Syntax.Parse.GeneratedControl (..)" not in source:
        fail("isolated generated Type must import the stdlib parser runtime")
    if "import Syntax.Parse.GeneratedControl (..)" not in production_source:
        fail("production generated Type must import shared generated control")
    for duplicate in ("fn generated_bind(", "fn generated_comma("):
        if duplicate in source or duplicate in production_source:
            fail(f"generated Type retained duplicated control: {duplicate}")
    if first.plan["type_leaf_emission"]["test_fixture"]["test_count"] != 55:
        fail("generated Type project must contain fifty-five independent tests")
    # Whether generation compacts the maintained parser is the question this
    # experiment exists to answer, so the answer is recorded rather than
    # asserted: `maintained_t_delta` and the verdict beside it are part of
    # plan.json, and `check` regenerates and diffs that file, so the number
    # cannot move without a human reading the diff. Asserting an improvement
    # here would instead make an unfavorable result look like a broken build.
    #
    # It is currently unfavorable. Measured in canonical layout on both sides,
    # generation costs lines rather than saving them: the earlier saving came
    # from comparing compact machine emission against verbosely hand-written
    # source, and disappears once both are formatted the same way.
    return first


def self_test() -> BuildResult:
    return verify_build()


def check_outputs(result: BuildResult) -> None:
    mismatches: list[str] = []
    for path, text in result.outputs():
        if not path.exists():
            mismatches.append(f"{path.relative_to(ROOT)} is missing")
        elif path.read_text(encoding="utf-8") != text:
            mismatches.append(f"{path.relative_to(ROOT)} is stale")
    if mismatches:
        fail("generated output check failed:\n  - " + "\n  - ".join(mismatches))


def write_outputs(result: BuildResult) -> None:
    for path, text in result.outputs():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "command",
        nargs="?",
        default="generate",
        choices=("generate", "promote", "check", "self-test"),
    )
    args = parser.parse_args(argv)
    try:
        result = self_test() if args.command == "self-test" else build()
        if args.command in ("generate", "promote"):
            write_outputs(result)
            print(
                f"{'promoted' if args.command == 'promote' else 'wrote'} "
                f"{len(result.outputs())} deterministic artifacts "
                f"({result.plan['predictive_validation']['production_count']} "
                "validated predictive selections, "
                f"{result.plan['type_leaf_emission']['action_schema']['entry_count']} "
                "typed leaf actions)"
            )
        elif args.command == "check":
            check_outputs(result)
            print("generated outputs are deterministic and current")
        else:
            print(
                "self-test passed: "
                f"{result.plan['manifest_validation']['production_count']} productions, "
                f"{result.plan['analysis']['concrete_instance_count']} instances, "
                f"{result.plan['predictive_validation']['production_count']} "
                "validated predictive selections, "
                f"{result.plan['type_leaf_emission']['action_schema']['entry_count']} "
                "typed leaf actions"
            )
    except GeneratorError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
