// The `prism-index-v1` artifact as the viewer reads it: the wire types, plus the
// two lookups a wire format deliberately does not carry.
//
// The artifact is a flat list of definitions and a flat, sorted list of edges,
// which is the right shape for something deterministic and diffable and the wrong
// shape for a interface that has to answer "who calls this" on a click. Building
// the indexes here, once, is the consumer's job; `Index::def` on the Rust side
// says the same thing about looking definitions up in a loop.

/// Every relation `prism index` derives.
export type EdgeKind = "calls" | "uses-type" | "performs" | "handles" | "instance-of" | "tests";

export interface Edge {
  kind: EdgeKind;
  from: string;
  to: string;
}

/// What the relation lookups below are built over: a revision's definitions
/// and edges. The loaded index is one; the old revision a diff can rebuild
/// (`Revisions.before`) is another, and the lookups do not care which.
export interface Graph {
  defs: Def[];
  byId: Map<string, Def>;
  edges: Edge[];
}

export type Kind =
  | "value"
  | "const"
  | "test"
  | "logic"
  | "type"
  | "synonym"
  | "row-alias"
  | "effect"
  | "error"
  | "class"
  | "instance"
  | "pattern"
  | "stable";

/// One name written inside a definition's `source`, and what it resolves to.
/// Offsets index `source` directly, so rendering a navigable body is a
/// slice-and-join with no coordinate translation.
export interface SourceRef {
  start: number;
  end: number;
  /// May name a definition the index does not contain (a builtin, a prelude
  /// function outside this artifact), exactly as an edge endpoint may.
  target: string;
}

/// A name a declaration introduces inside itself, and where its own text says it.
export interface Member {
  name: string;
  start: number;
  end: number;
}

export interface Def {
  /// The canonical name: the index's key, and this viewer's URL.
  id: string;
  name: string;
  module: string;
  kind: Kind;
  /// Absent for the kinds that have no independent content address.
  hash?: string;
  ty?: string;
  /// Highlight spans over `ty`, packed like `tokens`. A rendered type is not
  /// source, but it is written in the language's type syntax, so the compiler's
  /// own lexer classifies it and the viewer needs no second tokenizer.
  ty_tokens?: string;
  /// Names inside `ty` that resolve to definitions.
  ty_refs?: SourceRef[];
  effects?: string;
  /// Highlight spans over `effects`, packed like `tokens`.
  eff_tokens?: string;
  /// Names inside `effects` that resolve to definitions.
  eff_refs?: SourceRef[];
  source: string;
  span: { start: number; end: number };
  vis?: "private" | "public" | "opaque";
  doc?: string;
  claims?: string[];
  deprecated?: string;
  /// The constructors, methods or operations this declaration introduces. From
  /// the compiler's own declaration lists, so an unused member is here too.
  members?: Member[];
  /// Resolved names inside `source`, in source order.
  refs?: SourceRef[];
  /// Highlight spans over `source`, as `gap length class` triples. See
  /// `decodeSpans`.
  tokens?: string;
  /// The type of each name written in `source`, packed like `tokens` but indexing
  /// the shared `type_table`. Variables only, so the spans never nest.
  types?: string;
}

/// One highlight span, decoded.
export interface TokenSpan {
  start: number;
  end: number;
  cls: string;
}

/// Decode a definition's packed highlight spans.
///
/// The artifact stores `gap length class` triples: the gap from the previous span's
/// end and the class index into the shared table. A pretty-printed JSON
/// array would spend more bytes on indentation than on the data. Unstyled spans
/// are absent, so a gap is not always zero.
export function decodeSpans(packed: string | undefined, classes: string[]): TokenSpan[] {
  if (!packed) return [];
  const n = packed.split(" ");
  const out: TokenSpan[] = [];
  let at = 0;
  for (let i = 0; i + 2 < n.length; i += 3) {
    const start = at + Number(n[i]);
    const end = start + Number(n[i + 1]);
    out.push({ start, end, cls: classes[Number(n[i + 2])] ?? "" });
    at = end;
  }
  return out;
}

export interface IndexModule {
  dotted: string;
  path: string;
  doc?: string;
  prelude?: boolean;
  source?: string;
  /// The front end's diagnostic when this module did not parse; its definitions
  /// are then absent from the artifact rather than the module being empty.
  error?: string;
}

export interface Envelope {
  format: string;
  scheme: string;
  compiler: string;
  contract: string;
  title: string;
  tests: "included" | "empty" | { unavailable: string };
}

/// One compiler primitive: what source calls it, its type where the compiler
/// records one, and the compiler's own sentence about it.
export interface Primitive {
  name: string;
  kind?: "value" | "type" | "effect";
  signature?: string;
  doc?: string;
}

interface Wire {
  envelope: Envelope;
  modules: IndexModule[];
  defs: Def[];
  edges: Edge[];
  builtins?: Primitive[];
  token_classes?: string[];
  type_table?: string[];
}

const FORMAT = "prism-index-v1";

/// A decoded index with its definitions keyed by canonical name.
export class Index {
  readonly envelope: Envelope;
  readonly modules: IndexModule[];
  readonly defs: Def[];
  readonly byId: Map<string, Def>;
  readonly edges: Edge[];
  /// The compiler's own primitives, by name. One of these has no definition
  /// anywhere, so it is not a link. It is also not missing, and saying which
  /// of the two it is is the difference between "primitive" and "this index is
  /// incomplete". Its signature is what makes it readable rather than merely named.
  readonly builtins: Map<string, Primitive>;
  /// The highlight categories `Def::tokens` indexes.
  readonly tokenClasses: string[];
  /// The rendered types `Def::types` indexes.
  readonly typeTable: string[];

  constructor(wire: Wire) {
    // Refuse a format this viewer does not understand rather than rendering a
    // half-recognized artifact: the envelope exists precisely so a consumer can
    // tell before reading a single definition.
    if (wire?.envelope?.format !== FORMAT) {
      throw new Error(`not a ${FORMAT} artifact (found "${wire?.envelope?.format ?? "nothing"}")`);
    }
    this.envelope = wire.envelope;
    this.modules = wire.modules;
    this.defs = wire.defs;
    this.edges = wire.edges;
    this.byId = new Map(wire.defs.map((d) => [d.id, d]));
    this.builtins = new Map((wire.builtins ?? []).map((p) => [p.name, p]));
    this.tokenClasses = wire.token_classes ?? [];
    this.typeTable = wire.type_table ?? [];
    for (const d of this.defs) rebase(d, this.tokenClasses, this.typeTable);
  }

  /// The primitive a target names, if it names one. A qualified spelling
  /// (`Wire.bytes_at`) is still that primitive.
  primitive(target: string): Primitive | undefined {
    const bare = target.split(/[.@]/).at(-1) ?? target;
    return this.builtins.get(target) ?? this.builtins.get(bare);
  }

  /// How a reference target should read: a definition to navigate to, a named
  /// primitive, or a name that genuinely leaves this artifact.
  classify(target: string): "definition" | "builtin" | "elsewhere" {
    if (this.byId.has(target)) return "definition";
    return this.primitive(target) ? "builtin" : "elsewhere";
  }

  /// What to say about a target on hover: what it is, and above all its type.
  ///
  /// The type is the answer to "what is this" far more often than the name is,
  /// which is why it leads for a definition and why a primitive carries its
  /// signature at all.
  describe(target: string): string {
    const d = this.byId.get(target);
    if (d) {
      const lines = [target];
      if (d.ty) lines.push(d.ty);
      if (d.effects) lines.push(`effects ${d.effects}`);
      lines.push(d.module ? `${d.kind} in ${d.module}` : d.kind);
      if (d.deprecated) lines.push(`deprecated: ${d.deprecated}`);
      return lines.join("\n");
    }
    const prim = this.primitive(target);
    if (prim) {
      return [prim.name, prim.signature, prim.doc, "compiler builtin: no Prism definition"]
        .filter((l): l is string => Boolean(l))
        .join("\n");
    }
    return `${target}\nnot in this index`;
  }
}

/// Both directions of every edge kind, keyed for lookup.
///
/// Traversal has to be symmetric: "what does this call" and "what calls this" are
/// the same edge read from opposite ends, and a reviewer moves along it in both
/// directions equally often.
export class Relations {
  private readonly out = new Map<string, string[]>();
  private readonly inn = new Map<string, string[]>();

  constructor(index: Graph) {
    for (const e of index.edges) {
      push(this.out, `${e.kind} ${e.from}`, e.to);
      push(this.inn, `${e.kind} ${e.to}`, e.from);
    }
  }

  get(kind: EdgeKind, dir: "in" | "out", id: string): string[] {
    return (dir === "out" ? this.out : this.inn).get(`${kind} ${id}`) ?? [];
  }
}

/// What each definition's own source names, and who names it.
///
/// The dependency graph and the text answer different questions, and a reviewer
/// asks the text's. Elaboration inlines a top-level `let`, so a body that writes
/// `gen_float` depends on whatever the constant expanded to and not on the
/// constant. Across the standard library's 73 consts, exactly one is ever a
/// dependency. Reading the occurrence set instead gives back what is on the page.
///
/// Terms only. A written type, constructor or class method resolves to the
/// declaration that owns it, and those already have rows of their own.
export class Mentions {
  private readonly out = new Map<string, string[]>();
  private readonly inn = new Map<string, string[]>();

  constructor(index: Graph) {
    const term = (id: string): boolean => {
      const kind = index.byId.get(id)?.kind;
      return kind === "value" || kind === "const" || kind === "test" || kind === "logic";
    };
    // Deduplicated, and in the order the source names them: a body that calls the
    // same function three times relates to it once.
    const once = (map: Map<string, string[]>, key: string, value: string): void => {
      const at = map.get(key);
      if (!at) map.set(key, [value]);
      else if (!at.includes(value)) at.push(value);
    };
    for (const d of index.defs) {
      for (const r of d.refs ?? []) {
        if (r.target === d.id || !term(r.target)) continue;
        once(this.out, d.id, r.target);
        once(this.inn, r.target, d.id);
      }
    }
  }

  get(dir: "in" | "out", id: string): string[] {
    return (dir === "out" ? this.out : this.inn).get(id) ?? [];
  }
}

/// A class method, effect operation, or data constructor as another definition
/// wrote it.
export interface MemberUse {
  /// The name as written: `pure`, `Cons`, `get`.
  name: string;
  /// The declaration that owns it, which is what a reference to it resolves to.
  owner: string;
}

/// Who uses a declaration's members, and which member they used.
///
/// A reference to a member resolves to the declaration that owns it: `Cons` to
/// `List`, `pure` to `Applicative`, an operation to its effect. That is the right
/// destination because the declaration is where the member is introduced and typed,
/// but on its own it throws away *which* member was meant, and 28% of every
/// reference in the standard library is one of these.
///
/// The occurrence rows keep enough to recover it: a reference carries the span it
/// covers, so the text at that span is the member's name as written. Reading the
/// whole reference set from the far end turns that back into "who uses `pure`",
/// at member granularity, for every kind of member at once.
///
/// Member-use data is required because a class method is dispatched through a
/// dictionary, leaving no dependency-graph edge for the call.
/// `Data.Monad.map2` calls `ap` and `fmap` and has *zero* outgoing edges. Without
/// this the relation strip is silent in both directions.
export class Members {
  /// owner → member name → the definitions that write it, deduplicated.
  private readonly byOwner = new Map<string, Map<string, string[]>>();
  /// definition → the members its own source names.
  private readonly byUser = new Map<string, MemberUse[]>();

  constructor(index: Graph) {
    // Seeded from the declarations themselves, so a member nothing uses is still a
    // member: an effect's operations are performed by *programs*, so a library
    // index would otherwise list none of `Output`'s.
    for (const d of index.defs) {
      for (const m of d.members ?? []) {
        const members = this.byOwner.get(d.id) ?? new Map<string, string[]>();
        if (!members.has(m.name)) members.set(m.name, []);
        this.byOwner.set(d.id, members);
      }
    }
    for (const d of index.defs) {
      for (const r of d.refs ?? []) {
        const owner = index.byId.get(r.target);
        // A declaration is not a *user* of its own members: writing `Bin` inside
        // `type Map = Tip | Bin(..)` (or a sibling method in a default body) is
        // the declaration talking about itself, and its card is already open.
        if (!owner || owner.id === d.id) continue;
        const name = tail(d.source.slice(r.start, r.end));
        if (name === owner.name || name === "") continue;
        const members = this.byOwner.get(owner.id) ?? new Map<string, string[]>();
        const users = members.get(name) ?? [];
        if (!users.includes(d.id)) users.push(d.id);
        members.set(name, users);
        this.byOwner.set(owner.id, members);
        const used = this.byUser.get(d.id) ?? [];
        if (!used.some((u) => u.name === name && u.owner === owner.id)) {
          used.push({ name, owner: owner.id });
        }
        this.byUser.set(d.id, used);
      }
    }
  }

  /// The members of `owner` that anything uses, each with its users.
  of(owner: string): [string, string[]][] {
    return [...(this.byOwner.get(owner) ?? new Map<string, string[]>())].sort((a, b) =>
      a[0].localeCompare(b[0]),
    );
  }

  /// Who uses one member of one declaration.
  users(owner: string, name: string): string[] {
    return this.byOwner.get(owner)?.get(name) ?? [];
  }

  /// The members `id`'s own source names.
  usedBy(id: string): MemberUse[] {
    return this.byUser.get(id) ?? [];
  }
}

/// The unqualified tail of a written name: `L.text` was a use of `text`.
const tail = (written: string): string => written.split(/[.@]/).at(-1) ?? written;

/// What happened to a definition between two revisions.
export type Status = "added" | "removed" | "moved" | "changed" | "cone" | "cosmetic";

export interface DiffEntry {
  status: Status;
  id: string;
  old_id?: string;
  old?: Def;
  new?: Def;
}

/// One side of a diff: which revision it was, and the shared tables its carried
/// definition records index. The records were copied out of their index, whose
/// `token_classes`/`type_table` did not travel with them, and the two revisions'
/// tables can order entries differently, so each side brings its own.
interface DiffSide {
  title: string;
  contract: string;
  token_classes?: string[];
  type_table?: string[];
}

interface DiffWire {
  envelope: {
    format: string;
    old: DiffSide;
    new: DiffSide;
    counts: Record<Status | "unchanged", number>;
  };
  entries: DiffEntry[];
  /// The edges one revision has and the other does not. Absent from an
  /// artifact older than the field, which is "unknown", not "none".
  edges?: { added?: Edge[]; removed?: Edge[] };
}

const DIFF_FORMAT = "prism-index-diff-v1";

/// The left-hand revision, overlaid on the index that is the right-hand one.
///
/// The viewer's subject is a revision *pair*; a plain index is the degenerate
/// case where both sides are the same. Keeping the overlay separate is what makes
/// that true without a second code path: every card renders the same way and
/// consults this for whatever the other revision had.
export class Revisions {
  readonly envelope: DiffWire["envelope"];
  /// What moved in the dependency graph, or `null` when the artifact predates
  /// the delta and cannot say.
  readonly edges: { added: Edge[]; removed: Edge[] } | null;
  /// The renames the diff knows as facts: old canonical name to new.
  readonly movedTo = new Map<string, string>();
  private readonly byId = new Map<string, DiffEntry>();

  /// `classes` and `types` belong to the index loaded in the viewer. They are the
  /// tables every card paints against. Each side's records arrive indexing its own
  /// revision's tables (carried in the envelope), so they are re-encoded into the
  /// viewer's table space first, and then their offsets get the same move from
  /// bytes to code units that `Index` does for its own.
  ///
  /// `against` is the loaded index's contract. A diff records the revision its
  /// new side came from, and overlaying it on any other index would present old
  /// bodies against definitions they were never compared with. A stale `?diff=`
  /// must be refused, not rendered.
  constructor(wire: DiffWire, classes: string[] = [], types: string[] = [], against?: string) {
    if (wire?.envelope?.format !== DIFF_FORMAT) {
      throw new Error(
        `not a ${DIFF_FORMAT} artifact (found "${wire?.envelope?.format ?? "nothing"}")`,
      );
    }
    if (against !== undefined && wire.envelope.new.contract !== against) {
      throw new Error(
        `this diff was made against a different revision (its new side is ` +
          `${wire.envelope.new.contract.slice(0, 12)}…, the loaded index is ` +
          `${against.slice(0, 12)}…); regenerate it with \`prism index --diff\``,
      );
    }
    this.envelope = wire.envelope;
    this.edges = wire.edges
      ? { added: wire.edges.added ?? [], removed: wire.edges.removed ?? [] }
      : null;
    for (const e of wire.entries) {
      if (e.old) adopt(e.old, wire.envelope.old, classes, types);
      if (e.new) adopt(e.new, wire.envelope.new, classes, types);
      this.byId.set(e.id, e);
      if (e.status === "moved" && e.old_id !== undefined) this.movedTo.set(e.old_id, e.id);
    }
  }

  /// The old revision's definitions and edges, rebuilt from the new revision's
  /// and this diff.
  ///
  /// The artifact carries what differs and nothing else, so the other side is
  /// recovered rather than read: every definition the diff does not mention is
  /// the same on both sides, and every edge not in the delta likewise. The
  /// result is what lets a card ask the old revision the same questions it asks
  /// the new one, who called this and what it called, through the same lookups.
  /// `null` when the artifact carries no edge delta, since a graph with the
  /// old definitions and the new edges would answer those questions wrongly.
  before(index: Index): Graph | null {
    if (!this.edges) return null;
    const byId = new Map(index.byId);
    for (const e of this.byId.values()) {
      byId.delete(e.id);
      if (e.old) byId.set(e.old_id ?? e.id, e.old);
    }
    const added = new Set(this.edges.added.map(edgeKey));
    const edges = [...index.edges.filter((e) => !added.has(edgeKey(e))), ...this.edges.removed];
    return { defs: [...byId.values()], byId, edges };
  }

  get(id: string): DiffEntry | undefined {
    return this.byId.get(id);
  }

  /// Entries in artifact order, which is authored changes first.
  all(): DiffEntry[] {
    return [...this.byId.values()];
  }
}

/// Bring one side's definition record into the viewer's table space, then move
/// its offsets from bytes to code units.
///
/// Re-encoding rather than borrowing: the packed spans index the tables of the
/// index they were copied from, and the viewer paints everything against the
/// loaded index's tables. A class or rendered type the viewer's table lacks is
/// appended to it, so an old revision's spans stay decodable even where the two
/// revisions' tables disagree.
function adopt(d: Def, side: DiffSide, classes: string[], types: string[]): void {
  d.tokens = retable(d.tokens, side.token_classes, classes);
  d.ty_tokens = retable(d.ty_tokens, side.token_classes, classes);
  d.eff_tokens = retable(d.eff_tokens, side.token_classes, classes);
  d.types = retable(d.types, side.type_table, types);
  rebase(d, classes, types);
}

/// Re-encode packed spans from the table they were written against into `to`,
/// appending entries `to` lacks. A record with no source table (an artifact
/// predating the carried tables, or a test fixture built directly against the
/// viewer's) is taken as already being in the target space.
function retable(
  packed: string | undefined,
  from: string[] | undefined,
  to: string[],
): string | undefined {
  if (!packed || !from) return packed;
  const out: number[] = [];
  let prev = 0;
  for (const span of decodeSpans(packed, from)) {
    let cls = to.indexOf(span.cls);
    if (cls < 0) {
      cls = to.length;
      to.push(span.cls);
    }
    out.push(span.start - prev, span.end - span.start, cls);
    prev = span.end;
  }
  return out.join(" ");
}

/// Move every offset in a definition from bytes to JavaScript string indices.
///
/// The artifact counts in UTF-8 bytes, because that is what the compiler's spans
/// are and what a consumer holding the file on disk needs. A JavaScript string is
/// indexed in UTF-16 code units. The two agree on ASCII and nowhere else, which is
/// why the box-drawing characters in `Syntax.Report`, the standard library's first
/// non-ASCII definition bodies, put that definition's last highlight span three
/// bytes past the end of its own source, and slid every link after them onto the
/// wrong text. Translating once, here, is what keeps the rest of the viewer from
/// having to know which unit it is holding.
///
/// Note what did *not* catch this: the check that stripping markup from a rendered
/// body returns the source exactly. Painting emits contiguous slices, so a shifted
/// span still reproduces the text; only the boundaries move. The range check did.
function rebase(d: Def, classes: string[], types: string[] = []): void {
  const source = units(d.source);
  if (source) {
    d.tokens = repack(d.tokens, classes, source);
    d.types = repack(d.types, types, source);
    d.refs = d.refs?.map((r) => ({ ...r, ...at(source, r) }));
    d.members = d.members?.map((m) => ({ ...m, ...at(source, m) }));
  }
  const ty = d.ty === undefined ? null : units(d.ty);
  if (ty) {
    d.ty_tokens = repack(d.ty_tokens, classes, ty);
    d.ty_refs = d.ty_refs?.map((r) => ({ ...r, ...at(ty, r) }));
  }
  const eff = d.effects === undefined ? null : units(d.effects);
  if (eff) {
    d.eff_tokens = repack(d.eff_tokens, classes, eff);
    d.eff_refs = d.eff_refs?.map((r) => ({ ...r, ...at(eff, r) }));
  }
}

/// A byte offset to code-unit offset table, or `null` when the text is ASCII and
/// the two coincide. This covers all but a handful of definitions, so the common
/// case allocates nothing.
function units(text: string): Int32Array | null {
  let ascii = true;
  for (let i = 0; i < text.length; i++) {
    if (text.charCodeAt(i) > 127) {
      ascii = false;
      break;
    }
  }
  if (ascii) return null;
  const map = new Int32Array(new TextEncoder().encode(text).length + 1);
  let byte = 0;
  for (let unit = 0; unit < text.length; ) {
    const code = text.codePointAt(unit) ?? 0;
    const wide = code >= 0x10000;
    const width = code < 0x80 ? 1 : code < 0x800 ? 2 : wide ? 4 : 3;
    // Every byte of a character maps to where the character starts; a span should
    // never land mid-character, and if one does it clamps to a boundary.
    for (let k = 0; k < width; k++) map[byte + k] = unit;
    byte += width;
    unit += wide ? 2 : 1;
  }
  map[map.length - 1] = text.length;
  return map;
}

const at = <T extends { start: number; end: number }>(
  map: Int32Array,
  span: T,
): { start: number; end: number } => ({
  start: map[Math.min(span.start, map.length - 1)] ?? span.start,
  end: map[Math.min(span.end, map.length - 1)] ?? span.end,
});

/// Re-pack highlight spans against the translated offsets, in the same
/// `gap length class` encoding they arrived in.
function repack(packed: string | undefined, classes: string[], map: Int32Array): string {
  const out: number[] = [];
  let prev = 0;
  for (const span of decodeSpans(packed, classes)) {
    const { start, end } = at(map, span);
    out.push(start - prev, end - start, classes.indexOf(span.cls));
    prev = end;
  }
  return out.join(" ");
}

const edgeKey = (e: Edge): string => `${e.kind} ${e.from} ${e.to}`;

function push(map: Map<string, string[]>, key: string, value: string): void {
  const at = map.get(key);
  if (at) at.push(value);
  else map.set(key, [value]);
}
