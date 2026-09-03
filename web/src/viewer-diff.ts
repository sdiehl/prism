// Comparing two texts, for the revision pair a card shows.
//
// The index diff says *that* a definition changed, and carries both revisions of
// it; it does not say where. Two full bodies side by side leave the reader to find
// the edit by eye, which on anything longer than a few lines is most of the work a
// diff exists to remove. So the viewer draws a real one: lines are aligned by the
// shortest edit script, and within a changed line the words that moved are marked,
// so a one-token change in a twelve-line body reads as one token.
//
// Deliberately not a diff library. The viewer is a self-contained reader of one
// JSON file, no wasm and no dependencies, and the painting is already its own:
// every name in a body is a link and every token a class the compiler chose, and
// a library that renders diffs would render them without either. What is needed
// is the alignment, which is Myers' algorithm and fits in a screen.

/// One step of an edit script: a line (or token) kept, dropped, or introduced.
/// Indices are into the old (`a`) and new (`b`) sequences.
export type Op =
  | { kind: "eq"; a: number; b: number }
  | { kind: "del"; a: number }
  | { kind: "ins"; b: number };

// Retaining one full diagonal array per edit-distance round is what makes Myers
// easy to walk backward, but its worst case is quadratic. Past this many cells,
// preserve the common ends and render the unrelated middle as one replacement;
// a coarse diff is more useful than a viewer tab lost to memory pressure.
const MAX_TRACE_CELLS = 4_000_000;

/// The shortest edit script from `a` to `b` (Myers, 1986), with a bounded
/// coarse fallback for unusually large, unrelated inputs.
///
/// The greedy forward search with a trace of each round's furthest-reaching
/// paths, walked back from the end. O((N+M)·D) time and memory, where D is the
/// edit distance; a definition's two revisions are mostly the same text, so
/// D is small where N is large.
export function diff<T>(
  a: readonly T[],
  b: readonly T[],
  eq: (x: T, y: T) => boolean = same,
): Op[] {
  const n = a.length;
  const m = b.length;
  const max = n + m;
  // `v[k]` is the furthest x reached on diagonal k; shifted by `off` so that
  // negative diagonals index an array.
  const off = max + 1;
  const v = new Int32Array(2 * max + 3);
  const trace: Int32Array[] = [];
  for (let d = 0; d <= max; d++) {
    if ((trace.length + 1) * v.length > MAX_TRACE_CELLS) return coarse(a, b, eq);
    trace.push(v.slice());
    for (let k = -d; k <= d; k += 2) {
      let x =
        k === -d || (k !== d && v[off + k - 1] < v[off + k + 1])
          ? v[off + k + 1]
          : v[off + k - 1] + 1;
      let y = x - k;
      while (x < n && y < m && eq(a[x], b[y])) {
        x++;
        y++;
      }
      v[off + k] = x;
      if (x >= n && y >= m) return backtrack(trace, off, n, m);
    }
  }
  // Unreachable: the search always terminates by round `max`.
  return backtrack(trace, off, n, m);
}

// A valid edit script that keeps the shared prefix and suffix and treats the
// middle as one replacement. Used only when retaining the shortest script's
// trace would exceed the memory budget above.
function coarse<T>(a: readonly T[], b: readonly T[], eq: (x: T, y: T) => boolean): Op[] {
  let head = 0;
  while (head < a.length && head < b.length && eq(a[head], b[head])) head++;
  let oldTail = a.length;
  let newTail = b.length;
  while (oldTail > head && newTail > head && eq(a[oldTail - 1], b[newTail - 1])) {
    oldTail--;
    newTail--;
  }
  const out: Op[] = [];
  for (let i = 0; i < head; i++) out.push({ kind: "eq", a: i, b: i });
  for (let i = head; i < oldTail; i++) out.push({ kind: "del", a: i });
  for (let i = head; i < newTail; i++) out.push({ kind: "ins", b: i });
  for (let i = 0; oldTail + i < a.length; i++) {
    out.push({ kind: "eq", a: oldTail + i, b: newTail + i });
  }
  return out;
}

const same = <T>(x: T, y: T): boolean => x === y;

function backtrack(trace: Int32Array[], off: number, n: number, m: number): Op[] {
  const ops: Op[] = [];
  let x = n;
  let y = m;
  for (let d = trace.length - 1; d >= 0; d--) {
    const v = trace[d];
    const k = x - y;
    const prevK = k === -d || (k !== d && v[off + k - 1] < v[off + k + 1]) ? k + 1 : k - 1;
    const prevX = v[off + prevK];
    const prevY = prevX - prevK;
    while (x > prevX && y > prevY) {
      ops.push({ kind: "eq", a: x - 1, b: y - 1 });
      x--;
      y--;
    }
    if (d > 0) ops.push(x === prevX ? { kind: "ins", b: y - 1 } : { kind: "del", a: x - 1 });
    x = prevX;
    y = prevY;
  }
  return ops.reverse();
}

/// A run of kept lines, or one edit: the old lines it drops and the new ones it
/// introduces, together.
///
/// An `eq` pair means the two lines are byte-identical; a line edited *within*
/// is a del and an ins in a `change` block, re-paired by `textDiff` for its
/// word-level marks. The script interleaves drops and introductions however the
/// search happened to reach them; a reader wants each edit as one thing, old
/// above (or beside) new.
export type Block =
  | { kind: "eq"; pairs: [number, number][] }
  | { kind: "change"; dels: number[]; inss: number[] };

export function blocks(ops: Op[]): Block[] {
  const out: Block[] = [];
  for (const op of ops) {
    const last = out.at(-1);
    if (op.kind === "eq") {
      if (last?.kind === "eq") last.pairs.push([op.a, op.b]);
      else out.push({ kind: "eq", pairs: [[op.a, op.b]] });
    } else if (last?.kind === "change") {
      if (op.kind === "del") last.dels.push(op.a);
      else last.inss.push(op.b);
    } else {
      out.push(
        op.kind === "del"
          ? { kind: "change", dels: [op.a], inss: [] }
          : { kind: "change", dels: [], inss: [op.b] },
      );
    }
  }
  return out;
}

/// A half-open span of one text, in code units.
export type Range = [number, number];

/// Two revisions of one text, compared line by line and then, inside each edited
/// line, word by word: how the lines align, and what to emphasise inside them.
export interface TextDiff {
  /// The line alignment. Indices are into each text's lines, in order.
  blocks: Block[];
  /// The words that moved inside edited lines (the marks a rendered diff
  /// highlights), as absolute spans of each whole text: the painter works over
  /// the whole text, not line by line. Empty for a line that was replaced
  /// outright rather than edited.
  oldEmph: Range[];
  newEmph: Range[];
}

/// The threshold below which two paired lines are called a replacement rather
/// than an edit, and nothing inside them is marked: marking most of a line
/// says less than tinting all of it. The ratio is shared characters over the
/// longer line.
const ALIKE = 0.4;

export function textDiff(oldText: string, newText: string): TextDiff {
  // No text has no lines. Keeping `""` as one artificial line makes a field
  // added or removed in unified mode index a painted line that does not exist.
  const oldLines = oldText === "" ? [] : oldText.split("\n");
  const newLines = newText === "" ? [] : newText.split("\n");
  const oldStarts = starts(oldLines);
  const newStarts = starts(newLines);
  const bs = blocks(diff(oldLines, newLines));
  const oldEmph: Range[] = [];
  const newEmph: Range[] = [];
  for (const b of bs) {
    if (b.kind !== "change") continue;
    // Pair the dropped lines with the introduced ones in order. A block that
    // drops three and introduces four is, nearly always, three edited lines and
    // one new one; pairing by position is what every diff tool does, and the
    // likeness test below catches the cases where it is wrong.
    for (let i = 0; i < Math.min(b.dels.length, b.inss.length); i++) {
      const a = b.dels[i];
      const c = b.inss[i];
      const within = wordDiff(oldLines[a], newLines[c]);
      if (!within) continue;
      for (const [s, e] of within.old) oldEmph.push([oldStarts[a] + s, oldStarts[a] + e]);
      for (const [s, e] of within.new) newEmph.push([newStarts[c] + s, newStarts[c] + e]);
    }
  }
  return { blocks: bs, oldEmph, newEmph };
}

// Where each part starts when the parts are joined by a separator of `sep`
// characters: lines by a newline, tokens by nothing.
function starts(parts: string[], sep = 1): number[] {
  const out: number[] = [];
  let at = 0;
  for (const p of parts) {
    out.push(at);
    at += p.length + sep;
  }
  return out;
}

/// One line's tokens: words, runs of space, and single punctuation marks, so the
/// unit of change is a name or an operator and never half of one.
const TOKEN = /[\p{L}\p{N}_]+|\s+|./gsu;

/// Where two lines differ, as spans of each; `null` when they are not alike
/// enough for the spans to mean anything.
function wordDiff(a: string, b: string): { old: Range[]; new: Range[] } | null {
  const ta = a.match(TOKEN) ?? [];
  const tb = b.match(TOKEN) ?? [];
  const ops = diff(ta, tb);
  let kept = 0;
  for (const op of ops) if (op.kind === "eq") kept += ta[op.a].length;
  if (kept < ALIKE * Math.max(a.length, b.length)) return null;
  const sa = starts(ta, 0);
  const sb = starts(tb, 0);
  const old: Range[] = [];
  const fresh: Range[] = [];
  for (const op of ops) {
    if (op.kind === "del") extend(old, [sa[op.a], sa[op.a] + ta[op.a].length]);
    else if (op.kind === "ins") extend(fresh, [sb[op.b], sb[op.b] + tb[op.b].length]);
  }
  return { old, new: fresh };
}

// Append a span, merging it into the last one when they touch: the marks are
// read as runs, and `foo` then `(` then `x` marked separately is three boxes
// where one is meant.
function extend(ranges: Range[], r: Range): void {
  const last = ranges.at(-1);
  if (last && last[1] === r[0]) last[1] = r[1];
  else ranges.push(r);
}

/// How many kept lines it takes before the middle of a run is folded away, and
/// how many stay visible on each side of a fold. A body that is mostly unchanged
/// is mostly not what the reader came for; the fold says how much was skipped and
/// opens on a click.
export const FOLD_AT = 10;
export const CONTEXT = 3;

/// A run of kept lines, cut for display: the head, a fold over the middle (if
/// the run is long enough and not opened), and the tail.
export function folded(
  pairs: [number, number][],
  open: boolean,
): { head: [number, number][]; hidden: [number, number][]; tail: [number, number][] } {
  if (open || pairs.length < FOLD_AT) return { head: pairs, hidden: [], tail: [] };
  return {
    head: pairs.slice(0, CONTEXT),
    hidden: pairs.slice(CONTEXT, pairs.length - CONTEXT),
    tail: pairs.slice(pairs.length - CONTEXT),
  };
}
