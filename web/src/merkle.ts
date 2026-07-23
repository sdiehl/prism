// Content-addressed code, live. Every Prism top-level definition is stored under
// the hash of its elaborated core with each dependency replaced by that
// dependency's own hash, so the program is a Merkle DAG (compiler.html#content-
// addressed-core). This page asks the wasm compiler for that `name -> hash` map
// on every keystroke and draws it: edit one definition and its hash moves, and
// so does every hash that transitively depends on it, while independent code
// keeps its exact address. The real hashes come from the compiler (`hash_defs`);
// the graph structure and the cascade highlight are pure functions of that map.
//
// `hash_defs` is a statically imported named export, so a rename or drift on the
// wasm side is a `pnpm typecheck` failure against the generated `pkg` types rather
// than a silent dead page.
import init, { hash_defs, tokens } from "../pkg/prism.js";
import { highlight, initFaces } from "./showcase.js";
import "./showcase.css";
import "./merkle.css";

// One definition as the compiler addresses it: its name, its short content hash,
// and the names of the other user definitions it references. Emitted by
// `hash_defs` as a JSON array; on a front-end error the export returns `{error}`.
interface Def {
  name: string;
  hash: string;
  deps: string[];
}

// The starting program: two leaf helpers, a mid function over them, a top
// function over that, and one independent definition. The interesting structure
// is the cascade (editing `inc` moves `step` and `run` but not `solo`) and the
// dedup (make two bodies identical and their hashes collapse).
const SEED = `-- Every definition is content-addressed: its hash folds in the
-- hashes of everything it calls, so this is a Merkle DAG. Edit a
-- body below and watch which node hashes move.

fn inc(x) : Int = x + 1

fn dbl(x) : Int = x + x

fn step(x) : Int = dbl(inc(x))

fn run(x) : Int = step(x) + step(inc(x))

fn solo(x) : Int = x * 100
`;

const el = <T extends HTMLElement>(id: string): T => document.getElementById(id) as T;
const srcEl = el<HTMLTextAreaElement>("src");
const codeEl = el<HTMLElement>("code");
const dagEl = el<HTMLDivElement>("dag");
const errEl = el<HTMLDivElement>("err");

srcEl.value = SEED;
codeEl.textContent = SEED;
initFaces();

// How many hex characters of the content hash to show on a node chip. The full
// hash is far longer; a short prefix is enough to read at a glance and to see
// change, exactly how `prism dump core-hash` renders it for a human.
const CHIP_HEX = 7;
// Vertical gap between DAG layers, and the padding kept clear at the frame edges
// so node chips never clip it (a leaf placed at the far right of a narrow phone
// frame would otherwise touch the border). Pixels.
const ROW_GAP = 96;
const PAD_Y = 46;
const PAD_X = 58;
// How long a changed node keeps its highlight before settling, in milliseconds.
// Matches the CSS pulse so re-editing the same node retriggers cleanly.
const PULSE_MS = 900;
// Debounce between a keystroke and a re-hash, in milliseconds: long enough to
// coalesce a burst of typing, short enough to feel live.
const DEBOUNCE_MS = 160;

// The last good hash per name, so a re-hash can mark exactly the nodes whose
// address changed. Seeded empty: the first render pulses nothing.
let prevHash = new Map<string, string>();
// Timers clearing the transient `.changed` class, keyed by node name.
const pulseTimers = new Map<string, number>();

// Ask the compiler for the current program's `name/hash/deps`. Returns the parsed
// defs, or an error string (the export answers `{error}` on a front-end failure).
function hashDefs(src: string): Def[] | { error: string } {
  let raw: string;
  try {
    raw = hash_defs(src);
  } catch (e) {
    return { error: String(e) };
  }
  let parsed: unknown;
  try {
    parsed = JSON.parse(raw);
  } catch {
    return { error: raw };
  }
  if (parsed && typeof parsed === "object" && "error" in parsed) {
    return { error: String((parsed as { error: unknown }).error) };
  }
  if (!Array.isArray(parsed)) return { error: "unexpected hash output" };
  return parsed as Def[];
}

interface Placed {
  def: Def;
  x: number;
  y: number;
}

// Longest dependency chain below each node, so a node always sits above every
// definition it calls. Leaves land on layer 0 (the bottom row); the top sits
// highest, which is the direction hashes cascade.
function layerOf(defs: Def[]): Map<string, number> {
  const byName = new Map(defs.map((d) => [d.name, d]));
  const memo = new Map<string, number>();
  const depth = (name: string, stack: Set<string>): number => {
    const cached = memo.get(name);
    if (cached !== undefined) return cached;
    const d = byName.get(name);
    if (!d || stack.has(name)) return 0;
    let best = 0;
    for (const dep of d.deps) {
      if (byName.has(dep)) best = Math.max(best, 1 + depth(dep, new Set(stack).add(name)));
    }
    memo.set(name, best);
    return best;
  };
  return new Map(defs.map((d) => [d.name, depth(d.name, new Set())]));
}

// Place every node: group by layer, spread each layer evenly across the width,
// stack layers bottom (leaves) to top (roots). Returns positions in the DAG
// element's own pixel coordinates plus the height the frame needs.
function layout(defs: Def[], width: number): { placed: Placed[]; height: number } {
  const layers = layerOf(defs);
  const maxLayer = Math.max(0, ...defs.map((d) => layers.get(d.name) ?? 0));
  const rows: Def[][] = Array.from({ length: maxLayer + 1 }, () => []);
  for (const d of defs) rows[layers.get(d.name) ?? 0].push(d);
  for (const row of rows) row.sort((a, b) => a.name.localeCompare(b.name));
  const height = PAD_Y * 2 + maxLayer * ROW_GAP;
  const usable = Math.max(0, width - 2 * PAD_X);
  const placed: Placed[] = [];
  rows.forEach((row, layer) => {
    const y = height - PAD_Y - layer * ROW_GAP;
    row.forEach((def, i) => {
      const x = PAD_X + (usable * (i + 1)) / (row.length + 1);
      placed.push({ def, x, y });
    });
  });
  return { placed, height };
}

const SVG_NS = "http://www.w3.org/2000/svg";

// Draw the whole DAG: an SVG edge layer beneath, HTML node chips above. Nodes
// whose hash changed since the last render are marked `.changed` for a soft
// pulse, and definitions that now share one hash are marked `.twin` to surface
// content dedup. Independent nodes keep their position and their address.
function render(defs: Def[]): void {
  const width = dagEl.clientWidth || 640;
  const { placed, height } = layout(defs, width);
  const pos = new Map(placed.map((p) => [p.def.name, p]));

  // Which hashes are shared by more than one name: content addressing dedup.
  const shareCount = new Map<string, number>();
  for (const d of defs) shareCount.set(d.hash, (shareCount.get(d.hash) ?? 0) + 1);

  dagEl.style.height = `${height}px`;
  dagEl.replaceChildren();

  const svg = document.createElementNS(SVG_NS, "svg");
  svg.setAttribute("class", "dag-edges");
  svg.setAttribute("viewBox", `0 0 ${width} ${height}`);
  svg.setAttribute("preserveAspectRatio", "none");
  const changedNames = new Set<string>();
  for (const d of defs) if (prevHash.get(d.name) !== d.hash) changedNames.add(d.name);

  for (const d of defs) {
    const from = pos.get(d.name);
    if (!from) continue;
    for (const dep of d.deps) {
      const to = pos.get(dep);
      if (!to) continue;
      const line = document.createElementNS(SVG_NS, "path");
      const midY = (from.y + to.y) / 2;
      line.setAttribute(
        "d",
        `M ${from.x} ${from.y} C ${from.x} ${midY}, ${to.x} ${midY}, ${to.x} ${to.y}`,
      );
      line.setAttribute("class", changedNames.has(d.name) ? "edge edge--hot" : "edge");
      svg.appendChild(line);
    }
  }
  dagEl.appendChild(svg);

  for (const { def, x, y } of placed) {
    const node = document.createElement("div");
    const twin = (shareCount.get(def.hash) ?? 0) > 1;
    node.className = `node${twin ? " twin" : ""}`;
    node.style.left = `${x}px`;
    node.style.top = `${y}px`;

    const name = document.createElement("span");
    name.className = "node-name";
    name.textContent = def.name;

    const chip = document.createElement("span");
    chip.className = "node-hash";
    chip.textContent = def.hash.slice(0, CHIP_HEX);
    chip.title = def.hash;

    node.append(name, chip);
    if (twin) {
      const tag = document.createElement("span");
      tag.className = "node-twin";
      tag.textContent = "same hash";
      node.appendChild(tag);
    }
    dagEl.appendChild(node);

    if (changedNames.has(def.name) && prevHash.size > 0) {
      node.classList.add("changed");
      const prior = pulseTimers.get(def.name);
      if (prior) clearTimeout(prior);
      pulseTimers.set(
        def.name,
        window.setTimeout(() => node.classList.remove("changed"), PULSE_MS),
      );
    }
  }

  prevHash = new Map(defs.map((d) => [d.name, d.hash]));
}

// Recompute from the editor: repaint the highlighted source face, then either
// render the fresh DAG or surface the front-end error while leaving the last good
// graph on screen.
function update(): void {
  const src = srcEl.value;
  highlight(codeEl, src, tokens);
  const result = hashDefs(src);
  if ("error" in result) {
    errEl.textContent = firstLine(result.error);
    errEl.classList.add("show");
    dagEl.classList.add("stale");
    return;
  }
  errEl.classList.remove("show");
  dagEl.classList.remove("stale");
  if (result.length === 0) {
    errEl.textContent = "no definitions yet";
    errEl.classList.add("show");
    return;
  }
  render(result);
}

// A diagnostic can be several lines; the first line is the headline a reader
// needs, and it keeps the editor panel from jumping.
function firstLine(s: string): string {
  const line = s.split("\n").find((l) => l.trim().length > 0) ?? s;
  return line.length > 160 ? `${line.slice(0, 157)}...` : line;
}

let debounce = 0;
srcEl.addEventListener("input", () => {
  clearTimeout(debounce);
  debounce = window.setTimeout(update, DEBOUNCE_MS);
});

let resizeRaf = 0;
window.addEventListener("resize", () => {
  cancelAnimationFrame(resizeRaf);
  // A resize only re-lays-out; it must not read as an edit, so suppress the
  // pulse by keeping prevHash in step with what is already drawn.
  resizeRaf = requestAnimationFrame(() => {
    const result = hashDefs(srcEl.value);
    if (!("error" in result) && result.length > 0) render(result);
  });
});

async function boot(): Promise<void> {
  await init();
  update();
}

void boot();
