// Incremental computation, live. Prism's `Incr` effect memoizes each derivation
// in a demand graph by the content hash of its value (spec.html#incremental-
// computation). Reading a cell records a dependency edge; changing a source
// re-demands only the affected cone, and a derivation whose recomputed value is
// unchanged by hash does not disturb its dependents (compiler.html#content-
// addressed-core). This page runs a fixed cell graph through the wasm interpreter
// twice per change (once before, once after) and lights up exactly what the engine
// recomputed: recomputed cells, cut-off cells (re-run to the same value, cascade
// stopped), and cells served from cache.
//
// `incr_run` is a statically imported named export, so a rename or drift on the
// wasm side is a `pnpm typecheck` failure against the generated `pkg` types rather
// than a silent dead page.
import init, { incr_run, tokens } from "../pkg/prism.js";
import { highlight, initFaces } from "./showcase.js";
import "./showcase.css";
import "./incr.css";

type Kind = "input" | "memo";
type State = "changed" | "unchanged" | "recomputed" | "cutoff" | "cached";

// One cell as the graph draws it: its name, layer, and the cells it reads. The
// topology is fixed (the program is a teaching artifact), so it lives here rather
// than round-tripping through the compiler; the engine supplies only the per-cell
// value and state.
interface Cell {
  name: string;
  kind: Kind;
  deps: string[];
  layer: number;
}

const GRAPH: Cell[] = [
  { name: "a", kind: "input", deps: [], layer: 0 },
  { name: "b", kind: "input", deps: [], layer: 0 },
  { name: "c", kind: "input", deps: [], layer: 0 },
  { name: "total", kind: "memo", deps: ["a", "b", "c"], layer: 1 },
  { name: "peak", kind: "memo", deps: ["a", "b", "c"], layer: 1 },
  { name: "scaled", kind: "memo", deps: ["total"], layer: 2 },
  { name: "alert", kind: "memo", deps: ["peak"], layer: 2 },
  { name: "board", kind: "memo", deps: ["scaled", "alert"], layer: 3 },
];

const INPUTS = GRAPH.filter((c) => c.kind === "input").map((c) => c.name);
const cellOf = new Map(GRAPH.map((c) => [c.name, c]));

// One cell's value and state after a change, as the engine reports it.
interface NodeState {
  name: string;
  value: number;
  state: State;
}

type Inputs = Record<string, number>;

// The starting values: peak is b, so lowering a or c is a cutoff move and raising
// one past b is a cascade move.
const SEED: Inputs = { a: 3, b: 7, c: 5 };

// Source values stay in a small range so the graph reads at a glance and the peak
// is easy to cross either way.
const MIN = 0;
const MAX = 12;

// The clean teaching program shown on the Source face. It is the honest kernel of
// what the demo runs: the same cell graph without the two-phase instrumentation
// the browser wraps around it to observe each fire.
const SOURCE = `import Incr (..)

-- Three source cells feed a few derivations; reading the top cell
-- demands the whole graph. Each memo caches its value by content hash.
fn cells() =
  run_incr() fn
    let a = input(3)
    let b = input(7)
    let c = input(5)

    let total  = memo(\\() -> get(a) + get(b) + get(c))
    let peak   = memo(\\() -> max(get(a), max(get(b), get(c))))
    let scaled = memo(\\() -> get(total) * 2)
    let alert  = memo(\\() -> get(peak) * 10)
    let board  = memo(\\() -> get(scaled) + get(alert))

    -- reading board demands the whole cone below it
    let _ = get(board)

    -- lower a below the peak: total and its cone recompute, but peak
    -- re-runs to the same 7, so its hash is unchanged and alert stays
    -- cached. that unchanged hash is early cutoff, no dirty bit needed.
    set(a, 6)
    get(board)
`;

const el = <T extends HTMLElement>(id: string): T => document.getElementById(id) as T;
const graphEl = el<HTMLDivElement>("graph");
const codeEl = el<HTMLElement>("code");
const counterEl = el<HTMLDivElement>("counter");
const storyEl = el<HTMLParagraphElement>("story");

// Vertical gap between layers and the padding kept clear at the frame edges so a
// chip never clips the border. Pixels. A memo chip is shorter than an input chip
// (which carries its stepper), so the layout leaves generous headroom.
const ROW_GAP = 96;
const PAD_Y = 52;
const PAD_X = 64;
// How long a recomputed or cut-off cell keeps its pulse before settling, matching
// the CSS animation so a repeated change retriggers cleanly. Milliseconds.
const PULSE_MS = 820;

const val = (inp: Inputs, name: string): number => {
  switch (name) {
    case "a":
    case "b":
    case "c":
      return inp[name];
    case "total":
      return inp.a + inp.b + inp.c;
    case "peak":
      return Math.max(inp.a, inp.b, inp.c);
    case "scaled":
      return val(inp, "total") * 2;
    case "alert":
      return val(inp, "peak") * 10;
    case "board":
      return val(inp, "scaled") + val(inp, "alert");
    default:
      return 0;
  }
};

// Ask the compiler to run the graph before and after the change and classify each
// cell. `prev` is null on the cold first render (every derivation is recomputed).
function incrRun(prev: Inputs | null, next: Inputs): NodeState[] {
  const raw = incr_run(JSON.stringify({ prev, next }));
  const parsed = JSON.parse(raw) as { nodes?: NodeState[]; error?: string };
  if (parsed.error) throw new Error(parsed.error);
  return parsed.nodes ?? [];
}

interface Placed {
  cell: Cell;
  x: number;
  y: number;
}

// Place every cell: group by layer, spread each layer evenly across the measured
// width, stack layers bottom (sources) to top (the board). Returns positions in
// the graph element's own pixel coordinates plus the height the frame needs.
function layout(width: number): { placed: Placed[]; height: number } {
  const maxLayer = Math.max(...GRAPH.map((c) => c.layer));
  const rows: Cell[][] = Array.from({ length: maxLayer + 1 }, () => []);
  for (const c of GRAPH) rows[c.layer].push(c);
  const height = PAD_Y * 2 + maxLayer * ROW_GAP;
  const usable = Math.max(0, width - 2 * PAD_X);
  const placed: Placed[] = [];
  rows.forEach((row, layer) => {
    const y = height - PAD_Y - layer * ROW_GAP;
    row.forEach((cell, i) => {
      const x = PAD_X + (usable * (i + 1)) / (row.length + 1);
      placed.push({ cell, x, y });
    });
  });
  return { placed, height };
}

const SVG_NS = "http://www.w3.org/2000/svg";

// Live input values, the last classification drawn (redrawn on resize without
// reclassifying, so a resize never reads as an edit), and the pulse timers that
// clear the transient state class.
let current: Inputs = { ...SEED };
let lastStates: NodeState[] = [];
const pulseTimers = new Map<string, number>();

// Draw the whole graph from a classification: an SVG edge layer beneath, HTML
// cell chips above. Input chips carry a stepper; every chip is coloured by its
// state, and a recomputed or cut-off chip pulses once. An edge into a cell that
// recomputed is drawn hot, so the affected cone is visible as a lit subtree.
function render(states: NodeState[], pulse: boolean): void {
  lastStates = states;
  const stateOf = new Map(states.map((s) => [s.name, s]));
  const width = graphEl.clientWidth || 640;
  const { placed, height } = layout(width);
  const pos = new Map(placed.map((p) => [p.cell.name, p]));

  graphEl.style.height = `${height}px`;
  graphEl.replaceChildren();

  const svg = document.createElementNS(SVG_NS, "svg");
  svg.setAttribute("class", "graph-edges");
  svg.setAttribute("viewBox", `0 0 ${width} ${height}`);
  svg.setAttribute("preserveAspectRatio", "none");
  for (const c of GRAPH) {
    const from = pos.get(c.name);
    if (!from) continue;
    const st = stateOf.get(c.name)?.state;
    const hot = st === "recomputed";
    for (const dep of c.deps) {
      const to = pos.get(dep);
      if (!to) continue;
      const line = document.createElementNS(SVG_NS, "path");
      const midY = (from.y + to.y) / 2;
      line.setAttribute(
        "d",
        `M ${from.x} ${from.y} C ${from.x} ${midY}, ${to.x} ${midY}, ${to.x} ${to.y}`,
      );
      line.setAttribute("class", hot ? "edge edge--hot" : "edge");
      svg.appendChild(line);
    }
  }
  graphEl.appendChild(svg);

  for (const { cell, x, y } of placed) {
    const st = stateOf.get(cell.name);
    const node = document.createElement("div");
    node.className = `cell cell--${cell.kind} state-${st?.state ?? "cached"}`;
    node.style.left = `${x}px`;
    node.style.top = `${y}px`;

    const name = document.createElement("span");
    name.className = "cell-name";
    name.textContent = cell.name;
    node.appendChild(name);

    if (cell.kind === "input") {
      node.appendChild(stepper(cell.name, st?.value ?? 0));
    } else {
      const value = document.createElement("span");
      value.className = "cell-value";
      value.textContent = String(st?.value ?? 0);
      node.appendChild(value);
      if (st?.state === "cutoff") {
        const tag = document.createElement("span");
        tag.className = "cell-tag";
        tag.textContent = "cut off";
        node.appendChild(tag);
      }
    }
    graphEl.appendChild(node);

    const lit = st?.state === "recomputed" || st?.state === "cutoff";
    if (pulse && lit) {
      node.classList.add("pulse");
      const prior = pulseTimers.get(cell.name);
      if (prior) clearTimeout(prior);
      pulseTimers.set(
        cell.name,
        window.setTimeout(() => node.classList.remove("pulse"), PULSE_MS),
      );
    }
  }
}

// A source cell's minus/value/plus stepper. Each button changes the cell by one
// and re-runs the graph, so a click is one incremental step the engine observes.
function stepper(name: string, value: number): HTMLElement {
  const wrap = document.createElement("div");
  wrap.className = "stepper";
  const dec = button("-", `lower ${name}`, () => nudge(name, -1));
  const num = document.createElement("span");
  num.className = "stepper-val";
  num.textContent = String(value);
  const inc = button("+", `raise ${name}`, () => nudge(name, 1));
  dec.disabled = value <= MIN;
  inc.disabled = value >= MAX;
  wrap.append(dec, num, inc);
  return wrap;
}

function button(label: string, aria: string, on: () => void): HTMLButtonElement {
  const b = document.createElement("button");
  b.type = "button";
  b.className = "step-btn";
  b.textContent = label;
  b.setAttribute("aria-label", aria);
  b.addEventListener("click", on);
  return b;
}

// Apply a one-step change to a source and re-run. The engine sees `current`
// (before) and `next` (after); the visible pulse and counter come from the
// classification, and `current` advances only after the render.
function nudge(name: string, delta: number): void {
  const target = Math.max(MIN, Math.min(MAX, current[name] + delta));
  if (target === current[name]) return;
  const next = { ...current, [name]: target };
  step(next, name);
}

// Set a source directly (the scenario buttons), then re-run.
function setTo(name: string, target: number): void {
  const clamped = Math.max(MIN, Math.min(MAX, target));
  if (clamped === current[name]) return;
  step({ ...current, [name]: clamped }, name);
}

function step(next: Inputs, changedName: string): void {
  let states: NodeState[];
  try {
    states = incrRun(current, next);
  } catch (e) {
    storyEl.textContent = firstLine(String(e));
    return;
  }
  render(states, true);
  narrate(changedName, current, next, states);
  current = next;
}

// Summarise what the engine just did: how many derivations recomputed, and, when
// a change hit a cutoff, name the cell that re-ran to the same value and the
// dependents it spared.
function narrate(changedName: string, prev: Inputs, next: Inputs, states: NodeState[]): void {
  const memos = states.filter((s) => cellOf.get(s.name)?.kind === "memo");
  const recomputed = memos.filter((s) => s.state === "recomputed").length;
  const cutoffs = memos.filter((s) => s.state === "cutoff");
  const cached = memos.filter((s) => s.state === "cached").map((s) => s.name);
  counterEl.textContent = `${recomputed} of ${memos.length}`;

  const dir = next[changedName] > prev[changedName] ? "Raised" : "Lowered";
  const move = `${dir} ${changedName} to ${next[changedName]}.`;
  if (cutoffs.length > 0) {
    const cut = cutoffs[0].name;
    const spared = cached.length > 0 ? cached.join(", ") : "its dependents";
    storyEl.textContent = `${move} ${cut} recomputed to the same value, so the cascade cut off and ${spared} stayed cached.`;
  } else if (recomputed === 0) {
    storyEl.textContent = `${move} Nothing downstream changed, so every derivation stayed cached.`;
  } else {
    storyEl.textContent = `${move} The change reached the top, so its whole cone recomputed.`;
  }
}

function firstLine(s: string): string {
  const line = s.split("\n").find((l) => l.trim().length > 0) ?? s;
  return line.length > 160 ? `${line.slice(0, 157)}...` : line;
}

// The scenario buttons pick a move relative to the current peak so the two
// behaviours are one tap away: a cutoff move nudges a source that is not the sole
// peak (peak re-runs to the same value), a cascade move raises a source past the
// peak (the new maximum flows all the way up).
function cutoffMove(): void {
  const peak = val(current, "peak");
  const maxes = INPUTS.filter((n) => current[n] === peak);
  const name = INPUTS.find((n) => current[n] < peak) ?? (maxes.length > 1 ? maxes[0] : INPUTS[0]);
  setTo(name, current[name] > MIN ? current[name] - 1 : current[name] + 1);
}

function cascadeMove(): void {
  const peak = val(current, "peak");
  const name = INPUTS.slice().sort((x, y) => current[x] - current[y])[0];
  setTo(name, Math.min(MAX, peak + 1));
}

const MEMO_COUNT = GRAPH.filter((c) => c.kind === "memo").length;

function reset(): void {
  current = { ...SEED };
  render(incrRun(null, current), false);
  counterEl.textContent = `${MEMO_COUNT} of ${MEMO_COUNT}`;
  storyEl.textContent = "Fresh graph. Nudge a source cell, or try a cutoff or cascade move.";
}

el<HTMLButtonElement>("cut").addEventListener("click", cutoffMove);
el<HTMLButtonElement>("cascade").addEventListener("click", cascadeMove);
el<HTMLButtonElement>("reset").addEventListener("click", reset);

let resizeRaf = 0;
window.addEventListener("resize", () => {
  cancelAnimationFrame(resizeRaf);
  // A resize only re-lays-out; it must not read as an edit, so redraw the last
  // classification (not a fresh run) without a pulse.
  resizeRaf = requestAnimationFrame(() => render(lastStates, false));
});

async function boot(): Promise<void> {
  await init();
  codeEl.textContent = SOURCE;
  highlight(codeEl, SOURCE, tokens);
  initFaces();
  // Cold first render: build the graph from seed values, every derivation
  // recomputed, no pulse.
  render(incrRun(null, current), false);
  counterEl.textContent = `${MEMO_COUNT} of ${MEMO_COUNT}`;
  storyEl.textContent = "Nudge a source cell below, or try a cutoff or cascade move.";
}

void boot();
