// Branching timelines: pause a deterministic boids swarm at any step, poke one
// agent, and fork. Replay-to-N shipped with the scrubber; this adds the other
// half of the browser interaction, the run-FROM-state export (`boids_run_from`)
// and the timeline frontend. A branch is a pure function of its forked state and
// step count, so both branches persist AND each reproduces byte-for-byte: the
// determinism claim, made playable. The whole trajectory (positions AND
// velocities) is computed in wasm, so forking is just re-running the same
// interpreter from a perturbed frame, never an undo log.
import init, { boids_run_from, boids_run_full, tokens } from "../pkg/prism.js";
import { examples } from "./examples.js";
import { highlight, initFaces, kernel } from "./showcase.js";
import "./branch.css";

// The source shown on the surface's back face: the boids kernel exactly as it
// runs, sliced at the same sentinel the wasm driver uses so only the honest
// kernel shows.
const KERNEL_SPLIT = "-- @scrubber:main-below";
const KERNEL_SRC = kernel(examples.boids, KERNEL_SPLIT);

// Total steps in a timeline. The base run computes all of them; a fork at step g
// continues for STEPS - g more, so every branch spans the same 0..STEPS axis.
const STEPS = 120;
const FPS = 24;
const TRAIL = 6;
// The most branches to keep on screen (one base plus five forks), matching the
// per-branch accent palette in branch.css.
const MAX_BRANCHES = 6;

type Boid = { x: number; y: number; vx: number; vy: number };
type Frame = Boid[];

interface Branch {
  id: number;
  parent: number | null;
  forkStep: number;
  // The full trajectory over 0..STEPS. For steps before forkStep this is the
  // parent's frame (the shared prefix); from forkStep on it is the perturbed
  // continuation. Every branch carries a full-length array so rendering at the
  // shared playhead is a plain index.
  frames: Frame[];
  // First step at which this branch's frame differs from its parent's, or -1 for
  // the base. The visible answer to "when did the poke take over the flock".
  divergedAt: number;
  canvas?: HTMLCanvasElement;
}

const el = <T extends HTMLElement>(id: string): T => document.getElementById(id) as T;
const grid = el<HTMLDivElement>("grid");
const graph = document.getElementById("graph") as unknown as SVGSVGElement;
const playBtn = el<HTMLButtonElement>("play");
const scrub = el<HTMLInputElement>("scrub");
const frameEl = el<HTMLSpanElement>("frame");
const forkBtn = el<HTMLButtonElement>("fork");
const verifyBtn = el<HTMLButtonElement>("verify");
const resetBtn = el<HTMLButtonElement>("reset");
const activeSel = el<HTMLSelectElement>("active");
const proofEl = el<HTMLSpanElement>("proof");
const codeEl = el<HTMLElement>("code");

const css = (name: string): string =>
  getComputedStyle(document.documentElement).getPropertyValue(name).trim();
const BR_COLORS = [0, 1, 2, 3, 4, 5].map((i) => css(`--br-${i}`) || "#2f6f4f");
const PANEL = css("--panel") || "#ffffff";
const LINE = css("--line") || "#e6e6e2";
const MUTED = css("--muted") || "#6b6b6b";

let world = 100000;
let branches: Branch[] = [];
let current = 0;
let playing = false;

// --- Source panel (same wasm highlighter as the scrubber/playground) ----------

// Show the plain source immediately and wire the Demo/Source flip; boot()
// upgrades the source to highlighted once the wasm tokenizer is available.
codeEl.textContent = KERNEL_SRC;
initFaces();

// --- Parsing the wasm trajectory ----------------------------------------------

// One full-state frame line: space-separated "x,y,vx,vy" boids.
function parseFrame(line: string): Frame {
  return line
    .split(" ")
    .filter((p) => p.length > 0)
    .map((quad) => {
      const [x, y, vx, vy] = quad.split(",").map(Number);
      return { x, y, vx, vy };
    });
}

// A wasm trajectory: header "W W" then one full-state frame per line.
function parseTrajectory(text: string): { world: number; frames: Frame[] } {
  const lines = text.split("\n");
  const [w] = lines[0].split(" ").map(Number);
  const frames = lines
    .slice(1)
    .filter((line) => line.trim().length > 0)
    .map(parseFrame);
  return { world: w, frames };
}

// Serialize a frame back to the "x,y,vx,vy ..." line `boids_run_from` parses, so
// a forked (perturbed) frame round-trips into the kernel as its start state.
function serializeFrame(f: Frame): string {
  return f.map((b) => `${b.x},${b.y},${b.vx},${b.vy}`).join(" ");
}

// The perturbation: poke ONE agent. Reverse boid 0's velocity, leaving every
// other boid and the seed untouched. A single reversed heading is a legal input
// change, and chaos does the rest: within a dozen steps the whole flock diverges.
function perturb(f: Frame): Frame {
  return f.map((b, i) => (i === 0 ? { ...b, vx: -b.vx, vy: -b.vy } : { ...b }));
}

// The first step where two trajectories differ (in any boid's full state), or -1
// if they never do. What "diverged at" reports.
function firstDivergence(a: Frame[], b: Frame[]): number {
  const n = Math.min(a.length, b.length);
  for (let i = 0; i < n; i++) {
    if (serializeFrame(a[i]) !== serializeFrame(b[i])) return i;
  }
  return -1;
}

// --- Building branches ---------------------------------------------------------

// Fork `parent` at global step `g`: perturb its frame there, continue the run
// from the perturbed state, and splice the continuation onto the shared prefix.
// Returns null if the continuation errored (surfaced by the caller).
function makeFork(parent: Branch, g: number, id: number): Branch | null {
  const perturbed = perturb(parent.frames[g]);
  const raw = boids_run_from(serializeFrame(perturbed), STEPS - g);
  if (raw.startsWith("error:")) {
    proofEl.textContent = raw;
    proofEl.className = "branch-proof err";
    return null;
  }
  const cont = parseTrajectory(raw).frames;
  // Shared prefix from the parent, then the perturbed continuation. cont[0] is
  // the perturbed frame itself (step g); cont[k] is step g + k.
  const frames = parent.frames.slice(0, g).concat(cont);
  const divergedAt = firstDivergence(parent.frames, frames);
  return { id, parent: parent.id, forkStep: g, frames, divergedAt };
}

// --- Rendering the swarm -------------------------------------------------------

function drawBoid(ctx: CanvasRenderingContext2D, size: number, color: string, b: Boid): void {
  const cx = (b.x / world) * size;
  const cy = (b.y / world) * size;
  let hx = b.vx;
  let hy = b.vy;
  const mag = Math.hypot(hx, hy);
  if (mag < 1e-6) {
    hx = 0;
    hy = -1;
  } else {
    hx /= mag;
    hy /= mag;
  }
  const s = 6;
  const px = -hy;
  const py = hx;
  ctx.beginPath();
  ctx.moveTo(cx + hx * s, cy + hy * s);
  ctx.lineTo(cx - hx * s * 0.5 + px * s * 0.5, cy - hy * s * 0.5 + py * s * 0.5);
  ctx.lineTo(cx - hx * s * 0.5 - px * s * 0.5, cy - hy * s * 0.5 - py * s * 0.5);
  ctx.closePath();
  ctx.fillStyle = color;
  ctx.fill();
}

function drawBranch(br: Branch): void {
  const canvas = br.canvas;
  if (canvas === undefined) return;
  const ctx = canvas.getContext("2d");
  if (ctx === null) return;
  const rect = canvas.getBoundingClientRect();
  const size = rect.width;
  const dpr = window.devicePixelRatio || 1;
  if (canvas.width !== Math.round(size * dpr)) {
    canvas.width = Math.round(size * dpr);
    canvas.height = Math.round(size * dpr);
  }
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  ctx.fillStyle = PANEL;
  ctx.fillRect(0, 0, size, size);

  const color = BR_COLORS[br.id % BR_COLORS.length];
  const g = Math.min(current, br.frames.length - 1);
  const frame = br.frames[g];
  if (frame === undefined) return;

  // Motion trail behind each boid.
  for (let k = Math.max(0, g - TRAIL); k < g; k++) {
    const past = br.frames[k];
    ctx.globalAlpha = 0.05 + 0.13 * ((k - (g - TRAIL)) / TRAIL);
    ctx.fillStyle = color;
    for (const b of past) {
      ctx.beginPath();
      ctx.arc((b.x / world) * size, (b.y / world) * size, 1.5, 0, Math.PI * 2);
      ctx.fill();
    }
  }
  ctx.globalAlpha = 1;
  for (const b of frame) drawBoid(ctx, size, color, b);

  ctx.strokeStyle = LINE;
  ctx.strokeRect(0.5, 0.5, size - 1, size - 1);
}

function drawAll(): void {
  for (const br of branches) drawBranch(br);
}

// --- The branch stage grid -----------------------------------------------------

// Rebuild the grid of per-branch canvases (once per fork/reset). Each stage
// carries the branch colour, a label, and a live "diverged at" readout.
function buildGrid(): void {
  grid.innerHTML = "";
  for (const br of branches) {
    const color = BR_COLORS[br.id % BR_COLORS.length];
    const mini = document.createElement("div");
    mini.className = "mini";
    mini.style.setProperty("--br", color);

    const stage = document.createElement("div");
    stage.className = "mini-stage";
    const canvas = document.createElement("canvas");
    canvas.className = "mini-view";
    stage.appendChild(canvas);
    br.canvas = canvas;

    const label = document.createElement("div");
    label.className = "mini-label";
    const dot = document.createElement("span");
    dot.className = "mini-dot";
    const name = document.createElement("span");
    name.innerHTML =
      br.parent === null
        ? "<b>main</b>"
        : `<b>branch ${br.id}</b> <span style="color:var(--muted)">forked @ ${br.forkStep} from ${br.parent === 0 ? "main" : `br ${br.parent}`}</span>`;
    const diverged = document.createElement("span");
    diverged.className = "mini-diverged";
    diverged.textContent = br.divergedAt >= 0 ? `diverges @ ${br.divergedAt}` : "";
    label.append(dot, name, diverged);

    mini.append(stage, label);
    grid.appendChild(mini);
  }
}

// Refresh the active-branch dropdown to list every current branch.
function buildSelect(): void {
  const prev = activeSel.value;
  activeSel.innerHTML = "";
  for (const br of branches) {
    const opt = document.createElement("option");
    opt.value = String(br.id);
    opt.textContent = br.parent === null ? "main" : `branch ${br.id}`;
    activeSel.appendChild(opt);
  }
  if (branches.some((b) => String(b.id) === prev)) activeSel.value = prev;
}

// --- The git-graph -------------------------------------------------------------

const SVG_NS = "http://www.w3.org/2000/svg";
const G_TOP = 16;
const G_BOT = 16;
const G_LEFT = 26;
const G_LANE = 46;
const G_H = 340;

function svg(tag: string, attrs: Record<string, string | number>): SVGElement {
  const e = document.createElementNS(SVG_NS, tag);
  for (const [k, v] of Object.entries(attrs)) e.setAttribute(k, String(v));
  return e;
}

const laneX = (lane: number): number => G_LEFT + lane * G_LANE;
const stepY = (step: number): number => G_TOP + (step / STEPS) * (G_H - G_TOP - G_BOT);

// Draw the fork DAG: one vertical lane per branch (fork point to end), a curved
// connector from parent lane to child lane at the fork, a dot at each fork, and
// a horizontal playhead at the current step with a marker on every live lane.
function drawGraph(): void {
  const maxLane = branches.length - 1;
  const width = laneX(maxLane) + G_LEFT;
  graph.setAttribute("viewBox", `0 0 ${width} ${G_H}`);
  graph.innerHTML = "";

  // Step guide labels (0 at top, STEPS at bottom).
  for (const s of [0, STEPS]) {
    const t = svg("text", {
      x: 4,
      y: stepY(s) + (s === 0 ? 8 : 0),
      fill: MUTED,
      "font-size": 9,
      "font-family": "var(--mono)",
    });
    t.textContent = String(s);
    graph.appendChild(t);
  }

  for (const br of branches) {
    const color = BR_COLORS[br.id % BR_COLORS.length];
    const x = laneX(br.id);
    // Fork connector from the parent lane.
    if (br.parent !== null) {
      const px = laneX(br.parent);
      const y = stepY(br.forkStep);
      const path = svg("path", {
        d: `M ${px} ${y} C ${px} ${y + 14}, ${x} ${y - 14}, ${x} ${y}`,
        fill: "none",
        stroke: color,
        "stroke-width": 2,
        opacity: 0.75,
      });
      graph.appendChild(path);
    }
    // The lane line, from the fork (or top for main) to the end.
    graph.appendChild(
      svg("line", {
        x1: x,
        y1: stepY(br.forkStep),
        x2: x,
        y2: stepY(STEPS),
        stroke: color,
        "stroke-width": 3,
        "stroke-linecap": "round",
      }),
    );
    // Fork node.
    if (br.parent !== null) {
      graph.appendChild(svg("circle", { cx: x, cy: stepY(br.forkStep), r: 4, fill: color }));
    }
  }

  // Playhead: a horizontal rule at the current step, dots on live lanes.
  const y = stepY(current);
  graph.appendChild(
    svg("line", {
      x1: 2,
      y1: y,
      x2: width - 2,
      y2: y,
      stroke: MUTED,
      "stroke-width": 1,
      "stroke-dasharray": "3 3",
      opacity: 0.7,
    }),
  );
  for (const br of branches) {
    if (br.forkStep > current) continue;
    graph.appendChild(
      svg("circle", {
        cx: laneX(br.id),
        cy: y,
        r: 5,
        fill: PANEL,
        stroke: BR_COLORS[br.id % BR_COLORS.length],
        "stroke-width": 2.5,
      }),
    );
  }
}

// --- Transport & actions -------------------------------------------------------

function setFrame(n: number): void {
  current = Math.max(0, Math.min(STEPS, n));
  scrub.value = String(current);
  frameEl.textContent = `step ${current} / ${STEPS}`;
  drawAll();
  drawGraph();
}

let last = 0;
let acc = 0;
function tick(now: number): void {
  if (!playing) return;
  const dt = now - last;
  last = now;
  acc += dt;
  const interval = 1000 / FPS;
  while (acc >= interval) {
    acc -= interval;
    setFrame(current >= STEPS ? 0 : current + 1);
  }
  requestAnimationFrame(tick);
}

function setPlaying(on: boolean): void {
  playing = on;
  playBtn.textContent = on ? "Pause" : "Play";
  playBtn.setAttribute("aria-label", on ? "Pause" : "Play");
  if (on) {
    if (current >= STEPS) setFrame(0);
    last = performance.now();
    acc = 0;
    requestAnimationFrame(tick);
  }
}

function refreshForkEnabled(): void {
  forkBtn.disabled = branches.length >= MAX_BRANCHES || current >= STEPS;
}

// Continuing a run recompiles the kernel in wasm (~1s), so a fork/verify blocks
// the main thread briefly. Paint a "working" state first, then run the heavy
// synchronous body after a frame, so the button never looks hung. Buttons are
// disabled across the call to prevent a re-entrant second run.
function withWork(label: string, body: () => void): void {
  proofEl.textContent = label;
  proofEl.className = "branch-proof";
  forkBtn.disabled = true;
  verifyBtn.disabled = true;
  // `setTimeout`, not `requestAnimationFrame`: rAF is paused in a background tab,
  // which would leave the run wedged at "working" until the tab is focused. A
  // short timeout lets the label paint in the foreground and still fires when
  // backgrounded.
  setTimeout(() => {
    body();
    verifyBtn.disabled = false;
    refreshForkEnabled();
  }, 20);
}

function doFork(): void {
  if (branches.length >= MAX_BRANCHES || current >= STEPS) return;
  const parent = branches.find((b) => String(b.id) === activeSel.value) ?? branches[0];
  if (parent.forkStep > current) {
    proofEl.textContent = `pick a step at or after branch ${parent.id}'s fork (${parent.forkStep})`;
    proofEl.className = "branch-proof err";
    return;
  }
  withWork(`forking at step ${current}...`, () => {
    const id = branches.length;
    const fork = makeFork(parent, current, id);
    if (fork === null) return;
    branches.push(fork);
    buildGrid();
    buildSelect();
    activeSel.value = String(id);
    proofEl.textContent = `forked branch ${id} at step ${current}`;
    proofEl.className = "branch-proof ok";
    setFrame(current);
  });
}

// Re-run every forked branch from scratch (its perturbed start state) and check
// it reproduces the stored trajectory byte-for-byte. This is the determinism
// claim, checked live: a branch is a pure function of its forked state.
function doVerify(): void {
  withWork("replaying every branch...", verifyBody);
}

function verifyBody(): void {
  let checked = 0;
  for (const br of branches) {
    if (br.parent === null) continue;
    const parent = branches.find((b) => b.id === br.parent);
    if (parent === undefined) continue;
    const rerun = makeFork(parent, br.forkStep, br.id);
    if (rerun === null) return;
    for (let i = 0; i <= STEPS; i++) {
      if (serializeFrame(rerun.frames[i]) !== serializeFrame(br.frames[i])) {
        proofEl.textContent = `branch ${br.id} diverged on replay at step ${i}`;
        proofEl.className = "branch-proof err";
        return;
      }
    }
    checked++;
  }
  proofEl.textContent =
    checked === 0
      ? "fork a branch, then verify"
      : `${checked} branch${checked === 1 ? "" : "es"} replayed byte-for-byte`;
  proofEl.className = "branch-proof ok";
}

function doReset(): void {
  branches = branches.slice(0, 1);
  buildGrid();
  buildSelect();
  proofEl.textContent = "";
  proofEl.className = "branch-proof";
  refreshForkEnabled();
  requestAnimationFrame(() => setFrame(current));
}

playBtn.addEventListener("click", () => setPlaying(!playing));
scrub.addEventListener("input", () => {
  if (playing) setPlaying(false);
  setFrame(Number(scrub.value));
  refreshForkEnabled();
});
forkBtn.addEventListener("click", doFork);
verifyBtn.addEventListener("click", doVerify);
resetBtn.addEventListener("click", doReset);
window.addEventListener("resize", drawAll);

async function boot(): Promise<void> {
  try {
    await init();
    highlight(codeEl, KERNEL_SRC, tokens);
    await new Promise((r) => setTimeout(r, 0));
    const raw = boids_run_full(STEPS);
    if (raw.startsWith("error:")) {
      grid.textContent = raw;
      return;
    }
    const parsed = parseTrajectory(raw);
    world = parsed.world;
    branches = [{ id: 0, parent: null, forkStep: 0, frames: parsed.frames, divergedAt: -1 }];
    scrub.max = String(STEPS);
    scrub.disabled = false;
    playBtn.disabled = false;
    verifyBtn.disabled = false;
    resetBtn.disabled = false;
    activeSel.disabled = false;
    buildGrid();
    buildSelect();
    refreshForkEnabled();
    setFrame(0);
  } catch (err) {
    grid.textContent = `error: ${err}`;
  }
}

void boot();
