// The chaos counter: a concurrent swarm of fibers over a channel, run under a
// seeded-shuffle scheduler, with the Proof Panel ticking through N hostile
// schedules that all land on a byte-identical final state. The batches run in a
// worker (each recompiles the kernel in wasm, ~1s) so the interleaving animation
// stays smooth on the main thread while the counter climbs. Every schedule
// counted genuinely agrees to the byte: the determinism theorem made observable.
import init, { tokens } from "../pkg/prism.js";
import ChaosWorker from "./chaos-worker.ts?worker";
import { examples } from "./examples.js";
import { highlight, initFaces, kernel } from "./showcase.js";
import "./chaos.css";

// The source shown on the surface's back face: the swarm kernel exactly as the
// worker recompiles it, sliced at the same sentinel the wasm driver uses so only
// the honest kernel shows. Baked in at build time by gen-examples.
const KERNEL_SPLIT = "-- @chaos:main-below";
const KERNEL_SRC = kernel(examples.chaos_swarm, KERNEL_SPLIT);

// The swarm shape, mirroring examples/chaos_swarm.pr: one collector fiber (id 0)
// plus this many workers. The lanes and the formation bars derive from it.
const WORKERS = 6;
const LANES = WORKERS + 1;
// Schedules per wasm call. One call is a kernel recompile plus this many runs;
// the counter jumps by BATCH each reply.
const BATCH = 25;
// A soft budget cap so the tally is honestly bounded rather than pretending to
// run forever. The UI says so when it is reached.
const MAX_SCHEDULES = 3000;
// Milliseconds between interleaving pulses.
const STEP_MS = 55;

const el = <T extends HTMLElement>(id: string): T => document.getElementById(id) as T;
const lanesEl = el<HTMLDivElement>("lanes");
const formationEl = el<HTMLDivElement>("formation");
const counterEl = el<HTMLDivElement>("counter");
const checkEl = el<HTMLDivElement>("check");
const hashEl = el<HTMLSpanElement>("hash");
const noteEl = el<HTMLParagraphElement>("note");
const runBtn = el<HTMLButtonElement>("run");
const rateEl = el<HTMLSpanElement>("rate");
const codeEl = el<HTMLElement>("code");

// Show the plain source immediately and wire the Demo/Source flip, then upgrade
// the source to highlighted once the main-thread wasm tokenizer is ready (the
// worker keeps its own instance for the batches). If init fails, the plain text
// stays.
codeEl.textContent = KERNEL_SRC;
initFaces();
void init()
  .then(() => highlight(codeEl, KERNEL_SRC, tokens))
  .catch(() => {});

// --- Lanes (the animated schedule) --------------------------------------------

const laneFills: HTMLElement[] = [];
const laneRows: HTMLElement[] = [];
function buildLanes(): void {
  for (let i = 0; i < LANES; i++) {
    const lane = document.createElement("div");
    lane.className = i === 0 ? "lane collector" : "lane";
    const name = document.createElement("span");
    name.className = "lane-name";
    name.textContent = i === 0 ? "collector" : `worker ${i}`;
    const track = document.createElement("div");
    track.className = "lane-track";
    const fill = document.createElement("div");
    fill.className = "lane-fill";
    track.appendChild(fill);
    lane.append(name, track);
    lanesEl.appendChild(lane);
    laneFills.push(fill);
    laneRows.push(lane);
  }
}

// --- Formation (the invariant final state) ------------------------------------

// Draw the sorted (id, value) bars once. Identical on every schedule, so a single
// draw is the honest picture; later batches only assert it did not change.
let formationDrawn = false;
function drawFormation(state: Array<[number, number]>): void {
  if (formationDrawn || state.length === 0) return;
  const max = Math.max(...state.map(([, v]) => v), 1);
  formationEl.innerHTML = "";
  for (const [id, v] of state) {
    const bar = document.createElement("div");
    bar.className = "bar";
    const fill = document.createElement("div");
    fill.className = "bar-fill";
    fill.style.height = `${(v / max) * 100}%`;
    const label = document.createElement("div");
    label.className = "bar-label";
    label.textContent = String(id);
    bar.append(fill, label);
    formationEl.appendChild(bar);
  }
  formationDrawn = true;
}

// --- Interleaving animator -----------------------------------------------------

let scheduleQueue: number[][] = [];
let current: number[] = [];
let cursor = 0;
let lastPulse: number | null = null;

function pulse(fiber: number): void {
  if (lastPulse !== null) laneRows[lastPulse]?.classList.remove("pulse");
  if (fiber >= 0 && fiber < LANES) {
    laneRows[fiber]?.classList.add("pulse");
    lastPulse = fiber;
  }
}

function animate(): void {
  if (cursor >= current.length) {
    // Advance to the next queued schedule, or replay the last if none arrived.
    const next = scheduleQueue.shift();
    if (next !== undefined) current = next;
    cursor = 0;
    if (current.length === 0) return;
  }
  pulse(current[cursor]);
  cursor++;
}
setInterval(animate, STEP_MS);

// Keep the animator fed without unbounded growth: hold at most a few schedules.
function enqueueSchedule(trace: number[]): void {
  if (trace.length === 0) return;
  scheduleQueue.push(trace);
  if (scheduleQueue.length > 4) scheduleQueue = scheduleQueue.slice(-4);
  if (current.length === 0) {
    current = scheduleQueue.shift() ?? [];
    cursor = 0;
  }
}

// --- Batch driver --------------------------------------------------------------

const worker = new ChaosWorker();
let running = false;
let nextStart = 0;
let totalCount = 0;
let totalAgreed = 0;
let refHash: string | null = null;
let startTime = 0;
let pending = false;

function parseTrace(line: string): number[] {
  return line
    .split(" ")
    .filter((s) => s.length > 0)
    .map(Number);
}

function parseState(line: string): Array<[number, number]> {
  return line
    .split(" ")
    .filter((s) => s.length > 0)
    .map((pair) => {
      const [id, v] = pair.split(",").map(Number);
      return [id, v] as [number, number];
    });
}

function requestBatch(): void {
  if (!running || pending || totalCount >= MAX_SCHEDULES) {
    if (totalCount >= MAX_SCHEDULES) reachedBudget();
    return;
  }
  pending = true;
  worker.postMessage({ start: nextStart, count: BATCH });
}

function updateProof(): void {
  counterEl.textContent = `${totalAgreed} / ${totalCount}`;
  const ok = totalAgreed === totalCount && totalCount > 0;
  checkEl.textContent = ok
    ? "every schedule byte-identical"
    : totalCount === 0
      ? "checking..."
      : "a schedule diverged";
  checkEl.className = totalCount === 0 ? "proof-check" : ok ? "proof-check ok" : "proof-check err";
  if (refHash !== null) hashEl.textContent = refHash;
  const secs = (performance.now() - startTime) / 1000;
  if (secs > 0) rateEl.textContent = `${(totalCount / secs).toFixed(0)} schedules/s`;
}

function reachedBudget(): void {
  running = false;
  runBtn.textContent = "Run schedules";
  noteEl.textContent = `Budget reached: ${totalCount} schedules, all byte-identical. The claim is order-independence, not a particular count; press Run to keep going.`;
}

worker.onmessage = (e: MessageEvent<string>): void => {
  pending = false;
  const raw = e.data;
  if (raw.startsWith("error:")) {
    checkEl.textContent = raw;
    checkEl.className = "proof-check err";
    running = false;
    runBtn.textContent = "Run schedules";
    return;
  }
  const lines = raw.split("\n");
  const [agreed, count, hash] = lines[0].split(" ");
  totalAgreed += Number(agreed);
  totalCount += Number(count);
  // The reference hash is seed index 0 in every batch, so it must be constant;
  // a change would be a determinism violation, surfaced rather than hidden.
  if (refHash === null) refHash = hash;
  else if (refHash !== hash) {
    checkEl.textContent = "reference hash changed";
    checkEl.className = "proof-check err";
    running = false;
    return;
  }
  enqueueSchedule(parseTrace(lines[1] ?? ""));
  enqueueSchedule(parseTrace(lines[2] ?? ""));
  drawFormation(parseState(lines[3] ?? ""));
  nextStart += BATCH;
  updateProof();
  requestBatch();
};

function setRunning(on: boolean): void {
  running = on;
  runBtn.textContent = on ? "Pause" : "Run schedules";
  if (on) {
    if (startTime === 0) startTime = performance.now();
    requestBatch();
  }
}

runBtn.addEventListener("click", () => setRunning(!running));

buildLanes();
runBtn.disabled = false;
updateProof();
// Auto-start so the page is alive on load; the button becomes Pause.
setRunning(true);
