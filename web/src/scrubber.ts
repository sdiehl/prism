// The determinism scrubber: a boids swarm you drag backward and forward like a
// video. The whole trajectory is one deterministic run of the same interpreter
// the playground uses, computed once in wasm (`boids_run`); every frame is a
// pure function of its step index, so positioning the playhead at step N is
// literally replaying the swarm to N. Backward is not an undo buffer, it is the
// identical computation re-indexed. No dependencies beyond the wasm bundle.
import init, { boids_run, tokens } from "../pkg/prism.js";
import { examples } from "./examples.js";
import { highlight, initFaces, kernel } from "./showcase.js";
import "./showcase.css";

// The source shown on the surface's back face: the boids program exactly as it
// runs, sliced at the same sentinel the wasm driver uses so the terminal `main`
// is dropped and only the honest kernel remains. Baked in at build time by
// gen-examples (no runtime fetch); the sentinel line itself is stripped.
const KERNEL_SPLIT = "-- @scrubber:main-below";
const KERNEL_SRC = kernel(examples.boids, KERNEL_SPLIT);

// How many steps of the swarm to replay. The single upfront `boids_run` computes
// every frame 0..STEPS; scrubbing after that is pure array indexing.
const STEPS = 120;
// Playback advances at this many frames per second when Play is held.
const FPS = 24;
// How many past positions to fade in behind each boid, as a motion trail.
const TRAIL = 7;

type Vec = [number, number];
type Frame = Vec[];

const el = <T extends HTMLElement>(id: string): T => document.getElementById(id) as T;
const canvas = el<HTMLCanvasElement>("view");
const statusEl = el<HTMLDivElement>("status");
const playBtn = el<HTMLButtonElement>("play");
const scrub = el<HTMLInputElement>("scrub");
const frameEl = el<HTMLSpanElement>("frame");
const codeEl = el<HTMLElement>("code");
const ctx = canvas.getContext("2d") as CanvasRenderingContext2D;

// Show the plain source immediately and wire the Demo/Source flip; boot()
// upgrades the source to highlighted once the wasm tokenizer is available.
codeEl.textContent = KERNEL_SRC;
initFaces();

const css = (name: string): string =>
  getComputedStyle(document.documentElement).getPropertyValue(name).trim();
const ACCENT = css("--accent") || "#2f6f4f";
const PANEL = css("--panel") || "#ffffff";
const LINE = css("--line") || "#e6e6e2";

let frames: Frame[] = [];
let world = 1;
let current = 0;
let playing = false;
// The canvas is redrawn in CSS pixels; `size` tracks the current square edge so
// world coordinates map onto it, and the backing store is scaled for hi-dpi.
let size = 0;

// Parse the `boids_run` transcript: a header line "W H" then one line per frame,
// each a space-separated list of "x,y" integer positions.
function parse(text: string): { world: number; frames: Frame[] } {
  const lines = text.split("\n");
  const [w] = lines[0].split(" ").map(Number);
  const fs: Frame[] = lines
    .slice(1)
    .filter((line) => line.trim().length > 0)
    .map((line) =>
      line
        .split(" ")
        .filter((p) => p.length > 0)
        .map((pair) => {
          const [x, y] = pair.split(",").map(Number);
          return [x, y] as Vec;
        }),
    );
  return { world: w, frames: fs };
}

// The shortest signed offset between two coordinates on a wrapped axis, so a
// boid crossing an edge does not appear to streak across the whole world.
function wrapDelta(a: number, b: number): number {
  let d = a - b;
  if (d > world / 2) d -= world;
  if (d < -world / 2) d += world;
  return d;
}

// Match the backing store to the element's CSS size times the device pixel
// ratio, so the swarm stays crisp on retina displays and after a resize.
function resize(): void {
  const rect = canvas.getBoundingClientRect();
  size = rect.width;
  const dpr = window.devicePixelRatio || 1;
  canvas.width = Math.round(size * dpr);
  canvas.height = Math.round(size * dpr);
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  if (frames.length > 0) draw();
}

// Draw one boid as a small triangle at `p`, pointing along `heading`. A zero
// heading (a boid that did not move) falls back to pointing up.
function boid(p: Vec, heading: Vec): void {
  const cx = (p[0] / world) * size;
  const cy = (p[1] / world) * size;
  let hx = heading[0];
  let hy = heading[1];
  const mag = Math.hypot(hx, hy);
  if (mag < 1e-6) {
    hx = 0;
    hy = -1;
  } else {
    hx /= mag;
    hy /= mag;
  }
  const s = 7;
  const px = -hy;
  const py = hx;
  const tipx = cx + hx * s;
  const tipy = cy + hy * s;
  const bx = cx - hx * s * 0.5;
  const by = cy - hy * s * 0.5;
  ctx.beginPath();
  ctx.moveTo(tipx, tipy);
  ctx.lineTo(bx + px * s * 0.5, by + py * s * 0.5);
  ctx.lineTo(bx - px * s * 0.5, by - py * s * 0.5);
  ctx.closePath();
  ctx.fill();
}

function draw(): void {
  ctx.fillStyle = PANEL;
  ctx.fillRect(0, 0, size, size);
  const frame = frames[current];
  if (frame === undefined) return;

  // Motion trail: each boid's recent positions, fading in toward the present.
  for (let k = Math.max(0, current - TRAIL); k < current; k++) {
    const past = frames[k];
    const alpha = 0.05 + 0.14 * ((k - (current - TRAIL)) / TRAIL);
    ctx.globalAlpha = alpha;
    ctx.fillStyle = ACCENT;
    for (const p of past) {
      ctx.beginPath();
      ctx.arc((p[0] / world) * size, (p[1] / world) * size, 1.6, 0, Math.PI * 2);
      ctx.fill();
    }
  }

  // The swarm itself, oriented by where each boid moved since the last frame.
  ctx.globalAlpha = 1;
  ctx.fillStyle = ACCENT;
  const prev = frames[Math.max(0, current - 1)];
  frame.forEach((p, i) => {
    const q = prev[i] ?? p;
    boid(p, [wrapDelta(p[0], q[0]), wrapDelta(p[1], q[1])]);
  });

  // A hairline frame around the toroidal world.
  ctx.globalAlpha = 1;
  ctx.strokeStyle = LINE;
  ctx.strokeRect(0.5, 0.5, size - 1, size - 1);
}

function setFrame(n: number): void {
  current = Math.max(0, Math.min(frames.length - 1, n));
  scrub.value = String(current);
  frameEl.textContent = `step ${current} / ${frames.length - 1}`;
  draw();
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
    setFrame(current >= frames.length - 1 ? 0 : current + 1);
  }
  requestAnimationFrame(tick);
}

function setPlaying(on: boolean): void {
  playing = on;
  playBtn.textContent = on ? "Pause" : "Play";
  playBtn.setAttribute("aria-label", on ? "Pause" : "Play");
  if (on) {
    if (current >= frames.length - 1) setFrame(0);
    last = performance.now();
    acc = 0;
    requestAnimationFrame(tick);
  }
}

playBtn.addEventListener("click", () => setPlaying(!playing));
// Dragging the timeline scrubs the swarm and pauses playback, like a video.
scrub.addEventListener("input", () => {
  if (playing) setPlaying(false);
  setFrame(Number(scrub.value));
});
window.addEventListener("resize", resize);

async function boot(): Promise<void> {
  try {
    await init();
    highlight(codeEl, KERNEL_SRC, tokens);
    statusEl.textContent = `Simulating ${STEPS} deterministic steps...`;
    // Yield to the event loop so the status text paints before the wasm run
    // blocks. `setTimeout` rather than `requestAnimationFrame`, so a tab loaded
    // in the background (where rAF is paused) still starts the simulation.
    await new Promise((r) => setTimeout(r, 0));
    const raw = boids_run(STEPS);
    if (raw.startsWith("error:")) {
      statusEl.textContent = raw;
      statusEl.classList.add("err");
      return;
    }
    const parsed = parse(raw);
    world = parsed.world;
    frames = parsed.frames;
    scrub.max = String(frames.length - 1);
    scrub.disabled = false;
    playBtn.disabled = false;
    statusEl.classList.add("hidden");
    resize();
    setFrame(0);
  } catch (err) {
    statusEl.textContent = `error: ${err}`;
    statusEl.classList.add("err");
  }
}

void boot();
