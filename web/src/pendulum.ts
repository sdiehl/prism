// The double pendulum: two rods tumbling into chaos, dragged backward and forward
// like a video. The whole trajectory is one deterministic run of the same
// interpreter the playground uses, computed once in wasm (`pendulum_run`); every
// frame is a pure function of its step index, so positioning the playhead at step
// N is literally replaying the integrator to N. The sensitive dependence on
// initial conditions makes the motion look random, but it is bit-reproducible:
// every sine and cosine is Prism's vendored libm, identical on every backend.
// No dependencies beyond the wasm bundle.
import init, { pendulum_run, tokens } from "../pkg/prism.js";
import { examples } from "./examples.js";
import { highlight, initFaces, kernel } from "./showcase.js";
import "./showcase.css";

// The source shown on the surface's back face: the pendulum program exactly as it
// runs, sliced at the same sentinel the wasm driver uses so the terminal `main`
// is dropped and only the honest kernel remains. Baked in at build time by
// gen-examples (no runtime fetch); the sentinel line itself is stripped.
const KERNEL_SPLIT = "-- @scrubber:main-below";
const KERNEL_SRC = kernel(examples.pendulum, KERNEL_SPLIT);

// How many frames of the pendulum to replay (each frame is 0.02 s of simulated
// time, so this is ~6 s of motion). The single upfront `pendulum_run` computes
// every frame 0..STEPS; scrubbing after that is pure array indexing.
const STEPS = 300;
// Playback advances at this many frames per second when Play is held.
const FPS = 30;
// How many past positions of the second bob to draw as a fading trace, the
// signature curve a double pendulum paints.
const TRAIL = 90;

type Frame = [number, number, number, number];

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
const ACCENT_STRONG = css("--accent-strong") || "#285f44";
const PANEL = css("--panel") || "#ffffff";
const LINE = css("--line") || "#e6e6e2";
const MUTED = css("--muted") || "#6b6b6b";

let frames: Frame[] = [];
// The pendulum's maximum reach (rod + rod), from the transcript header; the world
// coordinates run over a disk of this radius about the pivot.
let reach = 2;
let current = 0;
let playing = false;
// The canvas is redrawn in CSS pixels; `size` tracks the current square edge so
// world coordinates map onto it, and the backing store is scaled for hi-dpi.
let size = 0;

// Parse the `pendulum_run` transcript: a header line with the reach, then one
// line per frame, each `x1,y1,x2,y2` (the two bob centers, pivot at origin).
function parse(text: string): { reach: number; frames: Frame[] } {
  const lines = text.split("\n");
  const r = Number(lines[0]);
  const fs: Frame[] = lines
    .slice(1)
    .filter((line) => line.trim().length > 0)
    .map((line) => line.split(",").map(Number) as Frame);
  return { reach: r, frames: fs };
}

// World-to-canvas mapping: the pivot sits at the center, and the reachable disk
// fills the stage with a small margin so the swinging bobs never touch the edge.
function project(x: number, y: number): [number, number] {
  const c = size / 2;
  const scale = (c * 0.86) / reach;
  return [c + x * scale, c + y * scale];
}

// Match the backing store to the element's CSS size times the device pixel
// ratio, so the pendulum stays crisp on retina displays and after a resize.
function resize(): void {
  const rect = canvas.getBoundingClientRect();
  size = rect.width;
  const dpr = window.devicePixelRatio || 1;
  canvas.width = Math.round(size * dpr);
  canvas.height = Math.round(size * dpr);
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  if (frames.length > 0) draw();
}

function dot(x: number, y: number, r: number, color: string): void {
  ctx.beginPath();
  ctx.arc(x, y, r, 0, Math.PI * 2);
  ctx.fillStyle = color;
  ctx.fill();
}

function draw(): void {
  ctx.fillStyle = PANEL;
  ctx.fillRect(0, 0, size, size);
  const frame = frames[current];
  if (frame === undefined) return;

  // The signature trace: the path of the second bob over the recent past, fading
  // in toward the present. This is the curve that makes the chaos legible.
  const start = Math.max(1, current - TRAIL);
  ctx.lineCap = "round";
  ctx.lineJoin = "round";
  for (let k = start; k <= current; k++) {
    const a = project(frames[k - 1][2], frames[k - 1][3]);
    const b = project(frames[k][2], frames[k][3]);
    ctx.globalAlpha = 0.04 + 0.55 * ((k - start) / TRAIL);
    ctx.strokeStyle = ACCENT;
    ctx.lineWidth = 1.6;
    ctx.beginPath();
    ctx.moveTo(a[0], a[1]);
    ctx.lineTo(b[0], b[1]);
    ctx.stroke();
  }
  ctx.globalAlpha = 1;

  // The two rods, pivot -> bob1 -> bob2.
  const pivot = project(0, 0);
  const b1 = project(frame[0], frame[1]);
  const b2 = project(frame[2], frame[3]);
  ctx.strokeStyle = MUTED;
  ctx.lineWidth = 2;
  ctx.beginPath();
  ctx.moveTo(pivot[0], pivot[1]);
  ctx.lineTo(b1[0], b1[1]);
  ctx.lineTo(b2[0], b2[1]);
  ctx.stroke();

  // The bobs and the fixed pivot.
  dot(b1[0], b1[1], 6, ACCENT);
  dot(b2[0], b2[1], 6, ACCENT_STRONG);
  dot(pivot[0], pivot[1], 3, MUTED);

  // A hairline frame around the stage.
  ctx.strokeStyle = LINE;
  ctx.lineWidth = 1;
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
// Dragging the timeline scrubs the pendulum and pauses playback, like a video.
scrub.addEventListener("input", () => {
  if (playing) setPlaying(false);
  setFrame(Number(scrub.value));
});
window.addEventListener("resize", resize);

async function boot(): Promise<void> {
  try {
    await init();
    highlight(codeEl, KERNEL_SRC, tokens);
    statusEl.textContent = `Integrating ${STEPS} deterministic frames...`;
    // Yield to the event loop so the status text paints before the wasm run
    // blocks. `setTimeout` rather than `requestAnimationFrame`, so a tab loaded
    // in the background (where rAF is paused) still starts the simulation.
    await new Promise((r) => setTimeout(r, 0));
    const raw = pendulum_run(STEPS);
    if (raw.startsWith("error:")) {
      statusEl.textContent = raw;
      statusEl.classList.add("err");
      return;
    }
    const parsed = parse(raw);
    reach = parsed.reach;
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
