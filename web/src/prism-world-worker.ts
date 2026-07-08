// The compute worker for PRISM WORLD. Every trajectory is the Prism world law
// (examples/world.pr) run through the wasm interpreter: one `world_run` call
// evolves a seed under a law for N ticks and returns one `<state-hash> <bits>`
// line per tick. Doing it off the main thread keeps the universe interactive
// while a law re-evolves. Law hashes and the law source come from the same
// bundle, so the identity a tab shows is the compiler's own content hash.
import init, { world_law_hash, world_run, world_source } from "../pkg/prism.js";

// A request carries an id the main thread matches replies against. `run` evolves
// a grid (a seed, or a forked frame's bits) under a law; `meta` fetches the law
// hashes and source once at boot.
interface RunReq {
  kind: "run";
  id: number;
  law: string;
  w: number;
  h: number;
  seed: string;
  ticks: number;
}
interface MetaReq {
  kind: "meta";
  id: number;
  laws: string[];
}
type Req = RunReq | MetaReq;

interface Scope {
  onmessage: ((e: MessageEvent<Req>) => void) | null;
  postMessage(data: unknown): void;
}
const ctx = globalThis as unknown as Scope;

let ready: Promise<unknown> | undefined;
const ensureReady = (): Promise<unknown> => {
  ready ??= init().catch((err) => {
    ready = undefined;
    throw err;
  });
  return ready;
};

ctx.onmessage = (e) => {
  const req = e.data;
  ensureReady()
    .then(() => {
      if (req.kind === "run") {
        const out = world_run(req.law, req.w, req.h, req.seed, req.ticks);
        ctx.postMessage({ id: req.id, kind: "run", out });
        return;
      }
      const hashes: Record<string, string> = {};
      for (const law of req.laws) hashes[law] = world_law_hash(law);
      ctx.postMessage({ id: req.id, kind: "meta", hashes, source: world_source() });
    })
    .catch((err) => ctx.postMessage({ id: req.id, kind: "error", error: `${err}` }));
};
