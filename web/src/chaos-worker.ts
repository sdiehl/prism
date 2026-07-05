// A dedicated worker for the chaos counter's batches. Each batch recompiles the
// swarm kernel in wasm (~1s) and runs `count` schedules; doing that off the main
// thread keeps the interleaving animation smooth while the counter climbs. The
// protocol is a bare {start, count} request answered with the raw `chaos_run`
// transcript (or an `error:` line).
import init, { chaos_run } from "../pkg/prism.js";

interface Req {
  start: number;
  count: number;
}
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
  const { start, count } = e.data;
  ensureReady()
    .then(() => ctx.postMessage(chaos_run(start, count)))
    .catch((err) => ctx.postMessage(`error: ${err}`));
};
