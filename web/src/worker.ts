import init, { diagnostics, dump, run } from "../pkg/prism.js";

// Two message protocols share this worker. The playground posts a bare string
// and expects the run transcript back as a string (unchanged). The REPL posts a
// tagged request and gets a tagged reply, so it can multiplex `run` (evaluate),
// `diag` (type-check the current line) and `dump` (`:type`) over the one wasm
// instance.
interface Req {
  id: number;
  kind: "run" | "diag" | "dump";
  src: string;
}
type Incoming = string | Req;

interface WorkerScope {
  onmessage: ((e: MessageEvent<Incoming>) => void) | null;
  postMessage(data: unknown): void;
}
const ctx = globalThis as unknown as WorkerScope;

let ready: Promise<unknown> | undefined;

// Memoize the wasm init, but clear the cache if it REJECTS: a memoized failed
// init would poison the worker so every later message errors with no retry.
// Clearing lets the next request re-attempt the load.
const ensureReady = (): Promise<unknown> => {
  ready ??= init().catch((err) => {
    ready = undefined;
    throw err;
  });
  return ready;
};

ctx.onmessage = (e) => {
  const boot = ensureReady();
  const msg = e.data;
  if (typeof msg === "string") {
    boot.then(() => ctx.postMessage(run(msg))).catch((err) => ctx.postMessage(`error: ${err}`));
    return;
  }
  const { id, kind, src } = msg;
  const call = (): string => {
    if (kind === "diag") return diagnostics(src);
    if (kind === "dump") return dump(src);
    return run(src);
  };
  // A wasm trap (e.g. a stack overflow on deep recursion) rejects `boot`/`call`;
  // without this a reply is never posted and the awaiting REPL caller hangs
  // forever. Always answer, tagging the failure so the caller renders an error.
  boot
    .then(() => ctx.postMessage({ id, data: call() }))
    .catch((err) => ctx.postMessage({ id, data: `error: ${err}` }));
};
