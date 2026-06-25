import init, { run } from "../pkg/prism.js";

interface WorkerScope {
  onmessage: ((e: MessageEvent<string>) => void) | null;
  postMessage(data: string): void;
}
const ctx = globalThis as unknown as WorkerScope;

let ready: Promise<unknown> | undefined;

ctx.onmessage = (e) => {
  ready ??= init();
  ready.then(() => ctx.postMessage(run(e.data)));
};
