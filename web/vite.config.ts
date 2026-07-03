import { defineConfig } from "vite";

// Three entry points, all self-contained (base "./"): the playground
// (index.html), the REPL (repl.html), and the determinism scrubber
// (scrubber.html). build-site.sh serves them at /play, /repl, and /scrub.
export default defineConfig({
  base: "./",
  build: {
    outDir: "dist",
    emptyOutDir: true,
    target: "es2022",
    rollupOptions: {
      input: { main: "index.html", repl: "repl.html", scrubber: "scrubber.html" },
    },
  },
  worker: { format: "es" },
});
