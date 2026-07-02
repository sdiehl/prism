import { defineConfig } from "vite";

// Two entry points, both self-contained (base "./"): the playground (index.html)
// and the REPL (repl.html). build-site.sh serves them at /play and /repl.
export default defineConfig({
  base: "./",
  build: {
    outDir: "dist",
    emptyOutDir: true,
    target: "es2022",
    rollupOptions: { input: { main: "index.html", repl: "repl.html" } },
  },
  worker: { format: "es" },
});
