import { defineConfig } from "vite";

// Self-contained entry points, all base "./": the playground (index.html), the
// REPL (repl.html), the gallery landing page (gallery.html), and its residents,
// the determinism scrubber (scrubber.html), the double pendulum (pendulum.html),
// the branching timelines (branch.html), the chaos counter (chaos.html), the
// schedule map (schedule.html), the teleport demo (teleport.html plus its
// receiver iframe teleport-recv.html), the content-addressed Merkle DAG
// (merkle.html), and the incremental cell graph (incr.html). The static site
// serves them at /play, /repl, /gallery, /scrub, /pendulum, /branch, /chaos,
// /schedule, /teleport, /merkle, and /incr.
export default defineConfig({
  base: "./",
  build: {
    outDir: "dist",
    emptyOutDir: true,
    target: "es2022",
    rollupOptions: {
      input: {
        main: "index.html",
        repl: "repl.html",
        gallery: "gallery.html",
        scrubber: "scrubber.html",
        pendulum: "pendulum.html",
        branch: "branch.html",
        chaos: "chaos.html",
        schedule: "schedule.html",
        teleport: "teleport.html",
        "teleport-recv": "teleport-recv.html",
        merkle: "merkle.html",
        incr: "incr.html",
      },
    },
  },
  worker: { format: "es" },
});
