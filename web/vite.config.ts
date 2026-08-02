import { defineConfig } from "vite";

// Self-contained entry points, all base "./": the playground (index.html), the
// gallery landing page (gallery.html), and its residents,
// the determinism scrubber (scrubber.html), the double pendulum (pendulum.html),
// the branching timelines (branch.html), the chaos counter (chaos.html), the
// schedule map (schedule.html), the teleport demo (teleport.html plus its
// receiver iframe teleport-recv.html), the content-addressed Merkle DAG
// (merkle.html), the incremental cell graph (incr.html), the shared cellular
// universe (prism-world.html), and the code viewer over a `prism index` artifact
// (viewer.html). The static site serves them at /play,
// /gallery, /scrub, /pendulum, /branch, /chaos, /schedule, /teleport, /merkle,
// /incr, /world, and /viewer.
//
// The viewer is the one page that loads no wasm: it is a pure consumer of the
// index JSON, which is what lets it open an artifact generated anywhere.
export default defineConfig({
  base: "./",
  build: {
    outDir: "dist",
    emptyOutDir: true,
    target: "es2022",
    rollupOptions: {
      input: {
        main: "index.html",
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
        world: "prism-world.html",
        viewer: "viewer.html",
      },
    },
  },
  worker: { format: "es" },
});
