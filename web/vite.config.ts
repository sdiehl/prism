import { defineConfig } from "vite";

export default defineConfig({
  base: "./",
  build: { outDir: "dist", emptyOutDir: true, target: "es2022" },
  worker: { format: "es" },
});
