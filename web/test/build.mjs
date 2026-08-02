// Transpile the viewer's modules for the checks in `viewer.mjs`.
//
// The types are stripped with Vite's own `transformWithEsbuild`, so the check needs
// no dependency the site does not already build with. Nothing is bundled: each
// module is emitted separately and exercised as itself.
//
// The only adaptations are removing the CSS import and the module's own `boot()`
// call, neither of which means anything outside a browser, and exporting the
// `Viewer` class. Everything else is the shipped code.

import { mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { dirname, join } from "node:path";

import { transformWithEsbuild } from "vite";

const here = dirname(new URL(import.meta.url).pathname);
const src = join(here, "..", "src");
const out = join(here, "build");
mkdirSync(out, { recursive: true });

const MODULES = ["viewer-model", "viewer-review", "viewer-context", "viewer"];

for (const name of MODULES) {
  const adapted = readFileSync(join(src, `${name}.ts`), "utf8")
    .replace(/^import "\.\/viewer\.css";$/m, "")
    .replace(/^void boot\(\);$/m, "")
    .replace(/^class Viewer \{/m, "export class Viewer {")
    .replace(/from "\.\/([\w-]+)\.js"/g, 'from "./$1.mjs"');
  const { code } = await transformWithEsbuild(adapted, `${name}.ts`, { loader: "ts" });
  writeFileSync(join(out, `${name}.mjs`), code);
}
