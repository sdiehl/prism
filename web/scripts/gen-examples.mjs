// Bake ../examples/*.pr into src/examples.ts so the static playground can offer
// them without a server. Runs automatically before `dev` and `build`.
import { readdirSync, readFileSync, writeFileSync } from "node:fs";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath } from "node:url";

const webRoot = resolve(dirname(fileURLToPath(import.meta.url)), "..");
const examplesDir = resolve(webRoot, "..", "examples");
const out = join(webRoot, "src", "examples.ts");

const examples = {};
for (const file of readdirSync(examplesDir).sort()) {
  if (!file.endsWith(".pr")) continue;
  examples[file.slice(0, -3)] = readFileSync(join(examplesDir, file), "utf8");
}

const body = JSON.stringify(examples, null, 2);
writeFileSync(out, `export const examples: Record<string, string> = ${body};\n`);
console.log(`wrote ${out} (${Object.keys(examples).length} examples)`);
