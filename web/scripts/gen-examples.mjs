// Bake the manifest's wasm-capable gallery/showcase programs into examples.ts.
// Compiler/runtime fixtures and host-only programs stay in the repository
// without leaking into the public playground.
import { existsSync, readdirSync, readFileSync, writeFileSync } from "node:fs";
import { basename, dirname, join, relative, resolve, sep } from "node:path";
import { fileURLToPath } from "node:url";

const webRoot = resolve(dirname(fileURLToPath(import.meta.url)), "..");
const examplesDir = resolve(webRoot, "..", "examples");
const manifestPath = join(examplesDir, "manifest.toml");
const out = join(webRoot, "src", "examples.ts");

function valueOf(raw, line) {
  try {
    return JSON.parse(raw);
  } catch {
    throw new Error(`${manifestPath}:${line}: values must use JSON-compatible TOML syntax`);
  }
}

function parseManifest(source) {
  const manifest = { defaults: {}, examples: [] };
  let target = manifest;
  for (const [index, original] of source.split(/\r?\n/).entries()) {
    const line = original.trim();
    if (line === "" || line.startsWith("#")) continue;
    if (line === "[defaults]") {
      target = manifest.defaults;
      continue;
    }
    if (line === "[[example]]") {
      target = {};
      manifest.examples.push(target);
      continue;
    }
    const match = /^([a-z_]+)\s*=\s*(.+)$/.exec(line);
    if (!match) throw new Error(`${manifestPath}:${index + 1}: unsupported TOML syntax`);
    target[match[1]] = valueOf(match[2], index + 1);
  }
  return manifest;
}

function prismFiles(dir) {
  if (!existsSync(dir)) return [];
  const found = [];
  for (const entry of readdirSync(dir, { withFileTypes: true })) {
    const path = join(dir, entry.name);
    if (entry.isDirectory()) found.push(...prismFiles(path));
    if (entry.isFile() && entry.name.endsWith(".pr")) found.push(path);
  }
  return found;
}

const parsed = parseManifest(readFileSync(manifestPath, "utf8"));
const entries = parsed.examples.map((entry) => ({ ...parsed.defaults, ...entry }));
const roles = new Set(["gallery", "showcase", "fixture"]);
const outputModes = new Set(["exact", "host-dependent", "input-fixture", "multi-run"]);
const seenPaths = new Set();
const seenIds = new Set();

for (const entry of entries) {
  for (const field of ["path", "title", "category", "role", "platforms", "expected_output"]) {
    if (entry[field] == null) throw new Error(`${manifestPath}: ${entry.path ?? "entry"} lacks ${field}`);
  }
  if (!roles.has(entry.role)) throw new Error(`${manifestPath}: invalid role ${entry.role}`);
  if (!outputModes.has(entry.expected_output)) {
    throw new Error(`${manifestPath}: invalid expected_output ${entry.expected_output}`);
  }
  if (!Array.isArray(entry.platforms) || entry.platforms.length === 0) {
    throw new Error(`${manifestPath}: ${entry.path} needs at least one platform`);
  }
  if (entry.path.startsWith("/") || entry.path.split("/").includes("..")) {
    throw new Error(`${manifestPath}: unsafe example path ${entry.path}`);
  }
  const path = join(examplesDir, entry.path);
  if (!existsSync(path)) throw new Error(`${manifestPath}: missing ${entry.path}`);
  if (seenPaths.has(entry.path)) throw new Error(`${manifestPath}: duplicate path ${entry.path}`);
  seenPaths.add(entry.path);
  const id = basename(entry.path, ".pr");
  if (entry.role !== "fixture" && seenIds.has(id)) {
    throw new Error(`${manifestPath}: duplicate public id ${id}`);
  }
  if (entry.role !== "fixture") seenIds.add(id);
  entry.id = id;
}

// Every public top-level program and every nested fixture must be classified.
// Other nested example projects carry their own manifests and are outside this
// playground inventory.
const inventoried = [
  ...prismFiles(examplesDir).filter((path) => dirname(path) === examplesDir),
  ...prismFiles(join(examplesDir, "fixtures")),
].map((path) => relative(examplesDir, path).split(sep).join("/"));
const missing = inventoried.filter((path) => !seenPaths.has(path));
const stale = [...seenPaths].filter((path) => !inventoried.includes(path));
if (missing.length || stale.length) {
  throw new Error(
    `${manifestPath}: inventory mismatch` +
      `${missing.length ? `\nunclassified: ${missing.join(", ")}` : ""}` +
      `${stale.length ? `\nstale: ${stale.join(", ")}` : ""}`,
  );
}

const visible = entries
  .filter((entry) => entry.role !== "fixture" && entry.platforms.includes("wasm"))
  .sort((a, b) => a.category.localeCompare(b.category) || a.title.localeCompare(b.title));
const examples = Object.fromEntries(
  visible.map((entry) => [entry.id, readFileSync(join(examplesDir, entry.path), "utf8")]),
);
const metadata = visible.map(
  ({ id, title, category, role, platforms, expected_output, allow_stdlib_reimplementation }) => ({
    id,
    title,
    category,
    role,
    platforms,
    expectedOutput: expected_output,
    allowStdlibReimplementation: allow_stdlib_reimplementation ?? [],
  }),
);

const body = JSON.stringify(examples, null, 2);
const meta = JSON.stringify(metadata, null, 2);
writeFileSync(
  out,
  `export interface ExampleMeta {
  id: string;
  title: string;
  category: string;
  role: "gallery" | "showcase";
  platforms: string[];
  expectedOutput: string;
  allowStdlibReimplementation: string[];
}

export const exampleMeta: ExampleMeta[] = ${meta};

export const examples: Record<string, string> = ${body};
`,
);
console.log(`wrote ${out} (${visible.length} manifest-selected examples)`);
