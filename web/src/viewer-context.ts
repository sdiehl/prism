// Build a Markdown context packet from compiler-index facts. Transport and UI are
// separate concerns, and no current viewer path calls this module.

import type { Def, Index, Relations } from "./viewer-model.js";
import type { Review } from "./viewer-review.js";

/// Maximum dependency source included in one packet, in bytes.
const DEPENDENCY_BUDGET = 24_000;

export interface PacketInput {
  index: Index;
  rel: Relations;
  review: Review | null;
  /// The canonical names the reader selected, in selection order.
  selected: string[];
}

/// Build the packet as Markdown.
export function packet({ index, rel, review, selected }: PacketInput): string {
  const defs = selected.map((id) => index.byId.get(id)).filter((d): d is Def => d !== undefined);
  if (defs.length === 0) return "";
  const out: string[] = [];
  const e = index.envelope;

  out.push(`# ${e.title}`);
  out.push(
    `Content-addressed at \`${e.contract.slice(0, 16)}…\` (${e.scheme}, prism ${e.compiler}). ` +
      `Every fact below is the compiler's, not inferred from context.`,
  );

  out.push(`\n## Selected (${defs.length})`);
  for (const d of defs) out.push(describe(d, rel, index, review));

  // Include the selected definitions' dependency closure.
  const closure = dependencies(defs, rel, index);
  if (closure.included.length > 0) {
    out.push(`\n## Reached by the above (${closure.included.length})`);
    for (const d of closure.included) {
      out.push(`\n### \`${d.id}\`${d.ty ? ` : ${d.ty}` : ""}\n\n\`\`\`prism\n${d.source}\n\`\`\``);
    }
  }
  if (closure.omitted > 0) {
    out.push(
      `\n_${closure.omitted} further reached definitions omitted to stay inside the context budget._`,
    );
  }

  // Relate multiple selected definitions.
  if (defs.length > 1) {
    const between = relationsAmong(defs, rel);
    out.push(`\n## Between the selected definitions`);
    out.push(between.length > 0 ? between.join("\n") : "_No direct relation between them._");
  }

  const notes = defs
    .map((d) => [d, review?.get(d.id)] as const)
    .filter(([, m]) => m?.note)
    .map(([d, m]) => `- \`${d.id}\`: ${m?.note ?? ""}`);
  if (notes.length > 0) out.push(`\n## Review notes\n${notes.join("\n")}`);

  return `${out.join("\n")}\n`;
}

// One definition, with everything the index knows about it.
function describe(d: Def, rel: Relations, index: Index, review: Review | null): string {
  const facts: string[] = [];
  facts.push(`Module \`${d.module || "(root)"}\`, ${d.kind}, ${d.vis ?? "private"}`);
  if (d.hash) facts.push(`address \`${d.hash.slice(0, 16)}…\``);
  if (d.effects) facts.push(`effects \`${d.effects}\``);
  if (d.claims?.length) facts.push(`claims ${d.claims.join(", ")}`);
  if (d.deprecated) facts.push(`deprecated: ${d.deprecated}`);

  const lines = [`\n### \`${d.id}\``, facts.join(" · ")];
  if (d.ty) lines.push(`\nType: \`${d.ty}\``);
  if (d.doc) lines.push(`\n${d.doc}`);
  lines.push(`\n\`\`\`prism\n${d.source}\n\`\`\``);

  const named = (ids: string[]): string => ids.map((i) => `\`${i}\``).join(", ");
  const callers = rel.get("calls", "in", d.id);
  const tests = rel.get("tests", "in", d.id);
  if (callers.length > 0)
    lines.push(`Called by ${named(callers.slice(0, 12))}${more(callers, 12)}`);
  else lines.push("Called by nothing in this index.");
  lines.push(
    tests.length > 0
      ? `Exercised by ${named(tests)}`
      : "No test in this index reaches this definition.",
  );

  // Equal content addresses identify behavioral duplicates.
  const twins = index.defs.filter((o) => o.hash && o.hash === d.hash && o.id !== d.id);
  if (twins.length > 0) {
    lines.push(`Identical behavior to ${named(twins.map((t) => t.id))} (same content address).`);
  }
  const mark = review?.get(d.id);
  if (mark?.reviewed) lines.push(`Previously reviewed at \`${mark.hash?.slice(0, 12) ?? "?"}\`.`);
  return lines.join("\n");
}

// The transitive call closure of the selection, breadth-first so the nearest
// dependencies land inside the budget rather than whatever the walk reached first.
function dependencies(
  defs: Def[],
  rel: Relations,
  index: Index,
): { included: Def[]; omitted: number } {
  const seen = new Set(defs.map((d) => d.id));
  const queue = defs.flatMap((d) => rel.get("calls", "out", d.id));
  const included: Def[] = [];
  let spent = 0;
  let omitted = 0;
  while (queue.length > 0) {
    const id = queue.shift();
    if (id === undefined || seen.has(id)) continue;
    seen.add(id);
    const d = index.byId.get(id);
    if (!d) continue;
    if (spent + d.source.length > DEPENDENCY_BUDGET) {
      omitted++;
      continue;
    }
    spent += d.source.length;
    included.push(d);
    queue.push(...rel.get("calls", "out", id));
  }
  return { included, omitted };
}

// Report complete call paths between selected definitions.
function relationsAmong(defs: Def[], rel: Relations): string[] {
  const lines: string[] = [];
  for (const from of defs) {
    for (const to of defs) {
      if (from === to) continue;
      const route = path(from.id, to.id, rel);
      if (route) {
        lines.push(`- ${route.map((s) => `\`${s}\``).join(" → ")}`);
      }
    }
  }
  const same = defs.filter((a) => defs.some((b) => b !== a && a.hash && a.hash === b.hash));
  if (same.length > 1) {
    lines.push(`- ${same.map((d) => `\`${d.id}\``).join(" and ")} have identical behavior`);
  }
  return [...new Set(lines)];
}

// The shortest call route from one definition to another, or `null` when it does
// not reach it. Breadth-first, so the route reported is the most direct one.
function path(from: string, to: string, rel: Relations): string[] | null {
  const back = new Map<string, string>();
  const seen = new Set([from]);
  let frontier = [from];
  // Bound route length to keep the packet useful.
  for (let depth = 0; depth < 8 && frontier.length > 0; depth++) {
    const next: string[] = [];
    for (const at of frontier) {
      for (const step of rel.get("calls", "out", at)) {
        if (seen.has(step)) continue;
        seen.add(step);
        back.set(step, at);
        if (step === to) {
          const route = [to];
          for (let cur = to; cur !== from; ) {
            const prev = back.get(cur);
            if (prev === undefined) break;
            route.unshift(prev);
            cur = prev;
          }
          return route;
        }
        next.push(step);
      }
    }
    frontier = next;
  }
  return null;
}

const more = (xs: string[], shown: number): string =>
  xs.length > shown ? ` and ${xs.length - shown} more` : "";
