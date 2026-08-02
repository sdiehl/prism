// Assembling a context packet for a set of definitions.
//
// The selection is a set of *definitions*, not a range of lines, and that is what
// makes the packet worth assembling. Handing an assistant "the file" gives it
// whatever else happens to live in that file and none of what the definition
// actually depends on. Handing it a definition's canonical name, inferred type,
// effect row, exact source, transitive dependencies, callers, and the tests that
// reach it gives it the same picture a reviewer builds by clicking around for ten
// minutes — and every part of it is a fact the compiler computed, not a guess
// from proximity.
//
// This builds the packet and stops there. Sending it somewhere is a request the
// reader makes with their own key, in their own tool; the part that needed to
// know how the codebase fits together is done here.
//
// Nothing in the viewer calls this yet. It had a UI — a `+` on every card that
// gathered definitions and a tray that copied the packet to the clipboard — and
// that UI was removed because copying a prompt is not asking a question: the
// reader wanted to ask in the browser and get an answer back. The assembly is the
// half that needed the compiler's facts, so it stays, checked, waiting for the
// half that needs a key and a network call.

import type { Def, Index, Relations } from "./viewer-model.js";
import type { Review } from "./viewer-review.js";

/// How much dependency source to include before saying so and stopping.
///
/// A budget is not politeness, it is honesty: the alternative to truncating is
/// either an unbounded packet or a silently clipped one, and a reader who cannot
/// see that the closure was cut cannot tell whether the answer was informed.
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

  // What the selection depends on, so the reader is not asked about a call it
  // cannot see the body of.
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

  // More than one definition selected means the question is probably about how
  // they relate, so say how they relate.
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

  // Behavioral duplicates come free from the addressing, and are worth stating:
  // they mean an answer about one applies verbatim to the others.
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

// How the selected definitions relate to each other, which is usually the actual
// question when more than one is selected.
//
// Reported as *paths*, not just direct edges. Two definitions a reader picks
// together are often several hops apart — that is frequently why they were picked
// together — and "no direct relation" would be a true statement that hides the
// answer. The route through the intermediate definitions is the relationship.
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
  // Bounded: a route long enough to need this many hops is not an explanation
  // anyone reading a packet would use.
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
