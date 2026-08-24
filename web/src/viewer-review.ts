// Browser-local review state anchored to definition identity and content address.

import type { Def, Index } from "./viewer-model.js";

/// How a definition stands relative to the revision a mark was made against.
///
/// Uses the same four-way split as `prism index --diff`. A cross-check test pins
/// these verdicts against the compiler's classifications.
export type Freshness = "current" | "cosmetic" | "cone" | "changed" | "gone";

export interface Mark {
  /// Canonical name: the mark's anchor.
  id: string;
  /// Whether the definition has been read and accepted.
  reviewed: boolean;
  /// Free-form review notes.
  note?: string;
  /// The address when the mark was last touched, and the text at that address.
  /// The text is what lets a later comparison separate a reformat and a
  /// dependency shift from a real edit, instead of only saying "something moved".
  hash?: string;
  source?: string;
  /// The review-facing facts neither the hash nor the text sees (see `metaOf`),
  /// as stamped when the mark was touched.
  meta?: string;
  /// Milliseconds since the epoch, for ordering a review session.
  at: number;
}

/// Review-facing facts outside a definition's hash and source text. Claims erase
/// before hashing, and doc comments sit outside `source`.
export function metaOf(def: Def): string {
  return JSON.stringify([
    def.claims ?? [],
    def.vis ?? "private",
    def.doc ?? "",
    def.deprecated ?? "",
  ]);
}

/// Classify a definition against the revision a mark recorded.
///
/// Matches the compiler's diff rule: equal addresses mean equal behavior, while a
/// moved address with unchanged text indicates a dependency change.
export function freshness(mark: Mark, def: Def | undefined): Freshness {
  if (!def) return "gone";
  // Claims, visibility, doc, deprecation: authored edits the hash never sees
  // and the text may not either. Compared only when the mark stamped them, so a
  // mark from before the stamp existed degrades to the hash-and-text rule
  // rather than reading every definition as edited.
  if (mark.meta !== undefined && mark.meta !== metaOf(def)) return "changed";
  if (mark.hash === undefined || def.hash === undefined) {
    return mark.source === def.source ? "current" : "changed";
  }
  if (mark.hash === def.hash) return mark.source === def.source ? "current" : "cosmetic";
  return mark.source === def.source ? "cone" : "changed";
}

/// Whether a definition needs the reviewer's attention again: they accepted it,
/// and its behavior has since moved. A cosmetic change does not qualify; that is
/// the noise this is meant to suppress.
export function needsAttention(mark: Mark, def: Def | undefined): boolean {
  if (!mark.reviewed) return false;
  const f = freshness(mark, def);
  return f === "changed" || f === "cone" || f === "gone";
}

const VERSION = "prism-review-v1";

interface Stored {
  format: string;
  /// The indexed unit these marks belong to: the artifact's URL joined with its
  /// title (see `boot`). Not the revision's contract digest, which moves on
  /// every change and would drop the marks exactly when they become
  /// interesting. The title alone is also insufficient because two unrelated
  /// projects can share one, letting one project's `main` display another's notes.
  unit: string;
  marks: Mark[];
}

/// The mark store, backed by `localStorage`.
export class Review {
  private readonly marks = new Map<string, Mark>();
  private readonly key: string;

  constructor(
    private readonly unit: string,
    private readonly storage: Storage | null,
  ) {
    this.key = `${VERSION}:${unit}`;
    this.load();
  }

  private load(): void {
    try {
      const raw = this.storage?.getItem(this.key);
      if (!raw) return;
      const doc = JSON.parse(raw) as Stored;
      if (doc?.format !== VERSION) return;
      for (const m of doc.marks ?? []) this.marks.set(m.id, m);
    } catch {
      // A corrupt or unreadable store is not worth failing the page over; the
      // reviewer loses notes, not the ability to read code.
    }
  }

  private save(): void {
    const doc: Stored = { format: VERSION, unit: this.unit, marks: [...this.marks.values()] };
    try {
      this.storage?.setItem(this.key, JSON.stringify(doc));
    } catch {
      // Quota or a disabled store: keep the in-memory marks working.
    }
  }

  /// Whether the definition list was left showing. A layout preference rather than
  /// review state, kept here because this is what already owns the browser's
  /// storage; it is stored apart from the marks so it cannot be mistaken for one.
  railShown(): boolean {
    return this.storage?.getItem(`${VERSION}:rail`) !== "hidden";
  }

  setRailShown(shown: boolean): void {
    try {
      this.storage?.setItem(`${VERSION}:rail`, shown ? "shown" : "hidden");
    } catch {
      // Quota or a disabled store: the preference is not worth failing over.
    }
  }

  get(id: string): Mark | undefined {
    return this.marks.get(id);
  }

  all(): Mark[] {
    return [...this.marks.values()].sort((a, b) => b.at - a.at);
  }

  /// Record something about a definition, stamping the revision it was recorded
  /// against so a later comparison has something to compare with.
  set(def: Def, patch: Partial<Pick<Mark, "reviewed" | "note">>, now: number): Mark {
    const prior = this.marks.get(def.id);
    const mark: Mark = {
      id: def.id,
      reviewed: patch.reviewed ?? prior?.reviewed ?? false,
      // Present-and-undefined means "clear this", absent means "leave it alone".
      // `??` cannot tell those apart, so clearing a note used to restore the old
      // one and the note could never be deleted.
      note: "note" in patch ? patch.note : prior?.note,
      hash: def.hash,
      source: def.source,
      meta: metaOf(def),
      at: now,
    };
    if (!mark.reviewed && !mark.note) this.marks.delete(def.id);
    else this.marks.set(def.id, mark);
    this.save();
    return mark;
  }

  /// Every mark whose definition has moved since it was made.
  stale(index: Index): Mark[] {
    return this.all().filter((m) => needsAttention(m, index.byId.get(m.id)));
  }

  /// Follow marks across renames and file moves, which change the canonical
  /// name a mark is keyed by while preserving the content the mark is *about*.
  /// Without this, moving a module silently orphans every mark in it despite the
  /// content-address anchor.
  ///
  /// Two sources, tried in order. A loaded diff knows moves as facts
  /// (`old_id` → `id`), so those re-key directly. Failing that, a mark whose id
  /// left the index follows its stamped hash, but only when it has an *unambiguous*
  /// destination. Two definitions can legitimately share a behavior
  /// hash and guessing which one the mark meant would attach a review to code
  /// nobody reviewed.
  rekey(moves: Map<string, string>, index: Index): void {
    let moved = false;
    const move = (mark: Mark, to: string): void => {
      this.marks.delete(mark.id);
      this.marks.set(to, { ...mark, id: to });
      moved = true;
    };
    for (const [from, to] of moves) {
      const mark = this.marks.get(from);
      if (mark && !this.marks.has(to)) move(mark, to);
    }
    const byHash = new Map<string, Def[]>();
    for (const d of index.defs) {
      if (!d.hash) continue;
      const at = byHash.get(d.hash);
      if (at) at.push(d);
      else byHash.set(d.hash, [d]);
    }
    for (const mark of [...this.marks.values()]) {
      if (!mark.hash || index.byId.has(mark.id)) continue;
      const found = byHash.get(mark.hash) ?? [];
      if (found.length === 1 && !this.marks.has(found[0].id)) move(mark, found[0].id);
    }
    if (moved) this.save();
  }
}
