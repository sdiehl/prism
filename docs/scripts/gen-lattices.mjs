// Generate the lattice figures for the spec as standalone SVGs: three for
// section 5.1 and the coeffect-axes grid for section 7.9.
// Zero dependencies, deterministic: integer geometry, no timestamps, no
// randomness. Running twice changes nothing. Diagrams are edited by the data
// consts below, not by pixel surgery.
import { writeFileSync } from "node:fs";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath } from "node:url";

const outDir = resolve(dirname(fileURLToPath(import.meta.url)), "..", "src", "images");

// Palette: mid-tone neutrals that read on both mdbook light and dark themes,
// plus one accent (the brand green, lifted to mid luminance so it survives a
// near-black background). Nothing here is pure black or pure white.
const STROKE = "#8a8f98"; // structure: edges, node outlines
const TEXT = "#6f747c"; // labels, balanced contrast on white and near-black
const ACCENT = "#2f9e63"; // the join, the meet, the chain arrows only
const WASH = "rgba(47, 158, 99, 0.12)"; // accent node fill

const MONO = "ui-monospace, SFMono-Regular, Menlo, monospace";
const FONT = 13; // code-label size
const CAPTION = 11; // annotation size
const CHAR_W = 7.8; // mono advance at FONT, for chip sizing
const PAD_X = 12; // chip horizontal padding
const CHIP_H = 27;
const half = Math.round(CHIP_H / 2);
const MIN_W = 46;
const EDGE_W = 1.25;
const RADIUS = 7;

const chipW = (label) => Math.max(MIN_W, Math.round(label.length * CHAR_W + PAD_X * 2));

// A lattice point drawn as a rounded-rect label chip. kind "accent" fills with
// the wash and strokes green; "plain" is a neutral outline.
function chip(node) {
  const w = chipW(node.label);
  const x = node.cx - Math.round(w / 2);
  const y = node.cy - Math.round(CHIP_H / 2);
  const accent = node.kind === "accent";
  const fill = accent ? WASH : "none";
  const stroke = accent ? ACCENT : STROKE;
  return [
    `<rect x="${x}" y="${y}" width="${w}" height="${CHIP_H}" rx="${RADIUS}" `
    + `fill="${fill}" stroke="${stroke}" stroke-width="${EDGE_W}"/>`,
    `<text x="${node.cx}" y="${node.cy}" font-family="${MONO}" font-size="${FONT}" `
    + `fill="${TEXT}" text-anchor="middle" dominant-baseline="central">`
    + esc(node.label) + `</text>`,
  ].join("\n");
}

// An edge connects the bottom of the upper node to the top of the lower node.
// Dashed edges signal a relation to a missing point.
function edge(a, b, dashed) {
  const y1 = a.cy + half;
  const y2 = b.cy - half;
  const dash = dashed ? ` stroke-dasharray="4 4"` : "";
  return `<line x1="${a.cx}" y1="${y1}" x2="${b.cx}" y2="${y2}" `
    + `stroke="${STROKE}" stroke-width="${EDGE_W}"${dash}/>`;
}

// A vertical accent arrow along a total-order chain, arrowhead at the top (up
// is greater). Connects the top of the lower chip to the bottom of the upper.
function upArrow(lower, upper) {
  const x = lower.cx;
  const yBot = lower.cy - half;
  const yTop = upper.cy + half;
  return [
    `<line x1="${x}" y1="${yBot}" x2="${x}" y2="${yTop + 6}" `
    + `stroke="${ACCENT}" stroke-width="${EDGE_W}"/>`,
    `<path d="M ${x} ${yTop} L ${x - 4} ${yTop + 7} L ${x + 4} ${yTop + 7} Z" fill="${ACCENT}"/>`,
  ].join("\n");
}

// The visibly missing meet: a dashed circle struck through with an X, captioned
// so the absence is explicit rather than merely an empty space.
function absentMeet(cx, cy) {
  const r = 13;
  return [
    `<circle cx="${cx}" cy="${cy}" r="${r}" fill="none" stroke="${STROKE}" `
    + `stroke-width="${EDGE_W}" stroke-dasharray="4 4"/>`,
    `<line x1="${cx - 6}" y1="${cy - 6}" x2="${cx + 6}" y2="${cy + 6}" `
    + `stroke="${STROKE}" stroke-width="${EDGE_W}"/>`,
    `<line x1="${cx - 6}" y1="${cy + 6}" x2="${cx + 6}" y2="${cy - 6}" `
    + `stroke="${STROKE}" stroke-width="${EDGE_W}"/>`,
    `<text x="${cx}" y="${cy + r + 14}" font-family="${MONO}" font-size="${CAPTION}" `
    + `fill="${TEXT}" text-anchor="middle" dominant-baseline="central">(no meet)</text>`,
  ].join("\n");
}

// A borderless mono label: the keyword alias sitting beside a chain node, and a
// faint dotted tick pairing it to that node.
function aliasLabel(node, x, label) {
  const w = chipW(node.label);
  const rightEdge = node.cx + Math.round(w / 2);
  return [
    `<line x1="${rightEdge + 4}" y1="${node.cy}" x2="${x - 4}" y2="${node.cy}" `
    + `stroke="${STROKE}" stroke-width="1" stroke-dasharray="2 3"/>`,
    `<text x="${x}" y="${node.cy}" font-family="${MONO}" font-size="${FONT}" `
    + `fill="${TEXT}" text-anchor="start" dominant-baseline="central">`
    + esc(label) + `</text>`,
  ].join("\n");
}

// A centered mono caption (axis direction, "(no meet)"-style notes).
function caption(cx, cy, text, color, size) {
  return `<text x="${cx}" y="${cy}" font-family="${MONO}" font-size="${size}" `
    + `fill="${color}" text-anchor="middle" dominant-baseline="central">${esc(text)}</text>`;
}

// A direction pill: a small rounded chip with an inline arrow and a word, one
// uniform style (soft-fill, stroke of the same hue, no dashes) differentiated
// only by hue plus the chevron. Past points left in a soft blue (the fact
// travels back with the value from its producer); future points right in a soft
// amber (the fact constrains what may still be done). Both pastels read on the
// light and dark themes and neither competes with the single green Fip accent.
const DIR_STYLE = {
  past: { fill: "rgba(77, 132, 200, 0.16)", stroke: "rgba(77, 132, 200, 0.62)", ink: "#4d84c8" },
  future: { fill: "rgba(202, 132, 62, 0.18)", stroke: "rgba(202, 132, 62, 0.64)", ink: "#c07f2e" },
};
const DIR_H = 18;
function dirPill(cx, cy, dir) {
  const past = dir === "past";
  const label = dir;
  const style = DIR_STYLE[dir];
  const arrowW = 7;
  const gap = 5;
  const textW = Math.round(label.length * (CAPTION * 0.6));
  const innerPad = 9;
  const w = arrowW + gap + textW + innerPad * 2;
  const x = cx - Math.round(w / 2);
  const y = cy - Math.round(DIR_H / 2);
  // Arrow apex and base: left-pointing for past, right-pointing for future.
  const ax = x + innerPad;
  const amid = cy;
  const arrow = past
    ? `<path d="M ${ax} ${amid} L ${ax + arrowW} ${amid - 4} L ${ax + arrowW} ${amid + 4} Z" fill="${style.ink}"/>`
    : `<path d="M ${ax + arrowW} ${amid} L ${ax} ${amid - 4} L ${ax} ${amid + 4} Z" fill="${style.ink}"/>`;
  const tx = ax + arrowW + gap;
  return [
    `<rect x="${x}" y="${y}" width="${w}" height="${DIR_H}" rx="${Math.round(DIR_H / 2)}" `
    + `fill="${style.fill}" stroke="${style.stroke}" stroke-width="1"/>`,
    arrow,
    `<text x="${tx}" y="${cy}" font-family="${MONO}" font-size="${CAPTION}" `
    + `fill="${style.ink}" text-anchor="start" dominant-baseline="central">${esc(label)}</text>`,
  ].join("\n");
}

// A centered mini-lattice title, the axis name in a slightly heavier weight.
function title(cx, cy, text) {
  return `<text x="${cx}" y="${cy}" font-family="${MONO}" font-size="${FONT}" `
    + `font-weight="600" fill="${TEXT}" text-anchor="middle" dominant-baseline="central">`
    + esc(text) + `</text>`;
}

const esc = (s) => s.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;");

function svg(w, h, ariaLabel, desc, body) {
  return [
    `<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 ${w} ${h}" `
    + `role="img" aria-label="${esc(ariaLabel)}">`,
    `<title>${esc(ariaLabel)}</title>`,
    `<desc>${esc(desc)}</desc>`,
    body,
    `</svg>`,
    ``,
  ].join("\n");
}

// -- Figure 1: effect-row diamond. Join (top) is accent; handling walks down. --
const rowsTop = { label: "{IO, Ask}", cx: 210, cy: 42, kind: "accent" };
const rowsL = { label: "{IO}", cx: 118, cy: 118, kind: "plain" };
const rowsR = { label: "{Ask}", cx: 302, cy: 118, kind: "plain" };
const rowsBot = { label: "{ }", cx: 210, cy: 194, kind: "plain" };

const rowsSvg = svg(
  420,
  236,
  "the effect row lattice: {IO, Ask} above {IO} and {Ask} above the empty row",
  "A diamond. The join {IO, Ask} sits at the top, {IO} and {Ask} in the "
    + "middle, and the empty row { } at the bottom. Sequencing joins upward by "
    + "union; handling subtracts back down toward the pure bottom.",
  [
    edge(rowsTop, rowsL),
    edge(rowsTop, rowsR),
    edge(rowsL, rowsBot),
    edge(rowsR, rowsBot),
    chip(rowsTop),
    chip(rowsL),
    chip(rowsR),
    chip(rowsBot),
  ].join("\n"),
);

// -- Figure 2: two coeffect axes. Left has no meet; right meets at accent. --
const axL_top = { label: "(no claim)", cx: 152, cy: 44, kind: "plain" };
const axL_l = { label: "once", cx: 90, cy: 120, kind: "plain" };
const axL_r = { label: "many", cx: 214, cy: 120, kind: "plain" };
const axL_meet = { cx: 152, cy: 198 };

const axR_top = { label: "(no claim)", cx: 440, cy: 44, kind: "plain" };
const axR_l = { label: "linear", cx: 372, cy: 120, kind: "plain" };
const axR_r = { label: "bounded_stack", cx: 512, cy: 120, kind: "plain" };
const axR_meet = { label: "{linear, bounded_stack}", cx: 440, cy: 198, kind: "accent" };

const axesSvg = svg(
  600,
  252,
  "two coeffect axes: an exclusive axis with once and many that has no meet "
    + "below them, and the fip axis with linear and bounded_stack that meet at "
    + "{linear, bounded_stack}",
  "Left axis: (no claim) over once and many, with dashed edges descending to a "
    + "struck-out circle marked (no meet), because once and many have no lower "
    + "bound. Right axis: (no claim) over linear and bounded_stack, which meet "
    + "at {linear, bounded_stack}.",
  [
    edge(axL_top, axL_l),
    edge(axL_top, axL_r),
    edge(axL_l, { cx: axL_meet.cx, cy: axL_meet.cy }, true),
    edge(axL_r, { cx: axL_meet.cx, cy: axL_meet.cy }, true),
    absentMeet(axL_meet.cx, axL_meet.cy),
    chip(axL_top),
    chip(axL_l),
    chip(axL_r),
    edge(axR_top, axR_l),
    edge(axR_top, axR_r),
    edge(axR_l, axR_meet),
    edge(axR_r, axR_meet),
    chip(axR_top),
    chip(axR_l),
    chip(axR_r),
    chip(axR_meet),
  ].join("\n"),
);

// -- Figure 3: grade chain, a single vertical total order with accent arrows. --
const grMany = { label: "many", cx: 104, cy: 44, kind: "plain" };
const grOnce = { label: "once", cx: 104, cy: 134, kind: "plain" };
const grNever = { label: "never", cx: 104, cy: 224, kind: "plain" };
const ALIAS_X = 168;

const gradesSvg = svg(
  300,
  268,
  "the grade chain: many over once over never, a single vertical total order, "
    + "paired with the keywords ctl, fun, and final ctl",
  "Three chips stacked vertically with upward accent arrows: many at the top, "
    + "once in the middle, never at the bottom. Each is paired by a dotted tick "
    + "to its keyword: many to ctl, once to fun, never to final ctl.",
  [
    upArrow(grOnce, grMany),
    upArrow(grNever, grOnce),
    chip(grMany),
    chip(grOnce),
    chip(grNever),
    aliasLabel(grMany, ALIAS_X, "ctl"),
    aliasLabel(grOnce, ALIAS_X, "fun"),
    aliasLabel(grNever, ALIAS_X, "final ctl"),
  ].join("\n"),
);

// -- Figure 4: the whole coeffect vocabulary, one mini-lattice per axis. --
// A 3-row by 2-column grid in table order. Accent marks only the two special
// points: the one checked fact today (noalloc) and the fip meet. Every reserved
// fact chip stays plain. Which axes have a meet (compose), which are exclusive
// (no meet), and which are single points is legible at a glance.
const Y_TITLE = 22; // panel-local baselines, from the content origin
const Y_DIR = 39;
const Y_TOP = 70;
const Y_MID = 124;
const Y_BOT = 178;
const NOTE_DY = 25; // caption offset below a chip

// Each panel sits in a faint rounded box with even inner padding, and the boxes
// are spaced by an outer gutter so they do not crowd. The box stroke is well
// below the chip strokes in weight so it stays subordinate on both themes.
const BOX_W = 310;
const BOX_H = 216;
const BOX_T = 4; // content origin sits this far below the box top
const GUTTER = 18;
const MARGIN = 16;
const STRIDE_X = BOX_W + GUTTER;
const STRIDE_Y = BOX_H + GUTTER;
const BOX_RX = 9;
const BOX_STROKE = "rgba(138, 143, 152, 0.35)";
const BOX_FILL = "rgba(138, 143, 152, 0.04)";
function panelBox(x, y) {
  return `<rect x="${x}" y="${y}" width="${BOX_W}" height="${BOX_H}" rx="${BOX_RX}" `
    + `fill="${BOX_FILL}" stroke="${BOX_STROKE}" stroke-width="1"/>`;
}

// Each axis as declarative data. kind: chain2 (top over one fact), meet (diamond
// with a lower bound), nomeet (exclusive, lower bound absent).
const AXES = [
  { title: "Allocation", dir: "past", kind: "chain2", bottom: { label: "noalloc", note: "checked" } },
  { title: "Fip", dir: "past", kind: "meet", left: "linear", right: "bounded_stack", meet: "{linear, bounded_stack}", spread: 75 },
  { title: "Multiplicity", dir: "future", kind: "nomeet", left: "once", right: "many", spread: 56 },
  { title: "Aliasing", dir: "past", kind: "nomeet", left: "unique", right: "aliased", spread: 60 },
  { title: "Escape", dir: "future", kind: "nomeet", left: "local", right: "noescape", spread: 62 },
  { title: "Mobility", dir: "past", kind: "chain2", bottom: { label: "portable" } },
];

function cell(spec, i) {
  const col = i % 2;
  const row = Math.floor(i / 2);
  const boxLeft = MARGIN + col * STRIDE_X;
  const boxTop = MARGIN + row * STRIDE_Y;
  const cx = boxLeft + Math.round(BOX_W / 2);
  const y0 = boxTop - BOX_T; // content origin, keeps every panel-local offset
  const out = [
    panelBox(boxLeft, boxTop),
    title(cx, y0 + Y_TITLE, spec.title),
    dirPill(cx, y0 + Y_DIR, spec.dir),
  ];
  const top = { label: "(no claim)", cx, cy: y0 + Y_TOP, kind: "plain" };
  if (spec.kind === "chain2") {
    const bottom = { label: spec.bottom.label, cx, cy: y0 + Y_BOT, kind: "plain" };
    out.push(edge(top, bottom), chip(top), chip(bottom));
    if (spec.bottom.note) out.push(caption(cx, bottom.cy + NOTE_DY, spec.bottom.note, TEXT, CAPTION));
  } else {
    const l = { label: spec.left, cx: cx - spec.spread, cy: y0 + Y_MID, kind: "plain" };
    const r = { label: spec.right, cx: cx + spec.spread, cy: y0 + Y_MID, kind: "plain" };
    out.push(edge(top, l), edge(top, r));
    if (spec.kind === "meet") {
      const m = { label: spec.meet, cx, cy: y0 + Y_BOT, kind: "accent" };
      out.push(edge(l, m), edge(r, m), chip(top), chip(l), chip(r), chip(m));
    } else {
      const at = { cx, cy: y0 + Y_BOT };
      out.push(edge(l, at, true), edge(r, at, true), absentMeet(cx, y0 + Y_BOT), chip(top), chip(l), chip(r));
    }
  }
  return out.join("\n");
}

const coeffectAxesSvg = svg(
  2 * MARGIN + 2 * BOX_W + GUTTER,
  2 * MARGIN + 3 * BOX_H + 2 * GUTTER,
  "the six coeffect axes as mini-lattices: Allocation and Mobility as two-point "
    + "chains, Fip meeting at {linear, bounded_stack}, and Multiplicity, "
    + "Aliasing, and Escape as exclusive axes with no meet",
  "A three-row by two-column grid of mini-lattices, one per usage axis, each "
    + "titled with its axis name and a past or future caption. Allocation: (no "
    + "claim) over noalloc, marked as the one checked fact today. Fip: (no claim) "
    + "over linear and bounded_stack, which meet at {linear, bounded_stack}. "
    + "Multiplicity: (no claim) over once and many, no meet. Aliasing: (no claim) "
    + "over unique and aliased, no meet. Escape: (no claim) over local and "
    + "noescape, no meet. Mobility: (no claim) over portable.",
  AXES.map((spec, i) => cell(spec, i)).join("\n"),
);

const files = [
  ["lattice-rows.svg", rowsSvg],
  ["lattice-axes.svg", axesSvg],
  ["lattice-grades.svg", gradesSvg],
  ["lattice-coeffect-axes.svg", coeffectAxesSvg],
];

for (const [name, content] of files) {
  writeFileSync(join(outDir, name), content);
}
console.log(`wrote ${files.length} SVGs to ${outDir}`);
