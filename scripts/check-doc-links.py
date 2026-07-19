#!/usr/bin/env python3
"""Fail if any internal link, anchor, or {{#include}} in docs/src is broken.

Checks, for every Markdown file under docs/src:
  - [text](#anchor)          same-file anchor, must match a heading {#anchor}
                              or <a id="anchor"> in this file
  - [text](path.md)          relative path, must exist on disk
  - [text](path.md#anchor)   both of the above, on the target file
  - {{#include path}}        mdbook include, path must exist on disk
  - {{#include path:tag}}    tag is a line range (N, N:, :N, N:M) or an
                              ANCHOR: tag / ANCHOR_END: tag region, either
                              of which must be present in the target file

External links (http://, https://, mailto:) are not checked.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DOCS_SRC = ROOT / "docs" / "src"

HEADING_ANCHOR_RE = re.compile(r"^#{1,6}\s+.*\{#([A-Za-z0-9_-]+)\}\s*$")
HTML_ANCHOR_RE = re.compile(r'<a\s+id="([A-Za-z0-9_-]+)"')
LINK_RE = re.compile(r"\[[^\]]*\]\(([^)\s]+)(?:\s+\"[^\"]*\")?\)")
INCLUDE_RE = re.compile(r"\{\{#include\s+([^}\s]+)\s*\}\}")
EXTERNAL_RE = re.compile(r"^(https?|mailto|ftp)://|^mailto:")
# Targets the site build (docs/scripts/build-site.sh) generates into the output
# tree rather than committing under docs/src, so a link to them resolves on the
# deployed site but never exists on disk here.
GENERATED_TARGETS = {"semantics.pdf"}
ANCHOR_TAG_RE_TEMPLATE = r"ANCHOR(?:_END)?:\s*{}\b"

anchor_cache = {}
errors = []


def fence_masked_lines(text):
    """Lines with fenced code blocks blanked out, since example text inside a
    fence is not a real link. {{#include}} directives are legitimately fenced
    (mdbook syntax-highlights the included file), so callers must scan the
    raw lines separately for those."""
    out = []
    in_fence = False
    for line in text.splitlines():
        if line.strip().startswith("```"):
            in_fence = not in_fence
            out.append("")
            continue
        out.append("" if in_fence else line)
    return out


def mask_inline_code(line):
    """Blank out inline code spans (backtick-delimited), preserving length so
    link-like text inside them is not parsed as a Markdown link. Markdown never
    renders `[x](y)` inside a code span as a link, so a format string such as
    `YYYY-MM-DDTHH:MM:SS[.frac](Z|(+|-)HH:MM)` is not a broken link. CommonMark:
    an opening run of n backticks is closed by the next run of exactly n."""
    out = []
    i, n = 0, len(line)
    while i < n:
        if line[i] != "`":
            out.append(line[i])
            i += 1
            continue
        j = i
        while j < n and line[j] == "`":
            j += 1
        run = j - i
        k, closed = j, False
        while k < n:
            if line[k] == "`":
                p = k
                while p < n and line[p] == "`":
                    p += 1
                if p - k == run:
                    out.append(" " * (p - i))
                    i, closed = p, True
                    break
                k = p
            else:
                k += 1
        if not closed:
            out.append(line[i:j])
            i = j
    return "".join(out)


def anchors_of(path):
    if path not in anchor_cache:
        anchors = set()
        if path.is_file() and path.suffix == ".md":
            for line in path.read_text().splitlines():
                m = HEADING_ANCHOR_RE.match(line)
                if m:
                    anchors.add(m.group(1))
                for m in HTML_ANCHOR_RE.finditer(line):
                    anchors.add(m.group(1))
        anchor_cache[path] = anchors
    return anchor_cache[path]


def check_link(src_file, lineno, target):
    if EXTERNAL_RE.match(target):
        return
    path_part, _, anchor_part = target.partition("#")
    if path_part and Path(path_part).name in GENERATED_TARGETS:
        return

    if path_part == "":
        target_path = src_file
    else:
        target_path = (src_file.parent / path_part).resolve()
        if not target_path.exists():
            errors.append(f"{src_file}:{lineno}: broken link, no such file: {path_part}")
            return

    if anchor_part and target_path.suffix == ".md":
        if anchor_part not in anchors_of(target_path):
            errors.append(
                f"{src_file}:{lineno}: broken anchor '#{anchor_part}' in {target_path.relative_to(ROOT)}"
            )


def check_include(src_file, lineno, spec):
    parts = spec.split(":")
    file_part = parts[0]
    target_path = (src_file.parent / file_part).resolve()
    if not target_path.exists():
        errors.append(f"{src_file}:{lineno}: broken include, no such file: {file_part}")
        return
    if len(parts) == 1:
        return
    tag_parts = parts[1:]
    if all(p == "" or p.isdigit() for p in tag_parts):
        return  # line range, e.g. path:10:20, path:10:, path::20
    tag = tag_parts[0]
    body = target_path.read_text()
    if not re.search(ANCHOR_TAG_RE_TEMPLATE.format(re.escape(tag)), body):
        errors.append(f"{src_file}:{lineno}: include tag '{tag}' not found in {file_part}")


def main():
    if not DOCS_SRC.is_dir():
        sys.exit(f"no such directory: {DOCS_SRC}")

    for md_file in sorted(DOCS_SRC.rglob("*.md")):
        text = md_file.read_text()
        raw_lines = text.splitlines()
        masked_lines = fence_masked_lines(text)
        for lineno, (raw, masked) in enumerate(zip(raw_lines, masked_lines), start=1):
            for m in LINK_RE.finditer(mask_inline_code(masked)):
                check_link(md_file, lineno, m.group(1))
            for m in INCLUDE_RE.finditer(raw):
                check_include(md_file, lineno, m.group(1))

    if errors:
        print(f"found {len(errors)} broken internal link(s):", file=sys.stderr)
        for e in errors:
            print(f"  {e}", file=sys.stderr)
        sys.exit(1)

    print("all internal doc links resolve")


if __name__ == "__main__":
    main()
