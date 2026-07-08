# lineage_tiles

A tiny deterministic byte pipeline that pressure-tests run lineage end to end. It reads a JSON config, reads a handful of raw grayscale tiles, computes a pure per-tile summary, writes `summary.json`, and prints a one-line digest. Nothing observes a clock or a random source, so the whole run is a pure function of the committed fixtures: the cold run and its replay agree byte for byte, and changing one tile moves exactly that tile's lineage node plus the outputs that depend on it.

## Files

- `pipeline.pr` - the program.
- `config.json` - the run config: a `threshold` integer and the ordered `tiles` list (tile names without extension).
- `tiles/<name>.gray` - the raw grayscale tiles (see the format below).
- `summary.json`, `run.replay`, `run.plineage` - generated outputs, git-ignored.

## Tile format

Each `tiles/<name>.gray` is a raw byte stream, one byte per grayscale sample in `0..255`, row-major, with no header. Dimensions are not encoded; the pipeline treats a tile as a flat vector of bytes. The committed tiles are 8 bytes each:

| tile         | bytes (decimal)                      |
| ------------ | ------------------------------------ |
| `north.gray` | 16, 32, 48, 64, 96, 128, 160, 200    |
| `south.gray` | 200, 180, 160, 140, 120, 100, 80, 60 |
| `delta.gray` | 0, 255, 0, 255, 0, 255, 0, 255       |

Regenerate them deterministically with:

```sh
printf '\x10\x20\x30\x40\x60\x80\xa0\xc8' > tiles/north.gray
printf '\xc8\xb4\xa0\x8c\x78\x64\x50\x3c' > tiles/south.gray
printf '\x00\xff\x00\xff\x00\xff\x00\xff' > tiles/delta.gray
```

## Per-tile summary

For each tile the pipeline computes, over its bytes:

- `count` - the number of bytes;
- `above` - how many bytes are `>= threshold`;
- `sum` - the sum of the byte values;
- `histogram` - four buckets by `value / 64` (`0..63`, `64..127`, `128..191`, `192..255`).

`summary.json` is the canonical JSON encoding (sorted keys) of the per-tile records plus an aggregate `total`.

## The four verbs

Run these from this directory (the pipeline resolves paths relative to the working directory, falling back to the checked-in location when run from the repo root, so `run --examples` stays green):

```sh
# 1. record a run, emitting a replay trace and a lineage sidecar
prism run pipeline.pr --record run.replay --lineage run.plineage

# 2. explain the written output from the sidecar alone (no source needed)
prism lineage why run.plineage summary.json

# 3. change one tile, re-record, and diff: only that tile plus its downstream move
printf '\x11\x20\x30\x40\x60\x80\xa0\xc8' > tiles/north.gray
prism run pipeline.pr --record run.replay --lineage new.plineage
prism diff run.plineage new.plineage

# 4. verify a run reproduces its recorded trace, stdout, and file digests
prism lineage verify --replay run.plineage
```

Step 3 moves `input-file tiles/north.gray` and its downstream (`trace`, `stdout`, `file-write summary.json`) and leaves `config.json`, `tiles/south.gray`, and `tiles/delta.gray` preserved; `prism diff` exits nonzero so it can gate CI.
