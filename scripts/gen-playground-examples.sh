#!/usr/bin/env bash
# Bake examples/*.pr into web/src/examples.ts so the static playground can
# offer them without a server.
set -euo pipefail
cd "$(dirname "$0")/.."

python3 - > web/src/examples.ts <<'PY'
import glob, json, os

examples = {}
for path in sorted(glob.glob("examples/*.pr")):
    name = os.path.splitext(os.path.basename(path))[0]
    with open(path, encoding="utf-8") as f:
        examples[name] = f.read()

body = json.dumps(examples, ensure_ascii=False, indent=2)
print("export const examples: Record<string, string> = " + body + ";")
PY

echo "wrote web/src/examples.ts ($(ls examples/*.pr | wc -l | tr -d ' ') examples)"
