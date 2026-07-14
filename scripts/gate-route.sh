#!/bin/sh
# Map changed files to the just gate targets that must run. Each path class
# selects a superset of the gates it can affect, and any unknown path
# escalates to the full authoritative gate, so routing can only over-run.
#
# Usage: gate-route.sh [--print] [--diff REF] [PATH...]
#   PATH...     route these paths as-is (for exercising the table directly)
#   --diff REF  route `git diff --name-only REF` plus untracked files
#   --print     print the selected just targets, one per line, without running
# With no PATHs and no --diff, defaults to --diff HEAD.

set -eu

print_only=0
ref=""
paths=""

while [ $# -gt 0 ]; do
    case "$1" in
        --print)
            print_only=1
            ;;
        --diff)
            shift
            if [ $# -eq 0 ]; then
                echo "gate-route: --diff needs a ref" >&2
                exit 2
            fi
            ref="$1"
            ;;
        -h|--help)
            echo "usage: gate-route.sh [--print] [--diff REF] [PATH...]"
            exit 0
            ;;
        *)
            paths="$paths$1
"
            ;;
    esac
    shift
done

if [ -z "$paths" ] && [ -z "$ref" ]; then
    ref=HEAD
fi
if [ -n "$ref" ]; then
    paths="$paths$(git diff --name-only "$ref" --)
$(git ls-files --others --exclude-standard)
"
fi

# Path classes, most demanding first. Anything compiled into the compiler or
# feeding an oracle corpus is `full`: for those changes every native gate is
# affected, and only `just gate` is a superset of that. Unknown paths fall
# through to `full` on purpose.
full=0
docs=0
tooling=0
n=0

classify() {
    case "$1" in
        src/*|bin/*|lib/*|runtime/*|tests/*|examples/*|*.pr|Cargo.toml|Cargo.lock|build.rs|justfile)
            full=1
            ;;
        docs/*|web/*|*.md)
            docs=1
            ;;
        scripts/*|.github/*|packaging/*|syntax/*|.gitignore|LICENSE*)
            tooling=1
            ;;
        *)
            full=1
            ;;
    esac
}

old_ifs=$IFS
IFS='
'
for p in $paths; do
    if [ -n "$p" ]; then
        classify "$p"
        n=$((n + 1))
    fi
done
IFS=$old_ifs

if [ "$n" -eq 0 ]; then
    echo "gate-route: no changed files; nothing to run"
    exit 0
fi

# Union of the selected classes. `gate-dev` already runs fmt-check, and the
# full gate subsumes every dev gate, so only the extras remain alongside it.
if [ "$full" -eq 1 ]; then
    targets="fmt-check fmt-examples gate"
elif [ "$tooling" -eq 1 ] && [ "$docs" -eq 1 ]; then
    targets="gate-dev fmt-examples"
elif [ "$tooling" -eq 1 ]; then
    targets="gate-dev"
else
    targets="fmt-check fmt-examples"
fi

echo "gate-route: $n path(s) -> $targets" >&2
if [ "$print_only" -eq 1 ]; then
    for t in $targets; do
        echo "$t"
    done
    exit 0
fi
for t in $targets; do
    echo "gate-route: running just $t" >&2
    just "$t"
done
