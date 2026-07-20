#!/usr/bin/env bash
# Set up a Prism working clone: the two remotes (public release target + private
# scratchpad) and the plans repo checked out under plans/.
set -euo pipefail

PUBLIC=git@github.com:sdiehl/prism.git
PRIVATE=git@github.com:sdiehl/prism-private.git
PLANS=git@github.com:sdiehl/prism-plans.git

remote() { # name url: force `name` to point at `url`, adding it if absent
  if git remote get-url "$1" >/dev/null 2>&1; then
    git remote set-url "$1" "$2"
  else
    git remote add "$1" "$2"
  fi
}

remote origin "$PUBLIC"
remote private "$PRIVATE"

if [ -d plans/.git ]; then
  git -C plans pull --ff-only origin main
else
  git clone "$PLANS" plans
fi
