#!/usr/bin/env bash
set -euo pipefail

# Run from the repository root.
case "$#:${1:-}" in
  0:) ;;
  1:--check)
    python3 "$(dirname "$0")/update-core-imports.py" --check
    lake exe mk_all --lib MathEconLibTest --git --check
    exit
    ;;
  *)
    echo "Usage: bash scripts/update-imports.sh [--check]" >&2
    exit 2
    ;;
esac

python3 "$(dirname "$0")/update-core-imports.py"

# With one --lib, mk_all returns 1 both for a change and for an error.
# Accept that status only when the output changed, then verify the result.
before=missing
if [ -f MathEconLibTest.lean ]; then
  before=$(git hash-object --no-filters MathEconLibTest.lean)
fi
status=0
lake exe mk_all --lib MathEconLibTest --git || status=$?
case "$status" in
  0) ;;
  1)
    if [ ! -f MathEconLibTest.lean ] ||
        [ "$(git hash-object --no-filters MathEconLibTest.lean)" = "$before" ]; then
      echo "mk_all failed without updating MathEconLibTest.lean" >&2
      exit 1
    fi
    ;;
  *) exit "$status" ;;
esac

python3 "$(dirname "$0")/update-core-imports.py" --check
lake exe mk_all --lib MathEconLibTest --git --check
