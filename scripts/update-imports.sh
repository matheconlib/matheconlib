#!/usr/bin/env bash
set -euo pipefail

# Run from the repository root. With one --lib, mk_all returns 0 for no change
# and 1 for one updated/created file. An error can also return 1, so require an
# actual change before accepting it, then verify both lists with --check.
case "${1:-}" in
  "") check_only=false ;;
  --check) check_only=true ;;
  *) echo "Usage: bash scripts/update-imports.sh [--check]" >&2; exit 2 ;;
esac
if [ "$#" -gt 1 ]; then
  echo "Usage: bash scripts/update-imports.sh [--check]" >&2
  exit 2
fi

if [ "$check_only" = false ]; then
  for lib in Auctionlib AuctionlibTest; do
    before=missing
    if [ -f "$lib.lean" ]; then
      before=$(git hash-object "$lib.lean")
    fi
    status=0
    lake exe mk_all --lib "$lib" --git || status=$?
    case "$status" in
      0) ;;
      1)
        if [ ! -f "$lib.lean" ] || [ "$(git hash-object "$lib.lean")" = "$before" ]; then
          echo "mk_all failed for $lib without updating $lib.lean" >&2
          exit 1
        fi
        ;;
      *) exit "$status" ;;
    esac
  done
fi

for lib in Auctionlib AuctionlibTest; do
  lake exe mk_all --lib "$lib" --git --check
done
