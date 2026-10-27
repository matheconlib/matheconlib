#!/usr/bin/env bash
# Report whether two commits differ in anything that affects generated API
# documentation: library Lean sources, the toolchain and dependency pins, and
# the documentation tooling. Exit 0 when they differ, 1 when they match, and 2
# when a commit is invalid or cannot be fetched.
set -uo pipefail

if [[ $# != 2 ]]; then
  echo "Usage: bash scripts/docs-inputs-changed.sh FROM TO" >&2
  exit 2
fi
for revision in "$1" "$2"; do
  if [[ ! $revision =~ ^[0-9a-f]{40}$ || $revision =~ ^0+$ ]]; then
    echo "Not a commit: $revision" >&2
    exit 2
  fi
  # CI checkouts are shallow, but comparing trees needs no history.
  git cat-file -e "$revision^{commit}" 2>/dev/null \
    || git fetch -q --depth=1 origin "$revision" || exit 2
done
git diff --quiet "$1" "$2" -- \
  MathEconLib.lean ':(glob)MathEconLib/**/*.lean' lean-toolchain lake-manifest.json lakefile.toml \
  scripts/build_docs.py scripts/extract_signatures.py scripts/upload-docs.sh \
  scripts/docs-inputs-changed.sh .github/workflows/lean_action_ci.yaml
case $? in
  0) exit 1 ;;
  1) exit 0 ;;
  *) exit 2 ;;
esac
