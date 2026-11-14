#!/usr/bin/env bash
# Check that every Lean declaration named in the blueprint exists in MathEconLib.
# Uses blueprint/lean_decls (written by `leanblueprint web`) when present, and
# otherwise collects the \lean{...} commands from the blueprint sources.
set -euo pipefail
cd "$(dirname "$0")/.."

if [[ -s blueprint/lean_decls ]]; then
  names=$(cat blueprint/lean_decls)
else
  names=$(grep -rhoE "\\\\lean\\{[^}]*\\}" blueprint/src | sed -E "s/^\\\\lean\\{//; s/\\}$//" | tr "," "\n")
fi

tmpdir=$(mktemp -d)
trap "rm -rf \"$tmpdir\"" EXIT
check_file="$tmpdir/CheckBlueprintDecls.lean"
count=0
{
  echo "import MathEconLib"
  while IFS= read -r name; do
    name=$(echo "$name" | tr -d "[:space:]")
    if [[ -n "$name" ]]; then
      echo "#check @$name"
      count=$((count + 1))
    fi
  done <<< "$names"
} > "$check_file"

if ! output=$(lake env lean "$check_file" 2>&1); then
  echo "$output" | grep -E "error" || echo "$output"
  echo "Some blueprint declarations do not exist."
  exit 1
fi
echo "All $count blueprint declarations exist."
