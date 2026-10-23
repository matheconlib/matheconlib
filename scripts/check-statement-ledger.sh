#!/usr/bin/env bash
# Check that StatementLedger.txt matches the statements of the built library.
# Regenerate it with: lake build MathEconLib && lake exe statement_ledger
set -euo pipefail
cd "$(dirname "$0")/.."

ledger=StatementLedger.txt
fresh=$(mktemp)
trap 'rm -f "$fresh"' EXIT

lake build MathEconLib
lake exe statement_ledger --output "$fresh"
if ! diff -u --label "$ledger (committed)" --label "$ledger (regenerated)" "$ledger" "$fresh"; then
  echo "::error file=$ledger::$ledger is out of date. Run locally: lake build MathEconLib && lake exe statement_ledger, then commit $ledger."
  exit 1
fi
echo "$ledger is up to date."
