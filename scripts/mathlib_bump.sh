#!/usr/bin/env bash
# Bump the Mathlib pin (and the Lean toolchain it requires) to a Mathlib release,
# rebuild, run every check that CI runs plus the audit scripts, and commit the
# result on a fresh branch. This script never pushes and never opens a PR; the
# GitHub workflow does that, and only when running inside GitHub Actions.
#
# Usage: bash scripts/mathlib_bump.sh [options]
#   --target TAG     Mathlib tag to bump to (default: latest stable vX.Y.Z tag)
#   --branch NAME    branch to create (default: chore/bump-mathlib-TAG)
#   --log-dir DIR    where to write logs (default: .lake/mathlib-bump)
#   --force          run even if the pin already equals the target
#   --no-commit      leave the bump uncommitted on the current branch
#
# Exit status: 0 bumped and verified (or already up to date), 1 a check failed,
# 2 usage or precondition error. Writes KEY=VALUE results to $GITHUB_OUTPUT if set.
set -euo pipefail
cd "$(dirname "$0")/.."

MATHLIB_URL=https://github.com/leanprover-community/mathlib4
MATHLIB_RAW=https://raw.githubusercontent.com/leanprover-community/mathlib4

target=""
branch=""
log_dir=".lake/mathlib-bump"
force=false
commit=true
while [ "$#" -gt 0 ]; do
  case "$1" in
    --target) target="${2:?--target needs a tag}"; shift 2 ;;
    --branch) branch="${2:?--branch needs a name}"; shift 2 ;;
    --log-dir) log_dir="${2:?--log-dir needs a directory}"; shift 2 ;;
    --force) force=true; shift ;;
    --no-commit) commit=false; shift ;;
    -h|--help) sed -n '2,16p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "Unknown option: $1" >&2; exit 2 ;;
  esac
done

mkdir -p "$log_dir"
log_dir=$(cd "$log_dir" && pwd)
summary="$log_dir/summary.txt"
rm -f "$log_dir"/[0-9][0-9]-*.log
: > "$summary"

output() {
  echo "$1=$2" >> "$summary"
  if [ -n "${GITHUB_OUTPUT:-}" ]; then echo "$1=$2" >> "$GITHUB_OUTPUT"; fi
}

# Run one named step, logging its output to $log_dir/NN-name.log.
step_number=0
step() {
  local name="$1"; shift
  step_number=$((step_number + 1))
  local log
  log=$(printf '%s/%02d-%s.log' "$log_dir" "$step_number" "$name")
  last_log="$log"
  echo "==> [$step_number] $name: $*"
  local start=$SECONDS status=0
  "$@" > "$log" 2>&1 || status=$?
  local elapsed=$((SECONDS - start))
  if [ "$status" -eq 0 ]; then
    echo "    ok (${elapsed}s)"
    echo "PASS $name ${elapsed}s" >> "$summary"
  else
    echo "    FAILED with status $status (${elapsed}s); last lines of $log:" >&2
    tail -n 40 "$log" >&2
    echo "FAIL $name ${elapsed}s status=$status" >> "$summary"
    output result failed
    output failed_step "$name"
    exit 1
  fi
}

if ! git diff --quiet || ! git diff --cached --quiet; then
  echo "Working tree has uncommitted changes; commit or stash them first." >&2
  exit 2
fi

latest_release() {
  git ls-remote --tags --refs "$MATHLIB_URL" 'v*' \
    | sed -n 's#.*refs/tags/\(v[0-9][0-9]*\.[0-9][0-9]*\.[0-9][0-9]*\)$#\1#p' \
    | sort -V | tail -n 1
}

current_rev() {
  python3 - <<'EOF'
import tomllib
with open("lakefile.toml", "rb") as f:
    config = tomllib.load(f)
print(next(r["rev"] for r in config["require"] if r["name"] == "mathlib"))
EOF
}

if [ -z "$target" ]; then
  target=$(latest_release)
  [ -n "$target" ] || { echo "Could not determine the latest Mathlib release" >&2; exit 2; }
fi
if ! git ls-remote --exit-code --tags --refs "$MATHLIB_URL" "refs/tags/$target" > /dev/null; then
  echo "Mathlib has no tag $target" >&2
  exit 2
fi
current=$(current_rev)
output current "$current"
output target "$target"
echo "Mathlib pin: $current -> $target"
if [ "$current" = "$target" ] && [ "$force" = false ]; then
  echo "Already on $target; nothing to do."
  output result up-to-date
  exit 0
fi

toolchain=$(curl -fsSL "$MATHLIB_RAW/$target/lean-toolchain" | tr -d '[:space:]')
case "$toolchain" in
  leanprover/lean4:*) ;;
  *) echo "Unexpected toolchain for Mathlib $target: '$toolchain'" >&2; exit 2 ;;
esac
output toolchain "$toolchain"
echo "Lean toolchain: $(cat lean-toolchain) -> $toolchain"

if [ "$commit" = true ]; then
  branch="${branch:-chore/bump-mathlib-$target}"
  if git rev-parse --verify --quiet "refs/heads/$branch" > /dev/null; then
    echo "Branch $branch already exists; delete it or pass --branch." >&2
    exit 2
  fi
  git switch -c "$branch"
  output branch "$branch"
fi

# Rewrite only the rev of the mathlib [[require]] entry; keep the rest verbatim.
set_mathlib_rev() {
  python3 - "$1" <<'EOF'
import re, sys, tomllib
path, rev = "lakefile.toml", sys.argv[1]
text = open(path).read()
blocks = re.split(r"(?m)^(?=\[)", text)
changed = 0
for i, block in enumerate(blocks):
    if block.startswith("[[require]]") and re.search(r'(?m)^name\s*=\s*"mathlib"', block):
        blocks[i], n = re.subn(r'(?m)^rev\s*=\s*"[^"]*"', f'rev = "{rev}"', block)
        changed += n
if changed != 1:
    sys.exit(f"expected one mathlib rev line in {path}, found {changed}")
text = "".join(blocks)
config = tomllib.loads(text)
assert next(r["rev"] for r in config["require"] if r["name"] == "mathlib") == rev
open(path, "w").write(text)
EOF
}

check_pins() {
  local want_rev="$1" want_toolchain="$2"
  python3 - "$want_rev" "$want_toolchain" <<'EOF'
import json, sys
rev, toolchain = sys.argv[1:]
manifest = json.load(open("lake-manifest.json"))
mathlib = next(p for p in manifest["packages"] if p["name"] == "mathlib")
assert mathlib["inputRev"] == rev, ("manifest inputRev", mathlib["inputRev"], rev)
ours = open("lean-toolchain").read().strip()
theirs = open(".lake/packages/mathlib/lean-toolchain").read().strip()
assert ours == theirs == toolchain, (ours, theirs, toolchain)
print(f"mathlib {rev} @ {mathlib['rev']}; toolchain {toolchain}")
EOF
}

# Snapshot counts from a lake build log, using the repo's own warning counter.
warning_counts() {
  node -e '
    const fs = require("node:fs");
    const { countWarnings } = require("./scripts/warning-counts.cjs");
    const counts = countWarnings(fs.readFileSync(process.argv[1], "utf8"));
    const total = Object.values(counts).reduce((a, b) => a + b, 0);
    console.log(JSON.stringify({ total, counts }, null, 2));
  ' "$1"
}

# Steps run inside `||`, where errexit is off, so multi-command steps chain with &&.
set_pins() { set_mathlib_rev "$target" && echo "$toolchain" > lean-toolchain && git diff; }
install_toolchain() {
  if elan toolchain list | awk '{print $1}' | grep -qxF "$toolchain"; then
    echo "$toolchain already installed"
  else
    elan toolchain install "$toolchain"
  fi
}

step set-pins set_pins
step elan-toolchain install_toolchain
step lake-update lake update mathlib
step check-pins check_pins "$target" "$toolchain"
step cache-get lake exe cache get

# The checks below mirror .github/workflows/lean_action_ci.yaml, in order.
step check-headers bash scripts/check-headers.sh
step test-update-imports python3 scripts/tests/test_update_imports.py
step test-warning-counts node --test scripts/tests/test_warning_counts.cjs
step check-imports bash scripts/update-imports.sh --check
step lake-build lake --rehash --no-ansi build
build_log="$last_log"
step test-proof-integrity python3 scripts/tests/test_proof_integrity.py
step proof-integrity python3 scripts/check-proof-integrity.py --report "$log_dir/proof-integrity-report.json"
step warning-counts warning_counts "$build_log"
# Audit scripts that are not part of CI.
step bic-regressions python3 scripts/check-bic-regressions.py
step bic-contract python3 scripts/tests/check_bic_contract.py

if [ "$commit" = true ]; then
  git add lean-toolchain lakefile.toml lake-manifest.json
  git commit -q -F - <<EOF
chore: bump Mathlib to $target

Mathlib $current -> $target, Lean toolchain $toolchain.
Generated by scripts/mathlib_bump.sh; lake build, the Lean Action CI checks,
the proof-integrity (axiom) audit, and the BIC audits passed locally.
EOF
  output commit "$(git rev-parse HEAD)"
  echo "Committed $(git rev-parse --short HEAD) on $branch."
fi
output result bumped
echo "Logs: $log_dir"
