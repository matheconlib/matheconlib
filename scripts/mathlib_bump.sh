#!/usr/bin/env bash
# Bump the Mathlib pin (and the Lean toolchain it requires) to a stable Mathlib
# release, rebuild, run every check that CI runs plus the audit scripts, and
# commit the result on a fresh branch. This script never pushes and never opens
# a PR; in GitHub Actions, scripts/mathlib_bump_publish.sh does that.
#
# Usage: bash scripts/mathlib_bump.sh [options]
#   --target TAG      stable Mathlib tag vX.Y.Z (default: the latest one); it must
#                     be newer than the current pin, or equal to it with --probe
#   --branch NAME     branch to create (default: chore/bump-mathlib-TAG)
#   --log-dir DIR     where to write logs and evidence (default: .lake/mathlib-bump)
#   --probe           compatibility probe: run every check against the target,
#                     even if it equals the pin; never creates a branch or commit
#   --allow-unstable  with --probe only: also accept an RC or an older tag
#   --no-commit       leave the bump uncommitted on the current branch
#
# Results go to summary.txt in the log dir, and to $GITHUB_OUTPUT if set:
#   result=up-to-date     the pin equals the target and the pins are consistent;
#                         this is release discovery, not compatibility evidence
#   result=branch-exists  origin already has the bump branch; nothing was run
#   result=bumped         every check passed; committed unless --no-commit
#   result=compatible     --probe and every check passed
#   result=failed         failed_step names the failed step. If the pins had been
#                         changed on the bump branch, the partial bump is committed
#                         with an "(unverified)" subject so it can become a draft PR.
# The log dir also keeps the step logs, lake-manifest.json, warning-counts.json,
# proof-integrity-report.json and, after a commit, bump.bundle.
# Exit status: 0 unless result=failed (1), or a usage or precondition error (2).
set -euo pipefail
cd "$(dirname "$0")/.."

MATHLIB_URL=${MATHLIB_URL:-https://github.com/leanprover-community/mathlib4}
MATHLIB_RAW=https://raw.githubusercontent.com/leanprover-community/mathlib4
MATHLIB_API=https://api.github.com/repos/leanprover-community/mathlib4
STABLE='^v[0-9]+\.[0-9]+\.[0-9]+$'
# The steps run after discovery, in order.
STEPS="set-pins elan-toolchain lake-update check-pins cache-get check-headers
test-update-imports test-warning-counts check-imports lake-build
test-proof-integrity proof-integrity bic-regressions bic-contract"

target=""
branch=""
log_dir=".lake/mathlib-bump"
probe=false
allow_unstable=false
commit=true
while [ "$#" -gt 0 ]; do
  case "$1" in
    --target) target="${2:?--target needs a tag}"; shift 2 ;;
    --branch) branch="${2:?--branch needs a name}"; shift 2 ;;
    --log-dir) log_dir="${2:?--log-dir needs a directory}"; shift 2 ;;
    --probe) probe=true; commit=false; shift ;;
    --allow-unstable) allow_unstable=true; shift ;;
    --no-commit) commit=false; shift ;;
    -h|--help) sed -n '2,30p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "Unknown option: $1" >&2; exit 2 ;;
  esac
done
if [ "$allow_unstable" = true ] && [ "$probe" = false ]; then
  echo "--allow-unstable is only accepted with --probe" >&2
  exit 2
fi

mkdir -p "$log_dir"
log_dir=$(cd "$log_dir" && pwd)
summary="$log_dir/summary.txt"
rm -f "$log_dir"/[0-9][0-9]-*.log "$log_dir"/warning-counts.json \
  "$log_dir"/proof-integrity-report.json "$log_dir"/lake-manifest.json "$log_dir"/bump.bundle
: > "$summary"

output() {
  echo "$1=$2" >> "$summary"
  if [ -n "${GITHUB_OUTPUT:-}" ]; then echo "$1=$2" >> "$GITHUB_OUTPUT"; fi
}

result=""
phase=preflight
passed=""
branch_created=false
current="" target_sha="" toolchain=""

# Record a failure and exit. Steps not yet run are listed as remaining work.
fail() {
  local name="$1" message="$2" code="${3:-1}" remaining
  echo "$message" >&2
  echo "FAIL $name: $message" >> "$summary"
  remaining=$(echo $STEPS | tr ' ' '\n' | sed "1,/^$name\$/d" | tr '\n' ' ')
  if ! echo $STEPS | tr ' ' '\n' | grep -qxF "$name"; then remaining=$(echo $STEPS); fi
  result=failed
  output result failed
  output failed_step "$name"
  output passed_steps "${passed:-none}"
  output remaining_steps "${remaining% }"
  exit "$code"
}

# Run one named step, logging its output to $log_dir/NN-name.log.
step_number=0
step() {
  local name="$1"; shift
  phase="$name"
  step_number=$((step_number + 1))
  local log
  log=$(printf '%s/%02d-%s.log' "$log_dir" "$step_number" "$name")
  echo "==> [$step_number] $name: $*"
  local start=$SECONDS status=0
  "$@" > "$log" 2>&1 || status=$?
  local elapsed=$((SECONDS - start))
  if [ "$status" -eq 0 ]; then
    echo "    ok (${elapsed}s)"
    echo "PASS $name ${elapsed}s" >> "$summary"
    passed="${passed:+$passed }$name"
  else
    echo "    FAILED with status $status (${elapsed}s); last lines of $log:" >&2
    tail -n 40 "$log" >&2
    fail "$name" "step $name failed with status $status after ${elapsed}s; see $(basename "$log")"
  fi
}

# Snapshot warning counts from a lake build log, using the repo's own counter.
record_warnings() {
  local total
  if total=$(node -e '
    const fs = require("node:fs");
    const { countWarnings } = require("./scripts/warning-counts.cjs");
    const counts = countWarnings(fs.readFileSync(process.argv[1], "utf8"));
    const total = Object.values(counts).reduce((a, b) => a + b, 0);
    fs.writeFileSync(process.argv[2], JSON.stringify({ total, counts }, null, 2) + "\n");
    console.log(total);
  ' "$1" "$log_dir/warning-counts.json"); then
    output warnings_total "$total"
  else
    output warnings_total unavailable
  fi
}

record_commit() {
  output commit "$(git rev-parse HEAD)"
  git bundle create -q "$log_dir/bump.bundle" "refs/heads/$branch" "^$base"
  echo "Committed $(git rev-parse --short HEAD) on $branch."
}

# Commit a partial bump so that adaptations can continue on a draft PR. The
# subject says it is unverified; the body says where it stopped.
commit_partial() {
  git add lean-toolchain lakefile.toml lake-manifest.json
  if git diff --cached --quiet; then return 0; fi
  git commit -q -F - <<EOF
chore: bump Mathlib to $target (unverified)

Mathlib $current -> $target ($target_sha),
Lean toolchain $toolchain.
NOT verified: scripts/mathlib_bump.sh stopped at the failed step
$(sed -n 's/^failed_step=//p' "$summary").

Passed: $(sed -n 's/^passed_steps=//p' "$summary").

Not run: $(sed -n 's/^remaining_steps=//p' "$summary").
EOF
  record_commit
}

# Keep the evidence on every exit path.
finish() {
  local status=$?
  set +e
  trap - EXIT
  if [ -z "$result" ] && [ "$status" -ne 0 ]; then
    echo "FAIL $phase: unexpected exit status $status" >> "$summary"
    result=failed
    output result failed
    output failed_step "$phase"
  fi
  local build_log
  build_log=$(ls "$log_dir"/[0-9][0-9]-lake-build.log 2> /dev/null | head -n 1)
  if [ -n "$build_log" ] && [ ! -f "$log_dir/warning-counts.json" ]; then
    record_warnings "$build_log"
  fi
  if [ -f lake-manifest.json ]; then cp lake-manifest.json "$log_dir/lake-manifest.json"; fi
  if [ "$result" = failed ] && [ "$branch_created" = true ]; then commit_partial; fi
  echo "Result: ${result:-none}. Logs and evidence: $log_dir"
  exit "$status"
}
trap finish EXIT

if ! git diff --quiet || ! git diff --cached --quiet; then
  fail preflight "Working tree has uncommitted changes; commit or stash them first." 2
fi
base=$(git rev-parse HEAD)
output base "$base"

current_rev() {
  python3 - <<'EOF'
import tomllib
with open("lakefile.toml", "rb") as f:
    config = tomllib.load(f)
print(next(r["rev"] for r in config["require"] if r["name"] == "mathlib"))
EOF
}

# version_lt A B: A sorts strictly before B as a version.
version_lt() {
  [ "$1" != "$2" ] && [ "$(printf '%s\n%s\n' "$1" "$2" | sort -V | head -n 1)" = "$1" ]
}

phase=discover
tags=$(git ls-remote --tags "$MATHLIB_URL") || fail discover "Cannot list the tags of $MATHLIB_URL"
stable=$(printf '%s\n' "$tags" | sed -n 's#^.*[[:space:]]refs/tags/##p' \
  | { grep -E "$STABLE" || true; } | sort -V)
[ -n "$stable" ] || fail discover "No stable vX.Y.Z tags at $MATHLIB_URL"
latest=$(printf '%s\n' "$stable" | tail -n 1)
target="${target:-$latest}"
current=$(current_rev)
output current "$current"
output target "$target"
output latest_stable "$latest"
echo "Mathlib pin: $current -> $target (latest stable: $latest)"

phase=select-target
target_sha=$(printf '%s\n' "$tags" | awk -v t="refs/tags/$target" \
  '$2 == t "^{}" { peeled = $1 } $2 == t { plain = $1 } END { print peeled ? peeled : plain }')
[ -n "$target_sha" ] || fail select-target "Mathlib has no tag $target"
output target_sha "$target_sha"
if [ "$allow_unstable" = false ]; then
  [[ $target =~ $STABLE ]] \
    || fail select-target "$target is not a stable vX.Y.Z release; RCs and other tags need --probe --allow-unstable"
  [[ $current =~ $STABLE ]] \
    || fail select-target "The current pin $current is not a stable vX.Y.Z release"
  if version_lt "$target" "$current"; then
    fail select-target "$target is older than the current pin $current"
  fi
fi
skipped=""
while read -r tag; do
  if version_lt "$current" "$tag" && version_lt "$tag" "$target"; then skipped="$skipped $tag"; fi
done <<< "$stable"
skipped="${skipped# }"
output skipped_releases "${skipped:-none}"

phase=discover
toolchain=$(curl -fsSL "$MATHLIB_RAW/$target_sha/lean-toolchain" | tr -d '[:space:]') \
  || fail discover "Cannot read lean-toolchain of Mathlib $target ($target_sha)"
case "$toolchain" in
  leanprover/lean4:*) ;;
  *) fail discover "Unexpected toolchain for Mathlib $target: '$toolchain'" ;;
esac
output toolchain "$toolchain"
release_date=$(curl -fsSL "$MATHLIB_API/releases/tags/$target" \
  | python3 -c 'import json, sys; print(json.load(sys.stdin)["published_at"])' 2> /dev/null) \
  || release_date=unknown
output release_date "$release_date"
echo "Mathlib $target is $target_sha, released $release_date; Lean toolchain: $(cat lean-toolchain) -> $toolchain"
[ -z "$skipped" ] || echo "Stable releases between the pins, not ported separately: $skipped"

# check_pins REV SHA TOOLCHAIN [package]: the lakefile, manifest and toolchain
# agree with Mathlib REV at commit SHA; with "package", so does Lake's checkout.
check_pins() {
  python3 - "$@" <<'EOF'
import json, sys, tomllib
rev, sha, toolchain = sys.argv[1:4]
package = sys.argv[4:] == ["package"]
errors = []
with open("lakefile.toml", "rb") as f:
    lake_rev = next(r["rev"] for r in tomllib.load(f)["require"] if r["name"] == "mathlib")
mathlib = next(p for p in json.load(open("lake-manifest.json"))["packages"] if p["name"] == "mathlib")
ours = open("lean-toolchain").read().strip()
if lake_rev != rev:
    errors.append(f"lakefile.toml requires mathlib rev {lake_rev}, expected {rev}")
if mathlib.get("inputRev") != rev:
    errors.append(f"lake-manifest.json mathlib inputRev is {mathlib.get('inputRev')}, expected {rev}")
if mathlib.get("rev") != sha:
    errors.append(f"lake-manifest.json resolves mathlib to {mathlib.get('rev')}, but {rev} is {sha}")
if ours != toolchain:
    errors.append(f"lean-toolchain is {ours}, but Mathlib {rev} requires {toolchain}")
if package:
    theirs = open(".lake/packages/mathlib/lean-toolchain").read().strip()
    if theirs != toolchain:
        errors.append(f".lake/packages/mathlib/lean-toolchain is {theirs}, expected {toolchain}")
for error in errors:
    print(error)
if errors:
    sys.exit(1)
print(f"mathlib {rev} @ {sha}; toolchain {toolchain}")
EOF
}

if [ "$current" = "$target" ] && [ "$probe" = false ]; then
  # Release discovery found nothing new. Still check that the pins agree with
  # the release; this is not a compatibility test (use --probe for that).
  step check-pins check_pins "$target" "$target_sha" "$toolchain"
  echo "Already on $target and the pins are consistent; nothing to do."
  result=up-to-date
  output result up-to-date
  exit 0
fi

if [ "$commit" = true ]; then
  phase=preflight
  branch="${branch:-chore/bump-mathlib-$target}"
  output branch "$branch"
  if git remote get-url origin > /dev/null 2>&1; then
    status=0
    GIT_TERMINAL_PROMPT=0 git ls-remote --exit-code --heads origin "refs/heads/$branch" > /dev/null \
      || status=$?
    case "$status" in
      0)
        echo "origin already has $branch; leaving it and any adaptations on it alone."
        result=branch-exists
        output result branch-exists
        exit 0 ;;
      2) ;;
      *) fail discover "Cannot query origin for $branch (git ls-remote status $status)" ;;
    esac
  fi
  if git rev-parse --verify --quiet "refs/heads/$branch" > /dev/null; then
    fail preflight "Branch $branch already exists locally; delete it or pass --branch." 2
  fi
  git switch -q -c "$branch"
  branch_created=true
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
step check-pins check_pins "$target" "$target_sha" "$toolchain" package
step cache-get lake exe cache get

# The checks below mirror .github/workflows/lean_action_ci.yaml, in order.
step check-headers bash scripts/check-headers.sh
step test-update-imports python3 scripts/tests/test_update_imports.py
step test-warning-counts node --test scripts/tests/test_warning_counts.cjs
step check-imports bash scripts/update-imports.sh --check
step lake-build lake --rehash --no-ansi build
record_warnings "$log_dir/$(printf '%02d' "$step_number")-lake-build.log"
step test-proof-integrity python3 scripts/tests/test_proof_integrity.py
step proof-integrity python3 scripts/check-proof-integrity.py --report "$log_dir/proof-integrity-report.json"
# Audit scripts that are not part of CI.
step bic-regressions python3 scripts/check-bic-regressions.py
step bic-contract python3 scripts/tests/check_bic_contract.py

phase=commit
if [ "$commit" = true ]; then
  git add lean-toolchain lakefile.toml lake-manifest.json
  git commit -q -F - <<EOF
chore: bump Mathlib to $target

Mathlib $current -> $target ($target_sha, released $release_date),
Lean toolchain $toolchain.
Stable releases between the pins, not ported separately: ${skipped:-none}.
Generated by scripts/mathlib_bump.sh; these steps passed on the bumped pins:
$passed.
Project warnings in the build log: $(sed -n 's/^warnings_total=//p' "$summary").
EOF
  record_commit
fi
if [ "$probe" = true ]; then result=compatible; else result=bumped; fi
output passed_steps "$passed"
output result "$result"
