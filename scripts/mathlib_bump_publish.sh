#!/usr/bin/env bash
# Publish the result of scripts/mathlib_bump.sh from GitHub Actions:
#   bumped         push the bump branch and open its PR
#   failed         with a bump commit: push it and open a draft PR that names the
#                  failed step; otherwise (discovery or setup failures) comment on
#                  the tracking issue
#   branch-exists  recover: reuse the open PR, or open the missing one (a push that
#                  succeeded before `gh pr create` failed); report merge conflicts
#                  with main and PRs closed without merging on the tracking issue
#   up-to-date, compatible: nothing to publish
# It never force-pushes and never rewrites an existing branch, so adaptations
# pushed to a bump branch are kept. Its own errors go to the tracking issue too.
#
# Usage: bash scripts/mathlib_bump_publish.sh LOG_DIR
#   LOG_DIR holds summary.txt, the step logs and bump.bundle from the bump job;
#   a missing or empty summary is reported as a setup failure. The bump job runs
#   generated code, so its branch name and commit are checked before any push:
#   the branch must be chore/bump-mathlib-vX.Y.Z for the recorded stable target,
#   and the commit a single child of a main commit changing only the pin files.
# Environment: GH_TOKEN; GITHUB_SERVER_URL, GITHUB_REPOSITORY and GITHUB_RUN_ID
# for the run link; BUMP_JOB_RESULT, the bump job's result; MATHLIB_BUMP_OWNER,
# the GitHub login responsible for followup (optional).
# Outside GitHub Actions (or under act) it does nothing, so local runs never push.
set -euo pipefail
cd "$(dirname "$0")/.."

ISSUE_TITLE="Mathlib bump automation: failure reports"
BOT_EMAIL="github-actions[bot]@users.noreply.github.com"

log_dir="${1:?usage: mathlib_bump_publish.sh LOG_DIR}"
if [ "${GITHUB_ACTIONS:-}" != "true" ] || [ -n "${ACT:-}" ]; then
  echo "Not running on GitHub Actions; not pushing or opening anything."
  exit 0
fi

get() {
  if [ -f "$log_dir/summary.txt" ]; then sed -n "s/^$1=//p" "$log_dir/summary.txt" | tail -n 1; fi
}
result=$(get result)
failed_step=$(get failed_step)
target=$(get target)
branch=$(get branch)
commit=$(get commit)
run_url="${GITHUB_SERVER_URL:-https://github.com}/${GITHUB_REPOSITORY:-}/actions/runs/${GITHUB_RUN_ID:-}"
owner="unassigned (see #233)"
if [ -n "${MATHLIB_BUMP_OWNER:-}" ]; then owner="@$MATHLIB_BUMP_OWNER"; fi
if [ -z "$result" ]; then
  result=failed
  failed_step="setup: the bump job ended (${BUMP_JOB_RESULT:-unknown}) before scripts/mathlib_bump.sh recorded a result"
fi

note() {
  echo "$1"
  if [ -n "${GITHUB_STEP_SUMMARY:-}" ]; then echo "$1" >> "$GITHUB_STEP_SUMMARY"; fi
}

evidence() {
  cat <<EOF
- Target: \`${target:-unknown}\`, Mathlib commit \`$(get target_sha)\`, released $(get release_date)
- Current pin: \`$(get current)\`; Lean toolchain for the target: \`$(get toolchain)\`
- Stable releases between the pins, not ported separately: $(get skipped_releases)
- Failed step: ${failed_step:-none}
- Passed steps: $(get passed_steps)
- Not run: $(get remaining_steps)
- Project warnings in the build log: $(get warnings_total)
- Owner: $owner
- Run, logs and evidence (artifact \`mathlib-bump-logs\`): $run_url
EOF
  local log
  log=$(ls "$log_dir"/[0-9][0-9]-"$failed_step".log 2> /dev/null | head -n 1)
  if [ -n "$failed_step" ] && [ -n "$log" ]; then
    printf '\n<details><summary>Last lines of %s</summary>\n\n~~~text\n' "$(basename "$log")"
    tail -n 60 "$log"
    printf '~~~\n</details>\n'
  fi
}

# report KEY TEXT: comment on the tracking issue, unless its last comment is the
# same report.
report() {
  local marker="<!-- mathlib-bump-report: $1 -->" number last
  number=$(gh issue list --state open --search "\"$ISSUE_TITLE\" in:title" --json number,title \
    | jq -r --arg t "$ISSUE_TITLE" '[.[] | select(.title == $t)][0].number // empty')
  if [ -z "$number" ]; then
    number=$(gh issue create --title "$ISSUE_TITLE" --body "Failures of the scheduled Mathlib bump \
(.github/workflows/mathlib_bump.yml) that need a person: failed discovery or setup, publishing \
errors, merge conflicts on a bump branch, and bump PRs closed without merging. Failed checks \
after the pins change open a draft bump PR instead." | sed 's#.*/##')
  fi
  last=$(gh issue view "$number" --json comments | jq -r '(.comments[-1].body // "") | split("\n")[0]')
  if [ "$last" = "$marker" ]; then
    note "Already reported on #$number: $1"
    return 0
  fi
  gh issue comment "$number" --body "$marker
$2

$(evidence)"
  note "Reported on #$number: $1"
}

# ensure_pr ready|draft: reuse the branch's open PR or open one. A closed or
# merged PR counts only if it has the branch's current head.
ensure_pr() {
  local head prs open merged closed others
  head=$(git ls-remote origin "refs/heads/$branch" | cut -f 1)
  prs=$(gh pr list --head "$branch" --base main --state all \
    --json number,state,url,headRefOid,isCrossRepository \
    | jq --arg h "$head" \
      '[.[] | select((.isCrossRepository | not) and (.state == "OPEN" or .headRefOid == $h))]')
  open=$(jq -r '[.[] | select(.state == "OPEN")][0].url // empty' <<< "$prs")
  merged=$(jq -r '[.[] | select(.state == "MERGED")][0].url // empty' <<< "$prs")
  closed=$(jq -r '[.[] | select(.state == "CLOSED")][0].url // empty' <<< "$prs")
  if [ -n "$open" ]; then
    note "Reusing the open PR for $branch: $open"
    return 0
  elif [ -n "$merged" ]; then
    note "$branch was already merged: $merged"
    return 0
  elif [ -n "$closed" ]; then
    report "closed:$branch:$head" \
      "The PR for \`$branch\` was closed without merging ($closed). The automation does not reopen it; reopen it or delete the branch."
    return 0
  fi
  # Older bump PRs that this target supersedes.
  others=$(gh pr list --base main --state open --json headRefName,url \
    | jq -r --arg b "$branch" '.[]
      | select((.headRefName | startswith("chore/bump-mathlib-")) and .headRefName != $b)
      | "- \(.url) (`\(.headRefName)`)"')
  if [ -n "$others" ]; then
    others="Superseded by this PR; close them once it is reviewed:
$others
"
  fi
  local ci="The required \`build\` check must pass on this PR's head before merging. Per GitHub's documentation, CI runs on a PR opened with \`GITHUB_TOKEN\` wait for a maintainer to select \"Approve workflows to run\"."
  if [ "$1" = ready ]; then
    gh pr create --base main --head "$branch" --title "chore: bump Mathlib to $target" --body "\
Automated bump of Mathlib to \`$target\`. Every step of \`scripts/mathlib_bump.sh\` passed on the bump runner; review new warnings under the warning policy.

$ci

$others
$(evidence)"
    note "Opened the bump PR for $branch."
  else
    gh pr create --draft --base main --head "$branch" \
      --title "chore: bump Mathlib to $target (unverified)" --body "\
Draft bump of Mathlib to \`$target\`: NOT verified. The pins are updated, but the bump stopped at the failed step and the steps after it did not run. Push the remaining adaptations to \`$branch\`, rerun the checks, then mark the PR ready.

$ci

$others
$(evidence)"
    note "Opened a draft bump PR for $branch."
  fi
}

# The bump branch already exists on origin: never touch it, only make sure it
# has a PR and report conflicts with main.
recover() {
  git fetch -q origin main "+refs/heads/$branch:refs/remotes/origin/$branch"
  local others subject kind=draft conflicts status=0
  others=$(git log --format='%ae' "origin/main..origin/$branch" | grep -cvxF "$BOT_EMAIL" || true)
  subject=$(git log -1 --format='%s' "origin/$branch")
  if [ "$others" -eq 0 ] && [ "$subject" = "chore: bump Mathlib to $target" ]; then kind=ready; fi
  note "Keeping origin/$branch at $(git rev-parse --short "origin/$branch") ($others commits by others)."
  conflicts=$(git merge-tree --write-tree --name-only --no-messages origin/main "origin/$branch") \
    || status=$?
  if [ "$status" -eq 1 ]; then
    report "conflict:$branch:$(git rev-parse "origin/$branch"):$(git rev-parse origin/main)" \
      "\`$branch\` conflicts with \`main\` in: $(tail -n +2 <<< "$conflicts" | tr '\n' ' '). The branch was left unchanged; merge \`main\` into it by hand."
  elif [ "$status" -ne 0 ]; then
    echo "git merge-tree failed with status $status" >&2
    exit 1
  fi
  ensure_pr "$kind"
}

# refuse REASON: report an artifact that fails validation and stop.
refused=false
refuse() {
  refused=true
  report "refused:$1" "Not publishing: the bump job's artifact failed validation ($1)."
  exit 1
}

publish_commit() {
  local base changed
  base=$(get base)
  git fetch -q "$log_dir/bump.bundle" "refs/heads/$branch" || refuse "bump.bundle has no $branch"
  [ "$(git rev-parse FETCH_HEAD)" = "$commit" ] || refuse "bump.bundle does not hold commit $commit"
  git merge-base --is-ancestor "$base" origin/main || refuse "base $base is not on main"
  [ "$(git rev-parse "$commit^")" = "$base" ] || refuse "$commit is not a single commit on $base"
  changed=$(git diff --name-only "$base" "$commit" \
    | grep -vxE 'lean-toolchain|lakefile\.toml|lake-manifest\.json' || true)
  [ -z "$changed" ] || refuse "$commit changes files other than the pins: $(echo $changed)"
  if git ls-remote --exit-code --heads origin "refs/heads/$branch" > /dev/null; then
    note "origin already has $branch; not pushing over it."
    recover
    return
  fi
  git push -q origin "$commit:refs/heads/$branch"
  note "Pushed $branch at $commit."
  ensure_pr "$1"
}

# Errors while publishing (a failed push or gh call) are reported as well.
on_exit() {
  local status=$?
  trap - EXIT
  if [ "$status" -ne 0 ] && [ "$refused" = false ]; then
    report "publish-error:${branch:-none}:$status" \
      "Publishing the Mathlib bump result ($result) failed with status $status; see the publish job log. Rerunning the failed job, or the next scheduled run, retries it." \
      || true
  fi
  exit "$status"
}
trap on_exit EXIT

if [ -n "$branch" ] && ! { [[ $target =~ ^v[0-9]+\.[0-9]+\.[0-9]+$ ]] \
    && [ "$branch" = "chore/bump-mathlib-$target" ]; }; then
  refuse "unexpected branch $branch for target $target"
fi

case "$result" in
  up-to-date|compatible) note "Nothing to publish (result: $result)." ;;
  bumped) publish_commit ready ;;
  branch-exists) recover ;;
  failed)
    if [ -n "$commit" ] && [ -n "$branch" ]; then
      publish_commit draft
    else
      report "failed:${target:-unknown}:$failed_step" \
        "The Mathlib bump failed before it changed the pins, so there is no draft PR."
    fi ;;
  *) report "unknown:$result" "scripts/mathlib_bump.sh recorded an unknown result: $result" ;;
esac
