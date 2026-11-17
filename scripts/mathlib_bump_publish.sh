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
# pushed to a bump branch are kept.
#
# Usage: bash scripts/mathlib_bump_publish.sh LOG_DIR
#   LOG_DIR holds summary.txt, the step logs and bump.bundle from the bump job;
#   a missing or empty summary is reported as a setup failure.
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
  failed_step="setup: the bump job (${BUMP_JOB_RESULT:-unknown}) ended before scripts/mathlib_bump.sh recorded a result"
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
(.github/workflows/mathlib_bump.yml) that need a person: failed discovery or setup, merge \
conflicts on a bump branch, and bump PRs closed without merging. Failed checks after the pins \
change open a draft bump PR instead." | sed 's#.*/##')
  fi
  last=$(gh issue view "$number" --json comments | jq -r '.comments[-1].body // ""' | head -n 1)
  if [ "$last" = "$marker" ]; then
    note "Already reported on #$number: $1"
    return 0
  fi
  gh issue comment "$number" --body "$marker
$2

$(evidence)"
  note "Reported on #$number: $1"
}

# ensure_pr ready|draft: reuse the branch's PR or open it.
ensure_pr() {
  local prs open merged closed
  prs=$(gh pr list --head "$branch" --base main --state all --json number,state,url,isDraft)
  open=$(jq -r '[.[] | select(.state == "OPEN")][0].url // empty' <<< "$prs")
  merged=$(jq -r '[.[] | select(.state == "MERGED")][0].url // empty' <<< "$prs")
  closed=$(jq -r '[.[] | select(.state == "CLOSED")][0].url // empty' <<< "$prs")
  if [ -n "$open" ]; then
    note "Reusing the open PR for $branch: $open"
  elif [ -n "$merged" ]; then
    note "$branch was already merged: $merged"
  elif [ -n "$closed" ]; then
    report "closed:$branch:$(git rev-parse "origin/$branch")" \
      "The PR for \`$branch\` was closed without merging ($closed). The automation does not reopen it; reopen it or delete the branch."
  elif [ "$1" = ready ]; then
    gh pr create --base main --head "$branch" --title "chore: bump Mathlib to $target" --body "\
Automated bump of Mathlib to \`$target\`. Every step of \`scripts/mathlib_bump.sh\` passed on the bump runner; review new warnings under the warning policy.

The required \`build\` check must pass on this PR's head before merging. CI runs on a PR opened with \`GITHUB_TOKEN\` wait for a maintainer to select \"Approve workflows to run\".

$(evidence)"
    note "Opened the bump PR for $branch."
  else
    gh pr create --draft --base main --head "$branch" \
      --title "chore: bump Mathlib to $target (unverified)" --body "\
Draft bump of Mathlib to \`$target\`: NOT verified. The pins are updated, but the bump stopped at the failed step and the steps after it did not run. Push the remaining adaptations to \`$branch\`, rerun the checks, then mark the PR ready.

The required \`build\` check must pass on the final head before merging. CI runs on a PR opened with \`GITHUB_TOKEN\` wait for a maintainer to select \"Approve workflows to run\".

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

publish_commit() {
  git fetch -q "$log_dir/bump.bundle" "refs/heads/$branch"
  if [ "$(git rev-parse FETCH_HEAD)" != "$commit" ]; then
    echo "bump.bundle does not contain the recorded commit $commit" >&2
    exit 1
  fi
  if git ls-remote --exit-code --heads origin "refs/heads/$branch" > /dev/null; then
    note "origin already has $branch; not pushing over it."
    recover
    return
  fi
  git push -q origin "$commit:refs/heads/$branch"
  note "Pushed $branch at $commit."
  ensure_pr "$1"
}

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
