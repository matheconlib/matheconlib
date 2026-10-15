#!/usr/bin/env bash
# Publish validated documentation snapshots to an existing R2 bucket.
set -euo pipefail

if [[ $# != 1 ]]; then
  echo "Usage: bash scripts/upload-docs.sh OUTPUT_DIR" >&2
  exit 2
fi
if [[ ${GITHUB_REF:-} != refs/heads/main || (${GITHUB_EVENT_NAME:-} != push && ${GITHUB_EVENT_NAME:-} != workflow_dispatch) ]]; then
  echo "R2 publication requires a main-branch push or manual main run" >&2
  exit 1
fi
: "${R2_BUCKET:?Set the R2_BUCKET repository variable}"
: "${R2_ENDPOINT_URL:?Set the R2_ENDPOINT_URL repository variable}"
: "${AWS_ACCESS_KEY_ID:?Set the R2_ACCESS_KEY_ID repository secret}"
: "${AWS_SECRET_ACCESS_KEY:?Set the R2_SECRET_ACCESS_KEY repository secret}"
: "${GITHUB_RUN_ID:?Missing GitHub run ID}"
: "${GITHUB_RUN_ATTEMPT:?Missing GitHub run attempt}"

output_dir=$1
revision=$(python3 -c 'import json, sys; print(json.load(open(sys.argv[1]))["revision"])' "$output_dir/metadata.json")
if [[ ! $revision =~ ^[a-f0-9]{40}$ || ! $GITHUB_RUN_ID =~ ^[0-9]+$ || ! $GITHUB_RUN_ATTEMPT =~ ^[0-9]+$ ]]; then
  echo "Invalid documentation revision or run identity" >&2
  exit 1
fi
prefix="matheconlib/$revision/$GITHUB_RUN_ID-$GITHUB_RUN_ATTEMPT"
export AWS_DEFAULT_REGION=auto
# R2 needs the classic transfer client with recent AWS CLI releases.
# Keep this configuration out of the user's normal AWS profiles.
config_dir=$(mktemp -d)
trap 'rm -rf "$config_dir"' EXIT
export AWS_CONFIG_FILE="$config_dir/config"
aws configure set default.s3.preferred_transfer_client classic
for file in api-docs.db.gz lake-manifest.json metadata.json; do
  aws s3 cp "$output_dir/$file" "s3://$R2_BUCKET/$prefix/$file" \
    --endpoint-url "$R2_ENDPOINT_URL" --only-show-errors
done
# Metadata is uploaded last so it denotes a complete snapshot.
if [[ -n ${GITHUB_STEP_SUMMARY:-} ]]; then
  printf 'Database snapshot: `s3://%s/%s/api-docs.db.gz`\n' "$R2_BUCKET" "$prefix" >> "$GITHUB_STEP_SUMMARY"
fi
