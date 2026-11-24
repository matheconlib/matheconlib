// Restore source audit results exclusively from successful pushes to main.
const fs = require('node:fs');
const os = require('node:os');
const path = require('node:path');
const { execFileSync } = require('node:child_process');

const WORKFLOW = 'lean_action_ci.yaml';
const SNAPSHOT = 'source-cache.json';
const MAX_SIZE = 1024 * 1024;

function readCache(bytes) {
  if (bytes.length > MAX_SIZE) throw new Error('Cache archive is too large');
  const temporary = fs.mkdtempSync(path.join(os.tmpdir(), 'proof-source-cache-'));
  try {
    const archive = path.join(temporary, 'cache.zip');
    fs.writeFileSync(archive, bytes);
    // Read only the JSON member. Artifact paths never determine where files go.
    const json = execFileSync('unzip', ['-p', archive, SNAPSHOT], {
      encoding: 'utf8', maxBuffer: MAX_SIZE, timeout: 10000,
    });
    const data = JSON.parse(json);
    if (!data || typeof data !== 'object' || Array.isArray(data) || Object.entries(data).some(
      ([key, value]) => !/^[a-f0-9]{64}$/.test(key) || !Number.isSafeInteger(value) || value < 0,
    )) throw new Error('Invalid source audit cache');
    return json;
  } finally {
    fs.rmSync(temporary, { recursive: true, force: true });
  }
}

async function restoreProofSourceCache({
  github, context, core, temporaryRoot = process.env.RUNNER_TEMP,
}) {
  const directory = fs.mkdtempSync(path.join(temporaryRoot, 'proof-source-cache-'));
  const destination = path.join(directory, SNAPSHOT);
  core.setOutput('path', destination);
  const { owner, repo } = context.repo;
  const repositoryId = context.payload.repository?.id;
  const options = { owner, repo, request: { timeout: 8000 } };
  const actions = github.rest.actions;
  try {
    const { data: { workflow_runs: runs } } = await actions.listWorkflowRuns({
      ...options, workflow_id: WORKFLOW, branch: 'main', event: 'push', status: 'success',
      per_page: 5,
    });
    for (const run of runs) {
      if (!repositoryId || run.repository?.id !== repositoryId
          || run.head_repository?.id !== repositoryId || run.head_branch !== 'main'
          || run.event !== 'push' || run.status !== 'completed' || run.conclusion !== 'success'
          || run.path !== `.github/workflows/${WORKFLOW}`
          || !Number.isSafeInteger(run.run_attempt)) continue;
      const { data: { artifacts } } = await actions.listWorkflowRunArtifacts({
        ...options, run_id: run.id, per_page: 100,
      });
      const artifact = artifacts.find(item => !item.expired
        && item.name === `proof-source-cache-v1-${run.run_attempt}`
        && item.size_in_bytes > 0 && item.size_in_bytes <= MAX_SIZE);
      if (!artifact) continue;
      const download = await actions.downloadArtifact({
        ...options, artifact_id: artifact.id, archive_format: 'zip',
      });
      const json = readCache(Buffer.from(download.data));
      fs.writeFileSync(destination, json);
      core.info(`Restored proof source cache from main run ${run.id}, attempt ${run.run_attempt}.`);
      return;
    }
    core.info('No proof source cache from a successful main push. Running a full source audit.');
  } catch (error) {
    core.warning(`Proof source cache unavailable. Running a full source audit. ${error.message}`);
  }
}

module.exports = { restoreProofSourceCache };
