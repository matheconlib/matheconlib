const assert = require('node:assert/strict');
const { execFileSync } = require('node:child_process');
const fs = require('node:fs');
const os = require('node:os');
const path = require('node:path');
const { test } = require('node:test');
const { restoreProofSourceCache } = require('../restore-proof-source-cache.cjs');

const context = { repo: { owner: 'owner', repo: 'library' }, payload: { repository: { id: 10 } } };
const mainRun = {
  id: 1, run_attempt: 2, head_branch: 'main', event: 'push', status: 'completed',
  conclusion: 'success', path: '.github/workflows/lean_action_ci.yaml',
  repository: { id: 10 }, head_repository: { id: 10 },
};

function tempDirectory(t) {
  const directory = fs.mkdtempSync(path.join(os.tmpdir(), 'proof-source-cache-test-'));
  t.after(() => fs.rmSync(directory, { recursive: true, force: true }));
  return directory;
}

test('restores only a successful same-repository main push and its current attempt', async t => {
  const directory = tempDirectory(t);
  let destination;
  const cache = { ['a'.repeat(64)]: 2 };
  fs.writeFileSync(path.join(directory, 'source-cache.json'), JSON.stringify(cache));
  fs.writeFileSync(path.join(directory, 'extra.txt'), 'extra file');
  execFileSync('zip', ['-q', 'cache.zip', 'source-cache.json', 'extra.txt'], { cwd: directory });
  const archive = fs.readFileSync(path.join(directory, 'cache.zip'));
  fs.unlinkSync(path.join(directory, 'extra.txt'));

  const candidates = [
    { ...mainRun, id: 2, event: 'pull_request' },
    { ...mainRun, id: 3, head_repository: { id: 20 } },
    { ...mainRun, id: 4, conclusion: 'failure' },
    { ...mainRun, id: 5, head_branch: 'topic' },
    { ...mainRun, id: 6, path: '.github/workflows/other.yaml' },
    mainRun,
  ];
  const actions = {
    listWorkflowRuns: async options => {
      assert.equal(options.workflow_id, 'lean_action_ci.yaml');
      assert.equal(options.branch, 'main');
      assert.equal(options.event, 'push');
      assert.equal(options.status, 'success');
      return { data: { workflow_runs: candidates } };
    },
    listWorkflowRunArtifacts: async ({ run_id }) => {
      assert.equal(run_id, 1);
      return { data: { artifacts: [
        { id: 40, name: 'proof-source-cache-v1-1', size_in_bytes: archive.length },
        { id: 41, name: 'proof-source-cache-v1-2', size_in_bytes: archive.length },
      ] } };
    },
    downloadArtifact: async ({ artifact_id }) => {
      assert.equal(artifact_id, 41);
      return { data: archive };
    },
  };
  const core = { info: () => {}, warning: assert.fail, setOutput: (name, value) => {
    assert.equal(name, 'path');
    destination = value;
  } };
  await restoreProofSourceCache({ github: { rest: { actions } }, context, core, temporaryRoot: directory });
  assert.deepEqual(JSON.parse(fs.readFileSync(destination, 'utf8')), cache);
  assert.equal(fs.existsSync(path.join(path.dirname(destination), 'extra.txt')), false);
});

test('a missing artifact or an API outage leaves the audit cache empty', async t => {
  const messages = [];
  const destinations = [];
  const core = {
    info: message => messages.push(message), warning: message => messages.push(message),
    setOutput: (name, value) => { assert.equal(name, 'path'); destinations.push(value); },
  };
  const actions = {
    listWorkflowRuns: async () => ({ data: { workflow_runs: [mainRun] } }),
    listWorkflowRunArtifacts: async () => ({ data: { artifacts: [] } }),
  };
  const inputs = { github: { rest: { actions } }, context, core, temporaryRoot: tempDirectory(t) };
  await restoreProofSourceCache(inputs);
  actions.listWorkflowRuns = async () => { throw new Error('request timed out'); };
  await restoreProofSourceCache(inputs);
  assert.equal(new Set(destinations).size, 2);
  assert.ok(destinations.every(destination => !fs.existsSync(destination)));
  assert.equal(messages.length, 2);
  assert.ok(messages.every(message => message.includes('Running a full source audit')));
});
