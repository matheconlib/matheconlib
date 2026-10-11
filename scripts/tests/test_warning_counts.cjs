const assert = require('node:assert/strict');
const fs = require('node:fs');
const os = require('node:os');
const path = require('node:path');
const { spawnSync, execFileSync } = require('node:child_process');
const { test } = require('node:test');
const { MARKER, countWarnings, snapshot, validateReport, validateSnapshot, renderReport, postComment, readSnapshot, processRun } = require('../warning-counts.cjs');

function report(overrides = {}) {
  return {
    version: 1, pr_number: 42, run_id: 123, run_attempt: 1,
    base_sha: 'a'.repeat(40), head_sha: 'b'.repeat(40),
    base: { status: 'success', counts: { 'MathEconLib/Basic.lean': 2, 'MathEconLib/Removed.lean': 1 } },
    head: { status: 'success', counts: { 'MathEconLib/Basic.lean': 1, 'MathEconLib/Added.lean': 3 } },
    ...overrides,
  };
}

function savedSnapshot(overrides = {}) {
  return {
    version: 3, event: 'pull_request', pr_number: 42, run_id: 123, run_attempt: 1,
    source_sha: 'b'.repeat(40), build_sha: 'b'.repeat(40), ci_sha: 'c'.repeat(40),
    pr_head_sha: 'b'.repeat(40),
    base_sha: 'a'.repeat(40), build: report().head, ...overrides,
  };
}

function trunkSnapshot(overrides = {}) {
  return savedSnapshot({ event: 'push', pr_number: undefined, base_sha: undefined,
    source_sha: 'a'.repeat(40), build_sha: 'a'.repeat(40), ci_sha: 'a'.repeat(40),
    run_id: 100, build: report().base, ...overrides });
}

function tempDirectory(t) {
  const directory = fs.mkdtempSync(path.join(os.tmpdir(), 'library-warnings-'));
  t.after(() => fs.rmSync(directory, { recursive: true, force: true }));
  return directory;
}

test('counts project diagnostic headers, including tests, examples, cached logs, and Unicode paths', () => {
  const log = [
    '⚠ [2/4] Replayed MathEconLib.Basic',
    'warning: MathEconLib/Basic.lean:1:8: declaration uses `sorry`',
    'warning: MathEconLib/Basic.lean:20:0: unused variable `x`',
    '  warning: MathEconLib/Basic.lean:30:0: quoted continuation text',
    '\x1b[33mwarning: MathEconLib.lean:2:0: root warning\x1b[0m',
    'warning: ./MathEconLib/α.lean:1:0: style warning',
    'warning: .lake/packages/mathlib/Mathlib/Basic.lean:1:0: dependency warning',
    'warning: .lake/packages/other/MathEconLib/Basic.lean:1:0: dependency warning',
    'warning: MathEconLibTest/Basic.lean:1:0: test warning',
    'warning: MathEconLibTest.lean:1:0: test root warning',
    'warning: MathEconLibExamples/Basic.lean:1:0: example warning',
    'warning: MathEconLibExamples.lean:1:0: example root warning',
    'warning: ApiStability.lean:1:0: API pin warning',
    'warning: Lake configuration notice',
    'error: MathEconLib/Basic.lean:3:0: error',
    'info: MathEconLib/Basic.lean:3:0: information',
    'This multiline warning contains the word warning again.',
  ].join('\r\n');
  assert.deepEqual(countWarnings(log), {
    'MathEconLib/Basic.lean': 2, 'MathEconLib.lean': 1, 'MathEconLib/α.lean': 1,
    'MathEconLibTest/Basic.lean': 1, 'MathEconLibTest.lean': 1,
    'MathEconLibExamples/Basic.lean': 1, 'MathEconLibExamples.lean': 1,
    'ApiStability.lean': 1,
  });
});

test('renders a signed total delta and added, deleted, and changed files', () => {
  const markdown = renderReport(report());
  assert.match(markdown, /⚠️: \*\*3 → 4/);
  assert.match(markdown, /3 → 4 warnings \(\+1\)/);
  assert.match(markdown, /MathEconLib\/Added\.lean` \| 0 \| 3 \| \+3/);
  assert.match(markdown, /MathEconLib\/Removed\.lean` \| 1 \| 0 \| -1/);
  assert.match(markdown, /MathEconLib\/Basic\.lean` \| 2 \| 1 \| -1/);
});

test('reports warning reductions and unchanged or empty counts', () => {
  const reduction = renderReport(report({ head: { status: 'success', counts: {} } }));
  assert.match(reduction, /✅: \*\*3 → 0/);
  assert.match(reduction, /3 → 0 warnings \(-3\)/);
  const empty = { status: 'success', counts: {} };
  const markdown = renderReport(report({ base: empty, head: empty }));
  assert.match(markdown, /✅: \*\*0 → 0/);
  assert.match(markdown, /0 → 0 warnings \(0\)/);
  assert.match(markdown, /No warning-count changes by file/);
});

test('shows offsetting file changes even when the total is unchanged', () => {
  const counts = { 'MathEconLib/New.lean': 3 };
  const markdown = renderReport(report({ head: { status: 'success', counts } }));
  assert.match(markdown, /✅: \*\*3 → 3/);
  assert.match(markdown, /3 → 3 warnings \(0\)/);
  assert.match(markdown, /MathEconLib\/New\.lean` \| 0 \| 3 \| \+3/);
});

test('reports separate library, test, and example deltas with API pins counted as tests', () => {
  const markdown = renderReport(report({
    base: { status: 'success', counts: {
      'MathEconLib.lean': 3, 'MathEconLibTest.lean': 2,
      'ApiStability.lean': 1, 'MathEconLibExamples.lean': 1,
    } },
    head: { status: 'success', counts: {
      'MathEconLib.lean': 2, 'MathEconLibTest.lean': 3, 'ApiStability.lean': 1,
    } },
  }));
  assert.match(markdown, /✅: \*\*7 → 6 warnings \(-1\)/);
  assert.match(markdown, /\| Library \| 3 \| 2 \| -1 \|/);
  assert.match(markdown, /\| Tests \| 3 \| 4 \| \+1 \|/);
  assert.match(markdown, /\| Examples \| 1 \| 0 \| -1 \|/);
});

test('test and example warnings contribute to the overall increase status', () => {
  for (const file of ['MathEconLibTest/Basic.lean', 'MathEconLibExamples/Basic.lean']) {
    const markdown = renderReport(report({
      head: { status: 'success', counts: { ...report().base.counts, [file]: 1 } },
    }));
    assert.match(markdown, /⚠️: \*\*3 → 4 warnings \(\+1\)/);
  }
});

test('failed and skipped builds cannot appear as zero-warning improvements', () => {
  for (const outcome of ['failure', 'skipped', 'cancelled', '']) {
    assert.deepEqual(snapshot(outcome, '/nonexistent/log'), { status: 'unavailable' });
  }
  for (const side of ['base', 'head']) {
    const markdown = renderReport(report({ [side]: { status: 'unavailable' } }));
    assert.match(markdown, /comparison unavailable/);
    assert.doesNotMatch(markdown, /⚠️|✅/);
    assert.doesNotMatch(markdown, /→/);
  }
  assert.throws(() => snapshot('success', '/nonexistent/log'), /ENOENT/);
});

test('rejects malformed artifact data and file names that could inject Markdown', () => {
  for (const change of [
    { version: 2 }, { base_sha: 'invalid' }, { pr_number: -1 }, { run_id: 1.5 },
    { base: { status: 'success', counts: [] } },
    { base: { status: 'unavailable', counts: {} } },
    { head: { status: 'success', counts: { 'MathEconLib/A.lean': -1 } } },
    { head: { status: 'success', counts: { 'MathEconLib/A.lean': '1' } } },
    { head: { status: 'success', counts: { 'MathEconLib/../Other.lean': 1 } } },
    { head: { status: 'success', counts: { 'MathEconLib/`@someone`.lean': 1 } } },
  ]) assert.throws(() => validateReport(report(change)));
});

test('limits the per-file table size', () => {
  const counts = Object.fromEntries(Array.from({ length: 101 }, (_, i) => [`MathEconLib/File${i}.lean`, 1]));
  const markdown = renderReport(report({ head: { status: 'success', counts } }));
  assert.match(markdown, /Showing 100 of 103 changed files/);
  const longNames = Object.fromEntries(Array.from({ length: 100 }, (_, i) => [`MathEconLib/${'α'.repeat(400)}${i}.lean`, 1]));
  const bounded = renderReport(report({ head: { status: 'success', counts: longNames } }));
  assert.ok(Buffer.byteLength(bounded) < 60000);
});

test('collector writes JSON and the CI summary, preserving build outcomes', t => {
  const directory = tempDirectory(t);
  fs.writeFileSync(path.join(directory, 'build.log'), 'warning: MathEconLib/A.lean:1:0: warning\n');
  const buildSha = execFileSync('git', ['rev-parse', 'HEAD'], { encoding: 'utf8' }).trim();
  const eventPath = path.join(directory, 'event.json');
  fs.writeFileSync(eventPath, '{}');
  const summary = path.join(directory, 'summary.md');
  for (const outcome of ['success', 'failure', 'skipped']) {
    const result = spawnSync(process.execPath, [path.resolve(__dirname, '../warning-counts.cjs')], {
      encoding: 'utf8',
      env: { ...process.env, REPORT_DIRECTORY: directory, GITHUB_STEP_SUMMARY: summary,
        GITHUB_EVENT_PATH: eventPath, GITHUB_EVENT_NAME: 'push', GITHUB_RUN_ID: '100',
        GITHUB_RUN_ATTEMPT: '1', GITHUB_SHA: buildSha, BUILD_OUTCOME: outcome },
    });
    assert.equal(result.status, 0, result.stderr);
    const data = JSON.parse(fs.readFileSync(path.join(directory, 'snapshot.json'), 'utf8'));
    assert.equal(data.build_sha, buildSha);
    assert.deepEqual(data.build, outcome === 'success'
      ? { status: 'success', counts: { 'MathEconLib/A.lean': 1 } } : { status: 'unavailable' });
  }
  assert.match(fs.readFileSync(summary, 'utf8'), /1 warnings across library, tests, and examples/);
  assert.match(fs.readFileSync(summary, 'utf8'), /count unavailable/);
  for (const headRepo of ['owner/library', 'contributor/library']) {
    fs.writeFileSync(eventPath, JSON.stringify({ pull_request: {
      number: 42, base: { sha: 'a'.repeat(40) },
      head: { sha: 'b'.repeat(40), repo: { full_name: headRepo } },
    } }));
    const result = spawnSync(process.execPath, [path.resolve(__dirname, '../warning-counts.cjs')], {
      encoding: 'utf8',
      env: { ...process.env, REPORT_DIRECTORY: directory, GITHUB_EVENT_PATH: eventPath,
        GITHUB_EVENT_NAME: 'pull_request', GITHUB_RUN_ID: '123', GITHUB_RUN_ATTEMPT: '1',
        GITHUB_SHA: buildSha, GITHUB_REPOSITORY: 'owner/library', BUILD_OUTCOME: 'success' },
    });
    assert.equal(result.status, 0, result.stderr);
    const data = JSON.parse(fs.readFileSync(path.join(directory, 'snapshot.json'), 'utf8'));
    assert.equal(data.source_sha, 'b'.repeat(40));
    assert.equal(data.pr_head_sha, headRepo === 'owner/library' ? buildSha : 'b'.repeat(40));
  }
});

function publisher(t, { data = savedSnapshot(), baseline = trunkSnapshot(), comments = [], prChanges = {}, runChanges = {} } = {}) {
  const calls = [];
  const pr = {
    number: 42, state: 'open', base: { sha: 'a'.repeat(40), repo: { full_name: 'owner/library' } },
    head: { sha: 'b'.repeat(40), ref: 'pr-branch', repo: { full_name: 'contributor/library' } }, ...prChanges,
  };
  const context = {
    serverUrl: 'https://github.com', repo: { owner: 'owner', repo: 'library' },
    payload: { workflow_run: { id: 123, run_attempt: 1, event: 'pull_request',
      head_sha: 'b'.repeat(40), head_repository: { full_name: 'contributor/library' }, ...runChanges } },
  };
  const github = {
    rest: {
      pulls: { get: async args => { calls.push(['get', args]); return { data: pr }; } },
      issues: {
        listComments: Symbol('listComments'),
        createComment: async args => calls.push(['create', args]),
        updateComment: async args => calls.push(['update', args]),
      },
    },
    paginate: async (_method, args) => { calls.push(['list', args]); return comments; },
  };
  return { calls, github, context, pr,
    publish: () => postComment({ github, context, core: { info() {} }, current: data, baseline, run: context.payload.workflow_run }) };
}

test('creates a fork PR comment with a link to the build run', async t => {
  const { calls, publish } = publisher(t);
  await publish();
  assert.deepEqual(calls.map(([method]) => method), ['get', 'list', 'create']);
  const comment = calls.at(-1)[1];
  assert.equal(comment.issue_number, 42);
  assert.match(comment.body, /3 → 4 warnings \(\+1\)/);
  assert.match(comment.body, /https:\/\/github.com\/owner\/library\/actions\/runs\/123/);
});

test('updates its existing bot comment rather than creating duplicates', async t => {
  const { calls, publish } = publisher(t, { comments: [
    { id: 7, user: { login: 'person', type: 'User' }, body: MARKER + '\n' },
    { id: 8, user: { login: 'github-actions[bot]', type: 'Bot' }, body: MARKER + '\nold report' },
  ] });
  await publish();
  assert.equal(calls.at(-1)[0], 'update');
  assert.equal(calls.at(-1)[1].comment_id, 8);
});

test('skips reports after PR closure or head/base changes', async t => {
  for (const prChanges of [
    { state: 'closed' },
    { head: { sha: 'c'.repeat(40), repo: { full_name: 'contributor/library' } } },
    { base: { sha: 'c'.repeat(40), repo: { full_name: 'owner/library' } } },
  ]) {
    const { calls, publish } = publisher(t, { prChanges });
    await publish();
    assert.deepEqual(calls.map(([method]) => method), ['get']);
  }
});

test('rejects artifacts bound to another run, attempt, event, or head revision', async t => {
  for (const runChanges of [
    { id: 124 }, { run_attempt: 2 }, { event: 'push' }, { head_sha: 'c'.repeat(40) },
  ]) {
    const { calls, publish } = publisher(t, { runChanges });
    await assert.rejects(publish, /does not match/);
    assert.equal(calls.length, 0);
  }
});

test('rejects artifacts associated with another PR repository', async t => {
  for (const prChanges of [
    { head: { sha: 'b'.repeat(40), repo: { full_name: 'other/library' } } },
    { base: { sha: 'a'.repeat(40), repo: { full_name: 'other/library' } } },
  ]) {
    const { calls, publish } = publisher(t, { prChanges });
    await assert.rejects(publish, /does not belong/);
    assert.deepEqual(calls.map(([method]) => method), ['get']);
  }
});

test('publishes an unavailable report when either build failed', async t => {
  const { calls, publish } = publisher(t, { data: savedSnapshot({ build: { status: 'unavailable' } }) });
  await publish();
  assert.match(calls.at(-1)[1].body, /comparison unavailable/);
  assert.doesNotMatch(calls.at(-1)[1].body, /→/);
});

test('uses a missing-baseline message without treating it as zero warnings', async t => {
  const { calls, publish } = publisher(t, { baseline: null });
  await publish();
  assert.match(calls.at(-1)[1].body, /No saved successful trunk build/);
  assert.doesNotMatch(calls.at(-1)[1].body, /→/);
});

test('refuses a baseline for a different commit or from a PR build', async t => {
  for (const baseline of [trunkSnapshot({ source_sha: 'd'.repeat(40), build_sha: 'd'.repeat(40) }), savedSnapshot()]) {
    const { calls, publish } = publisher(t, { baseline });
    await assert.rejects(publish, /baseline does not match/);
    assert.equal(calls.length, 0);
  }
});

test('labels existing CI merge builds and rejects an unrelated checkout', async t => {
  const { calls, publish } = publisher(t, { data: savedSnapshot({ build_sha: 'c'.repeat(40) }) });
  await publish();
  assert.match(calls.at(-1)[1].body, /merge build `cccccccc`/);
  assert.throws(() => validateSnapshot(savedSnapshot({ build_sha: 'd'.repeat(40) })), /different revision/);
});

function orchestrator(t, { trigger = 'pull_request', baseline = trunkSnapshot(), current = savedSnapshot(), includeBaseline = true, includePr = true, prChanges = {}, runChanges = {} } = {}) {
  const fixture = publisher(t, { prChanges, runChanges });
  const sourceRun = fixture.context.payload.workflow_run;
  const baseRun = { id: 100, run_attempt: 1, event: 'push', head_sha: 'a'.repeat(40),
    head_branch: 'main', conclusion: 'success', head_repository: { full_name: 'owner/library' } };
  fixture.context.payload.workflow_run = trigger === 'push' ? baseRun : sourceRun;
  const actions = { listWorkflowRuns: Symbol('runs'), listWorkflowRunArtifacts: Symbol('artifacts') };
  fixture.github.rest.actions = actions;
  fixture.github.rest.pulls.list = Symbol('pulls');
  const originalPaginate = fixture.github.paginate;
  fixture.github.paginate = async (method, args) => {
    if (method === actions.listWorkflowRuns) {
      fixture.calls.push(['runs', args]);
      assert.equal(args.workflow_id, 'lean_action_ci.yaml');
      if (args.branch === 'main') {
        assert.equal(args.head_sha, 'a'.repeat(40));
        assert.equal(args.branch, 'main');
        return includeBaseline ? [baseRun] : [];
      }
      assert.equal(args.branch, 'pr-branch');
      return includePr ? [sourceRun] : [];
    }
    if (method === fixture.github.rest.pulls.list) return [fixture.pr];
    return originalPaginate(method, args);
  };
  const loads = [];
  return { ...fixture, loads, process: () => processRun({ github: fixture.github, context: fixture.context,
    core: { info() {} }, loadSnapshot: async ({ run }) => {
      loads.push(run.id);
      return run.id === 100 ? baseline : current;
    } }) };
}

test('compares PR output with the exact saved trunk snapshot using only read APIs', async t => {
  const fixture = orchestrator(t);
  await fixture.process();
  assert.deepEqual(fixture.loads, [123, 100]);
  assert.match(fixture.calls.at(-1)[1].body, /3 → 4 warnings \(\+1\)/);
  assert.match(fixture.calls.at(-1)[1].body, /Saved trunk build/);
});

test('missing baseline does not start any build', async t => {
  const fixture = orchestrator(t, { includeBaseline: false });
  await fixture.process();
  assert.deepEqual(fixture.loads, [123]);
  assert.match(fixture.calls.at(-1)[1].body, /No saved successful trunk build/);
});

test('accepts a manually seeded trunk baseline', async t => {
  const fixture = publisher(t, { baseline: trunkSnapshot({ event: 'workflow_dispatch' }) });
  await fixture.publish();
  assert.match(fixture.calls.at(-1)[1].body, /3 → 4 warnings \(\+1\)/);
});

test('trunk completion retries an already-built PR after its baseline arrives', async t => {
  const fixture = orchestrator(t, { trigger: 'push' });
  await fixture.process();
  assert.deepEqual(fixture.loads, [100, 123]);
  assert.equal(fixture.calls.at(-1)[0], 'create');
  assert.match(fixture.calls.at(-1)[1].body, /3 → 4 warnings \(\+1\)/);
});

test('trunk retry finds counts after CI advances the PR head with its import commit', async t => {
  const fixture = orchestrator(t, {
    trigger: 'push', current: savedSnapshot({ pr_head_sha: 'd'.repeat(40), build_sha: 'd'.repeat(40) }),
    prChanges: { head: { sha: 'd'.repeat(40), ref: 'pr-branch', repo: { full_name: 'owner/library' } } },
    runChanges: { head_repository: { full_name: 'owner/library' } },
  });
  await fixture.process();
  assert.deepEqual(fixture.loads, [100, 123]);
  assert.equal(fixture.calls.at(-1)[0], 'create');
  assert.match(fixture.calls.at(-1)[1].body, /PR: `dddddddd`/);
});

test('failed trunk builds and missing PR snapshots do not trigger comparisons', async t => {
  for (const options of [
    { trigger: 'push', baseline: trunkSnapshot({ build: { status: 'unavailable' } }) },
    { trigger: 'push', includePr: false },
    { current: null },
  ]) {
    const fixture = orchestrator(t, options);
    await fixture.process();
    assert.ok(!fixture.calls.some(([method]) => ['create', 'update'].includes(method)));
  }
});

test('reads only the JSON member of a downloaded artifact and validates its run', async t => {
  const directory = tempDirectory(t);
  fs.writeFileSync(path.join(directory, 'snapshot.json'), JSON.stringify(savedSnapshot()));
  fs.writeFileSync(path.join(directory, 'untrusted.cjs'), 'throw new Error("Never execute this");');
  execFileSync('zip', ['-q', 'snapshot.zip', 'snapshot.json', 'untrusted.cjs'], { cwd: directory });
  const bytes = fs.readFileSync(path.join(directory, 'snapshot.zip'));
  const fixture = publisher(t);
  fixture.github.rest.actions = {
    listWorkflowRunArtifacts: Symbol('artifacts'),
    downloadArtifact: async () => ({ data: bytes }),
  };
  fixture.github.paginate = async () => [{ id: 1, name: 'library-warning-counts', expired: false, size_in_bytes: bytes.length }];
  const data = await readSnapshot({ github: fixture.github, context: fixture.context, run: fixture.context.payload.workflow_run });
  assert.deepEqual(data, savedSnapshot());
  fixture.github.rest.actions.downloadArtifact = async () => { throw Object.assign(new Error('expired'), { status: 410 }); };
  assert.equal(await readSnapshot({ github: fixture.github, context: fixture.context, run: fixture.context.payload.workflow_run }), null);
  fixture.github.paginate = async () => [{ name: 'library-warning-counts', expired: true }];
  assert.equal(await readSnapshot({ github: fixture.github, context: fixture.context, run: fixture.context.payload.workflow_run }), null);
});

test('ignores older library-only snapshots rather than treating missing scopes as zero', async t => {
  const data = savedSnapshot({ version: 2 });
  assert.throws(() => validateSnapshot(data), /Invalid warning snapshot metadata/);
  const directory = tempDirectory(t);
  fs.writeFileSync(path.join(directory, 'snapshot.json'), JSON.stringify(data));
  execFileSync('zip', ['-q', 'snapshot.zip', 'snapshot.json'], { cwd: directory });
  const fixture = publisher(t);
  fixture.github.rest.actions = {
    listWorkflowRunArtifacts: Symbol('artifacts'),
    downloadArtifact: async () => ({ data: fs.readFileSync(path.join(directory, 'snapshot.zip')) }),
  };
  fixture.github.paginate = async () => [{ id: 1, name: 'library-warning-counts', expired: false, size_in_bytes: 1000 }];
  assert.equal(await readSnapshot({ github: fixture.github, context: fixture.context, run: fixture.context.payload.workflow_run }), null);
});
