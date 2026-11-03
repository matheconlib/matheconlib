// Count Lean diagnostics and render the PR warning report.
const fs = require('node:fs');
const path = require('node:path');
const os = require('node:os');
const { execFileSync } = require('node:child_process');

const MARKER = '<!-- matheconlib-warning-counts -->';
const PROJECT_FILE = /^(MathEconLib|MathEconLibTest|MathEconLibExamples|ApiStability)(?:\/[\p{L}\p{N}_']+)*\.lean$/u;
const SCOPE_ROOTS = {
  MathEconLib: 'Library',
  MathEconLibTest: 'Tests',
  ApiStability: 'Tests',
  MathEconLibExamples: 'Examples',
};
const SHA = /^[0-9a-f]{40}$/;

function countWarnings(log) {
  const counts = {};
  // Lake prefixes diagnostics with their severity, including replayed logs.
  const plain = log.replace(/\x1b\[[0-9;]*m/g, '');
  for (const line of plain.split(/\r?\n/)) {
    // Lean 4.35 also emits module-import warnings without line/column numbers.
    const match = /^warning: (?:\.\/)?([^:]+):(?:\d+:\d+:| imports )/.exec(line);
    if (match && PROJECT_FILE.test(match[1])) {
      counts[match[1]] = (counts[match[1]] || 0) + 1;
    }
  }
  return counts;
}

function snapshot(outcome, logPath) {
  // Failed or skipped builds cannot supply a complete warning count.
  if (outcome !== 'success') return { status: 'unavailable' };
  return { status: 'success', counts: countWarnings(fs.readFileSync(logPath, 'utf8')) };
}

function validateBuild(item) {
  if (!item || !['success', 'unavailable'].includes(item.status)) {
    throw new Error('Invalid build status');
  }
  if (item.status === 'unavailable') {
    if (item.counts !== undefined) throw new Error('Build unavailable');
    return;
  }
  if (!item.counts || typeof item.counts !== 'object' || Array.isArray(item.counts)) {
    throw new Error('Invalid warning counts');
  }
  const entries = Object.entries(item.counts);
  if (entries.length > 10000) throw new Error('Too many files in warning report');
  for (const [file, count] of entries) {
      if (file.length > 500 || !PROJECT_FILE.test(file)
        || !Number.isSafeInteger(count) || count < 0 || count > 1000000) {
      throw new Error('Invalid file or count in warning report');
    }
  }
}

function validateReport(report) {
  if (!report || report.version !== 1 || !SHA.test(report.base_sha)
      || !SHA.test(report.head_sha)) throw new Error('Invalid warning report metadata');
  for (const key of ['pr_number', 'run_id', 'run_attempt']) {
    if (!Number.isSafeInteger(report[key]) || report[key] <= 0) {
      throw new Error(`Invalid warning report ${key}`);
    }
  }
  validateBuild(report.base);
  validateBuild(report.head);
  return report;
}

function validateSnapshot(data, run) {
  // Older snapshots counted only the library and cannot be compared fairly.
  if (!data || data.version !== 3 || !['push', 'pull_request', 'workflow_dispatch'].includes(data.event)
      || !SHA.test(data.source_sha) || !SHA.test(data.build_sha) || !SHA.test(data.ci_sha)
      || !Number.isSafeInteger(data.run_id) || data.run_id <= 0
      || !Number.isSafeInteger(data.run_attempt) || data.run_attempt <= 0) {
    throw new Error('Invalid warning snapshot metadata');
  }
  if (data.event === 'pull_request' && (!SHA.test(data.base_sha)
      || !SHA.test(data.pr_head_sha)
      || !Number.isSafeInteger(data.pr_number) || data.pr_number <= 0)) {
    throw new Error('Invalid PR metadata in warning snapshot');
  }
  validateBuild(data.build);
  const testedHead = data.event === 'pull_request' ? data.pr_head_sha : data.source_sha;
  if (data.build.status === 'success' && data.build_sha !== testedHead && data.build_sha !== data.ci_sha) {
    throw new Error('CI built a different revision than the warning snapshot describes');
  }
  if (run && (data.run_id !== run.id || data.run_attempt !== run.run_attempt
      || data.source_sha !== run.head_sha || data.event !== run.event)) {
    throw new Error('Warning snapshot does not match the triggering CI run');
  }
  return data;
}

function signed(value) {
  return value > 0 ? `+${value}` : String(value);
}

function total(counts) {
  return Object.values(counts).reduce((sum, value) => sum + value, 0);
}

function totalsByScope(counts) {
  const totals = { Library: 0, Tests: 0, Examples: 0 };
  for (const [file, count] of Object.entries(counts)) {
    const root = PROJECT_FILE.exec(file)[1];
    totals[SCOPE_ROOTS[root]] += count;
  }
  return totals;
}

function renderScopeTable(base, head) {
  const baseTotals = totalsByScope(base);
  const headTotals = totalsByScope(head);
  const rows = Object.keys(baseTotals).map(scope =>
    `| ${scope} | ${baseTotals[scope]} | ${headTotals[scope]} | ${signed(headTotals[scope] - baseTotals[scope])} |`);

  return `| Scope | Base | PR | Change |
| --- | ---: | ---: | ---: |
${rows.join('\n')}`;
}

function renderFileChanges(base, head) {
  const files = [...new Set([...Object.keys(base), ...Object.keys(head)])]
    .filter(file => (base[file] || 0) !== (head[file] || 0)).sort();
  if (!files.length) return 'No warning-count changes by file.';

  const rows = [];
  let tableBytes = 0;
  for (const file of files.slice(0, 100)) {
    const baseCount = base[file] || 0;
    const headCount = head[file] || 0;
    const row = `| \`${file}\` | ${baseCount} | ${headCount} | ${signed(headCount - baseCount)} |`;
    tableBytes += Buffer.byteLength(row + '\n');
    if (tableBytes > 48000) break;
    rows.push(row);
  }
  const truncation = files.length > rows.length
    ? `\n\nShowing ${rows.length} of ${files.length} changed files.` : '';

  return `<details>
<summary>Warning changes by file</summary>

| File | Base | PR | Change |
| --- | ---: | ---: | ---: |
${rows.join('\n')}${truncation}

</details>`;
}

function renderComparison(report) {
  if (report.base.status !== 'success' || report.head.status !== 'success') {
    const reason = report.reason || 'Both builds must finish successfully.';
    return `**Warning comparison unavailable.** ${reason}

Base build: ${report.base.status}. PR build: ${report.head.status}.`;
  }

  const base = report.base.counts;
  const head = report.head.counts;
  const baseTotal = total(base);
  const headTotal = total(head);
  const change = signed(headTotal - baseTotal);
  const status = headTotal > baseTotal ? '⚠️ Warnings increased:' : '✅ OK:';

  return `${status} **${baseTotal} → ${headTotal} warnings (${change}).**

${renderScopeTable(base, head)}

${renderFileChanges(base, head)}`;
}

function renderReport(input) {
  const report = validateReport(input);
  const lastRun = new Date(report.last_run_at || Date.now())
    .toISOString().slice(0, 16).replace('T', ' ');
  const mergeNote = report.build_sha && report.build_sha !== report.head_sha
    ? `\n\nPR counts come from CI's merge build \`${report.build_sha.slice(0, 8)}\`.` : '';

  return `${MARKER}
### Warning counts

Base: \`${report.base_sha.slice(0, 8)}\` · PR: \`${report.head_sha.slice(0, 8)}\` · Last run: ${lastRun} UTC

${renderComparison(report)}${mergeNote}

Counts include compiler, linter, and \`sorry\` warnings. Library covers \`MathEconLib\`; Tests covers \`MathEconLibTest\` and \`ApiStability\`; Examples covers \`MathEconLibExamples\`. Dependencies and Lake notices are excluded.
`;
}

async function postComment({ github, context, core, current, baseline, run }) {
  validateSnapshot(current, run);
  if (current.event !== 'pull_request') throw new Error('A PR snapshot is required');
  if (baseline && (!['push', 'workflow_dispatch'].includes(validateSnapshot(baseline).event)
      || baseline.build_sha !== current.base_sha || baseline.source_sha !== current.base_sha)) {
    throw new Error('Saved baseline does not match the PR base commit');
  }
  const { owner, repo } = context.repo;
  const { data: pr } = await github.rest.pulls.get({ owner, repo, pull_number: current.pr_number });
  if (pr.base.repo.full_name !== `${owner}/${repo}`
      || pr.head.repo?.full_name !== run.head_repository.full_name) {
    throw new Error('Warning report does not belong to this repository and PR');
  }
  if (pr.state !== 'open' || pr.head.sha !== current.pr_head_sha || pr.base.sha !== current.base_sha) {
    core.info('Skipping warning report for a closed or updated PR.');
    return;
  }
  const report = {
    version: 1, pr_number: current.pr_number, run_id: current.run_id, run_attempt: current.run_attempt,
    base_sha: current.base_sha, head_sha: current.pr_head_sha, build_sha: current.build_sha,
    last_run_at: run.updated_at || run.run_started_at || run.created_at,
    base: baseline?.build || { status: 'unavailable' }, head: current.build,
    reason: baseline ? undefined : 'No saved successful trunk build was found for this exact base commit. The baseline may still be building or its artifact may have expired.',
  };
  const body = renderReport(report)
    + `\n[PR build](${context.serverUrl}/${owner}/${repo}/actions/runs/${run.id})`
    + (baseline ? ` · [Saved trunk build](${context.serverUrl}/${owner}/${repo}/actions/runs/${baseline.run_id})` : '') + '\n';
  const comments = await github.paginate(github.rest.issues.listComments, {
    owner, repo, issue_number: report.pr_number, per_page: 100,
  });
  const existing = comments.find(comment => comment.user?.login === 'github-actions[bot]'
    && comment.user?.type === 'Bot' && comment.body?.startsWith(MARKER + '\n'));
  if (existing) {
    await github.rest.issues.updateComment({ owner, repo, comment_id: existing.id, body });
  } else {
    await github.rest.issues.createComment({ owner, repo, issue_number: report.pr_number, body });
  }
}

async function readSnapshot({ github, context, run }) {
  const { owner, repo } = context.repo;
  const artifacts = await github.paginate(github.rest.actions.listWorkflowRunArtifacts, {
    owner, repo, run_id: run.id, per_page: 100,
  });
  const artifact = artifacts.find(item => item.name === 'library-warning-counts' && !item.expired);
  if (!artifact) return null;
  if (artifact.size_in_bytes > 2 * 1024 * 1024) throw new Error('Warning artifact is too large');
  let download;
  try {
    download = await github.rest.actions.downloadArtifact({ owner, repo, artifact_id: artifact.id, archive_format: 'zip' });
  } catch (error) {
    if ([404, 410].includes(error.status)) return null;
    throw error;
  }
  const bytes = Buffer.from(download.data);
  if (bytes.length > 2 * 1024 * 1024) throw new Error('Warning artifact is too large');
  const directory = fs.mkdtempSync(path.join(os.tmpdir(), 'library-warnings-'));
  try {
    const archive = path.join(directory, 'snapshot.zip');
    fs.writeFileSync(archive, bytes);
    // Read one bounded JSON member. Never extract or execute artifact files.
    const json = execFileSync('unzip', ['-p', archive, 'snapshot.json'], {
      encoding: 'utf8', maxBuffer: 1024 * 1024, timeout: 10000,
    });
    const data = JSON.parse(json);
    if (data?.version === 2) return null;
    return validateSnapshot(data, run);
  } finally {
    fs.rmSync(directory, { recursive: true, force: true });
  }
}

async function processRun({ github, context, core, loadSnapshot = readSnapshot }) {
  const { owner, repo } = context.repo;
  const run = context.payload.workflow_run;
  const memo = new Map();
  async function load(candidate) {
    const key = `${candidate.id}:${candidate.run_attempt}`;
    if (!memo.has(key)) memo.set(key, await loadSnapshot({ github, context, run: candidate }));
    const data = memo.get(key);
    return data ? validateSnapshot(data, candidate) : null;
  }
  async function findSaved(event, sha, pr) {
    const runs = await github.paginate(github.rest.actions.listWorkflowRuns, {
      owner, repo, workflow_id: 'lean_action_ci.yaml',
      status: 'completed', ...(event === 'push' ? { branch: 'main', head_sha: sha } : { event, branch: pr.head.ref }), per_page: 100,
    });
    for (const candidate of runs) {
      if (candidate.conclusion === 'cancelled'
          || (event === 'push' ? !['push', 'workflow_dispatch'].includes(candidate.event) : candidate.event !== event)
          || (event === 'push' && (candidate.head_sha !== sha || candidate.head_branch !== 'main'))) continue;
      const data = await load(candidate);
      if (data && (event === 'push'
        ? data.build.status === 'success' && data.build_sha === sha
        : data.pr_number === pr.number && data.pr_head_sha === sha)) {
        return { data, run: candidate };
      }
    }
    return null;
  }
  const current = await load(run);
  if (!current) {
    core.info('No retained warning snapshot for this run.');
    return;
  }
  if (run.event === 'pull_request') {
    const baseline = await findSaved('push', current.base_sha);
    await postComment({ github, context, core, current, baseline: baseline?.data, run });
  } else if (['push', 'workflow_dispatch'].includes(run.event) && run.head_branch === 'main' && current.build.status === 'success') {
    // A PR may finish before its base's trunk build. Retry from saved snapshots
    // when the baseline arrives, without starting either build again.
    const prs = await github.paginate(github.rest.pulls.list, { owner, repo, state: 'open', base: 'main', per_page: 100 });
    for (const pr of prs) {
      if (pr.base.sha !== current.build_sha) continue;
      const saved = await findSaved('pull_request', pr.head.sha, pr);
      if (saved && saved.data.pr_number === pr.number && saved.data.base_sha === current.build_sha) {
        await postComment({ github, context, core, current: saved.data, baseline: current, run: saved.run });
      }
    }
  }
}

function collectSnapshot(env) {
  const directory = env.REPORT_DIRECTORY;
  fs.mkdirSync(directory, { recursive: true });
  const event = JSON.parse(fs.readFileSync(env.GITHUB_EVENT_PATH, 'utf8'));
  const buildSha = execFileSync('git', ['rev-parse', 'HEAD'], { encoding: 'utf8' }).trim();
  const report = validateSnapshot({
    version: 3,
    event: env.GITHUB_EVENT_NAME,
    pr_number: event.pull_request?.number,
    run_id: Number(env.GITHUB_RUN_ID),
    run_attempt: Number(env.GITHUB_RUN_ATTEMPT),
    base_sha: event.pull_request?.base.sha,
    source_sha: event.pull_request?.head.sha || env.GITHUB_SHA,
    ci_sha: env.GITHUB_SHA,
    build_sha: buildSha,
    pr_head_sha: event.pull_request
      ? (event.pull_request.head.repo.full_name === env.GITHUB_REPOSITORY ? buildSha : event.pull_request.head.sha)
      : undefined,
    build: snapshot(env.BUILD_OUTCOME, path.join(directory, 'build.log')),
  });
  fs.writeFileSync(path.join(directory, 'snapshot.json'), JSON.stringify(report, null, 2) + '\n');
  const markdown = `### Warning snapshot\n\nBuild: \`${report.build_sha.slice(0, 12)}\`\n\n`
    + (report.build.status === 'success' ? `**${total(report.build.counts)} warnings across library, tests, and examples.**\n` : 'Warning count unavailable: CI did not finish building successfully.\n');
  process.stdout.write(markdown);
  if (env.GITHUB_STEP_SUMMARY) fs.appendFileSync(env.GITHUB_STEP_SUMMARY, markdown);
  return report;
}

module.exports = { MARKER, countWarnings, snapshot, validateReport, validateSnapshot, renderReport, postComment, readSnapshot, processRun, collectSnapshot };

if (require.main === module) {
  try {
    collectSnapshot(process.env);
  } catch (error) {
    console.error(error.message);
    process.exitCode = 1;
  }
}
