import { REPO, RULE_ID, policy } from './core.mjs';
export function githubReader(token, fetcher = fetch) {
  if (!token) throw new Error('Missing GITHUB_READ_TOKEN.');
  return async path => {
    const url = new URL(path, 'https://api.github.com/');
    if (url.origin !== 'https://api.github.com') throw new Error('Refused a non-GitHub API URL.');
    const r = await fetcher(url, { headers: { Authorization: `Bearer ${token}`, Accept: 'application/vnd.github+json',
      'X-GitHub-Api-Version': '2022-11-28', 'User-Agent': 'MathEconLib-governance-alerts' }, redirect: 'manual', signal: AbortSignal.timeout(15000) });
    if (r.status === 404) return { status: 404 };
    if (!r.ok) throw new Error(`GitHub ${url.pathname}: HTTP ${r.status}.`);
    return { status: r.status, data: await r.json(), next: r.headers.get('link')?.match(/<([^>]+)>; rel="next"/)?.[1] };
  };
}
export async function collectSnapshot(read, known = [], options = { history: true }) {
  async function list(path) {
    const rows = [], visited = new Set();
    for (let next = path; next;) {
      if (visited.has(next) || visited.size >= 100) throw new Error('GitHub pagination did not finish.');
      visited.add(next);
      const r = await read(next);
      if (r.status === 404 || !Array.isArray(r.data)) throw new Error(`Cannot read required GitHub list ${path}.`);
      rows.push(...r.data); next = r.next;
    }
    return rows;
  }
  const root = `repos/${REPO}`;
  const access = await read(root);
  if (!access.data?.permissions?.admin) throw new Error('GitHub repository access cannot verify Administration permissions.');
  const raw = await read(`${root}/rulesets/${RULE_ID}`);
  let currentPolicy = null, history = [];
  if (raw.status === 404) {
    const rules = await list(`${root}/rulesets?includes_parents=true&per_page=100`);
    if (rules.some(r => r.id === RULE_ID)) throw new Error('Ruleset exists but its configuration could not be read.');
  } else {
    currentPolicy = policy(raw.data);
    if (options.history) {
    const versions = await list(`${root}/rulesets/${RULE_ID}/history?per_page=100`);
    if (known.length && !versions.some(h => known.includes(h.version_id))) throw new Error('Ruleset history has a coverage gap; manual reconciliation required.');
    const newVersions = [];
    for (const v of versions) { if (known.includes(v.version_id)) break; newVersions.push(v); }
    for (const v of newVersions.reverse()) {
      const r = await read(`${root}/rulesets/${RULE_ID}/history/${v.version_id}`);
      history.push({ ...v, policy: policy(r.data?.state) });
    }
    }
  }
  // This read verifies the endpoint is usable, but does not mistake an expanded
  // effective-rules response for the raw bypass actor list.
  await list(`${root}/rules/branches/main?per_page=100`);
  const collaborators = await list(`${root}/collaborators?affiliation=all&per_page=100`);
  if (collaborators.some(a => typeof a.permissions?.admin !== 'boolean')) throw new Error('Collaborator permissions are incomplete.');
  const invitations = await list(`${root}/invitations?per_page=100`);
  return { policy: currentPolicy, ruleUpdatedAt: raw.data?.updated_at || null,
    historyCoverage: options.history ? 'ruleset-history' : 'signed-webhooks-and-snapshots',
    admins: collaborators.filter(a => a.permissions.admin).map(({ id, login }) => ({ id, login })),
    invitations: invitations.filter(i => ['admin', 'administer'].includes(i.permissions)).map(i => ({ id: i.id, login: i.invitee?.login })), history };
}
