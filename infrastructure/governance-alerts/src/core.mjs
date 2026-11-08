export const REPO = 'matheconlib/matheconlib';
export const RULE_ID = 26805968;
export const RULE_URL = `https://github.com/${REPO}/rules/${RULE_ID}`;
export const ACCESS_URL = `https://github.com/${REPO}/settings/access`;
export const MERGERS = [
  [1121490, 'bocowgill'], [116958103, 'Ruizsolveall'], [1210395, 'scduko'],
  [43812953, 'peabrainiac'], [70076529, 'danlyng'], [4667623, 'morankor'],
  [13203488, 'jjaassoonn'],
];
export const APPROVED_ADMINS = MERGERS.slice(0, 3).map(([id, login]) => ({ id, login }));
const names = new Map(MERGERS);
export const stable = value => JSON.stringify(canonical(value));
function canonical(value) {
  if (Array.isArray(value)) return value.map(canonical).sort((a, b) => JSON.stringify(a).localeCompare(JSON.stringify(b)));
  if (value && typeof value === 'object') return Object.fromEntries(Object.keys(value).sort().map(k => [k, canonical(value[k])]));
  return value;
}
export function policy(raw) {
  if (raw === null) return null;
  if (!raw || !Array.isArray(raw.bypass_actors) || !Array.isArray(raw.rules) || !raw.conditions || !raw.enforcement || !raw.target) {
    throw new Error('Incomplete ruleset response; require Administration read access and raw bypass_actors.');
  }
  return canonical({ id: raw.id, target: raw.target, enforcement: raw.enforcement,
    conditions: raw.conditions, rules: raw.rules,
    bypass_actors: raw.bypass_actors.map(a => ({ actor_id: a.actor_id, actor_type: a.actor_type, bypass_mode: a.bypass_mode })) });
}
export const APPROVED_POLICY = policy({ id: RULE_ID, target: 'branch', enforcement: 'active',
  conditions: { ref_name: { include: ['refs/heads/main'], exclude: [] } }, rules: [{ type: 'update' }],
  bypass_actors: MERGERS.map(([actor_id]) => ({ actor_id, actor_type: 'User', bypass_mode: 'pull_request' })) });
export function initialState() {
  return { version: 1, observed: { policy: APPROVED_POLICY, admins: APPROVED_ADMINS, invitations: [] },
    historyPolicy: APPROVED_POLICY, historySeen: [56843070], lastSuccessfulCheck: null, failure: null };
}
function actorLabel(a) { return `${a.actor_type} ${names.get(a.actor_id) || a.actor_id} (${a.bypass_mode})`; }
export function policyChanges(before, after) {
  if (stable(before) === stable(after)) return [];
  if (!after) return ['The governing ruleset was deleted or is no longer accessible in the verified repository ruleset list.'];
  if (!before) return ['The governing ruleset exists again.', ...policyChanges(APPROVED_POLICY, after)];
  const lines = [];
  const oldActors = before.bypass_actors.map(actorLabel), newActors = after.bypass_actors.map(actorLabel);
  for (const a of newActors.filter(x => !oldActors.includes(x))) lines.push(`Merge exception added: ${a}.`);
  for (const a of oldActors.filter(x => !newActors.includes(x))) lines.push(`Merge exception removed: ${a}.`);
  for (const k of ['enforcement', 'target', 'conditions', 'rules']) {
    if (stable(before[k]) !== stable(after[k])) lines.push(`${k} changed: ${stable(before[k])} → ${stable(after[k])}.`);
  }
  return lines;
}
export async function digest(value) {
  const data = typeof value === 'string' ? value : stable(value);
  return [...new Uint8Array(await crypto.subtle.digest('SHA-256', new TextEncoder().encode(data)))].map(x => x.toString(16).padStart(2, '0')).join('');
}
export async function sign(secret, body) {
  const key = await crypto.subtle.importKey('raw', new TextEncoder().encode(secret), { name: 'HMAC', hash: 'SHA-256' }, false, ['sign']);
  return 'sha256=' + [...new Uint8Array(await crypto.subtle.sign('HMAC', key, new TextEncoder().encode(body)))].map(x => x.toString(16).padStart(2, '0')).join('');
}
export async function validSignature(secret, header, body) {
  if (!secret || !/^sha256=[a-f0-9]{64}$/.test(header || '')) return false;
  const key = await crypto.subtle.importKey('raw', new TextEncoder().encode(secret), { name: 'HMAC', hash: 'SHA-256' }, false, ['verify']);
  const bytes = Uint8Array.from(header.slice(7).match(/../g), b => parseInt(b, 16));
  return crypto.subtle.verify('HMAC', key, bytes, new TextEncoder().encode(body));
}
export function relevantEvent(event, body) {
  if (event === 'ping') return true;
  if (body.organization?.login?.toLowerCase() !== 'matheconlib' && body.repository?.full_name?.toLowerCase() !== REPO) return false;
  if (body.repository && body.repository.full_name?.toLowerCase() !== REPO) return false;
  if (event === 'repository_ruleset') return body.repository_ruleset?.id === RULE_ID || body.action === 'created';
  return ['member', 'membership', 'organization', 'team', 'team_add', 'repository', 'meta'].includes(event);
}
function notice(key, title, lines, source, now) { return { key, subject: `[MathEconLib governance] ${title}`, text: `${lines.join('\n')}\n\nSource: ${source}\nObserved: ${now}\n\nReview the change and restore the approved policy if it was unintended. This monitor does not change repository access or rules.`, createdAt: now }; }
export async function reconcile(previous, snapshot, now = new Date().toISOString()) {
  if (!snapshot || !Array.isArray(snapshot.admins) || !Array.isArray(snapshot.invitations) || !Array.isArray(snapshot.history)) throw new Error('Incomplete governance snapshot.');
  const state = structuredClone(previous), alerts = [];
  const currentPolicy = policy(snapshot.policy);
  let historyPolicy = state.historyPolicy;
  const unseen = snapshot.history.filter(h => !state.historySeen.includes(h.version_id));
  for (const h of unseen) {
    const p = policy(h.policy), changes = policyChanges(historyPolicy, p);
    if (changes.length) alerts.push(notice(`history:${h.version_id}`, 'Merge rule changed', [
      ...changes, `Recorded actor: ${names.get(h.actor?.id) || h.actor?.id || 'unavailable'}; time: ${h.updated_at || 'unavailable'}.`,
      `Current policy ${stable(currentPolicy) === stable(APPROVED_POLICY) ? 'matches' : 'differs from'} the approved baseline.`,
    ], `${RULE_URL}/history`, now));
    historyPolicy = p;
    state.historySeen.push(h.version_id);
  }
  // History is authoritative for intervening changes; only add a snapshot alert
  // if the live state differs from the most recent historical state as well.
  const changes = policyChanges(state.observed.policy, currentPolicy);
  if (changes.length && (!unseen.length || stable(historyPolicy) !== stable(currentPolicy))) {
    const key = 'policy:' + await digest([state.observed.policy, currentPolicy, state.historySeen.at(-1)]);
    alerts.push(notice(key, 'Merge rule changed', changes, RULE_URL, now));
  }
  state.historyPolicy = historyPolicy;
  const oldAdmins = new Map(state.observed.admins.map(a => [a.id, a]));
  const newAdmins = new Map(snapshot.admins.map(a => [a.id, a]));
  const approvedIds = new Set(APPROVED_ADMINS.map(a => a.id));
  for (const a of snapshot.admins.filter(a => !oldAdmins.has(a.id))) alerts.push(notice(
    `admin:${a.id}:${now}`, 'New Admin access', [`@${a.login} now has effective Admin access, including inherited access.`], ACCESS_URL, now));
  for (const a of state.observed.admins.filter(a => !newAdmins.has(a.id) && !approvedIds.has(a.id))) alerts.push(notice(
    `admin-revoked:${a.id}:${now}`, 'Unexpected Admin access revoked', [`@${a.login} no longer has effective Admin access.`], ACCESS_URL, now));
  const oldInvites = new Set(state.observed.invitations.map(i => i.id));
  for (const i of snapshot.invitations.filter(i => !oldInvites.has(i.id))) alerts.push(notice(
    `invitation:${i.id}`, 'Admin invitation issued', [`Admin invitation for @${i.login || 'unknown user'} is pending; it is not active access.`], ACCESS_URL, now));
  if (state.failure) alerts.push(notice(`recovered:${state.failure}`, 'Governance checks restored', ['Authenticated governance checks are working again.'], RULE_URL, now));
  state.observed = structuredClone({ policy: currentPolicy, admins: snapshot.admins, invitations: snapshot.invitations });
  state.historySeen = state.historySeen.slice(-2000);
  state.lastSuccessfulCheck = now;
  state.failure = null;
  return { state, alerts };
}
export function failureNotice(error, now) {
  // Errors from the API reader contain only paths/statuses, never response bodies or credentials.
  return notice(`failure:${error.message}`, 'Governance monitoring needs attention', [error.message, 'The previous successful checkpoint has been preserved.'], RULE_URL, now);
}
