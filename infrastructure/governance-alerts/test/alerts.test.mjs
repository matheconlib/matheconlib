import test from 'node:test';
import assert from 'node:assert/strict';
import { APPROVED_ADMINS, APPROVED_POLICY, applySignals, initialState, policy, policyChanges, reconcile, relevantEvent, sign, validSignature } from '../src/core.mjs';
import { collectSnapshot, githubReader } from '../src/github.mjs';
import worker, { GovernanceMonitor, sendEmail } from '../src/worker.mjs';
import vm from 'node:vm';
import { readFileSync } from 'node:fs';
import { createHmac } from 'node:crypto';
const now = '2026-11-08T20:00:00.000Z';
const copy = structuredClone;
function snapshot(p = APPROVED_POLICY) { return { policy: copy(p), admins: copy(APPROVED_ADMINS), invitations: [], history: [] }; }
test('approved starting state is quiet and does not overwrite the immutable baseline', async () => {
  const state = initialState(), result = await reconcile(state, snapshot(), now);
  assert.equal(result.alerts.length, 0); assert.equal(state.lastSuccessfulCheck, null);
  assert.equal(result.state.lastSuccessfulCheck, now);
});
test('missing raw bypass actors fails rather than implying an empty allowlist', () => {
  const p = copy(APPROVED_POLICY); delete p.bypass_actors;
  assert.throws(() => policy(p), /Incomplete/);
});
test('name-only edits, timestamps and array reordering are quiet', () => {
  const p = copy(APPROVED_POLICY); p.name = 'new name'; p.updated_at = now; p.bypass_actors.reverse();
  assert.deepEqual(policyChanges(APPROVED_POLICY, policy(p)), []);
});
test('user additions, removals, role replacement and bypass-mode changes alert', async () => {
  for (const mutate of [
    p => p.bypass_actors.push({ actor_type: 'User', actor_id: 999, bypass_mode: 'always' }),
    p => p.bypass_actors.pop(),
    p => p.bypass_actors[0] = { actor_type: 'RepositoryRole', actor_id: 5, bypass_mode: 'always' },
    p => p.bypass_actors[0].bypass_mode = 'always',
  ]) {
    const p = copy(APPROVED_POLICY); mutate(p);
    const r = await reconcile(initialState(), snapshot(p), now); assert.equal(r.alerts.length, 1);
    assert.match(r.alerts[0].text, /Merge exception/);
  }
});
test('disabling, deleting, retargeting and removing the restriction alert', async () => {
  for (const p of [null, { ...copy(APPROVED_POLICY), enforcement: 'disabled' },
    { ...copy(APPROVED_POLICY), target: 'tag' }, { ...copy(APPROVED_POLICY), rules: [] }]) {
    assert.equal((await reconcile(initialState(), snapshot(p), now)).alerts.length, 1);
  }
});
test('history catches a change and reversal even with approved live state, then deduplicates', async () => {
  const p = { ...copy(APPROVED_POLICY), enforcement: 'disabled' }, s = snapshot();
  s.history = [{ version_id: 11, policy: p, actor: { id: 1121490 }, updated_at: now },
    { version_id: 12, policy: APPROVED_POLICY, actor: { id: 1121490 }, updated_at: now }];
  const r = await reconcile(initialState(), s, now);
  assert.equal(r.alerts.length, 2); assert.match(r.alerts[0].text, /Current policy matches/);
  assert.equal((await reconcile(r.state, s, now)).alerts.length, 0);
});
test('new Admin and pending Admin invitation are distinct transitions; unchanged state is quiet', async () => {
  const s = snapshot(); s.invitations = [{ id: 17, login: 'new-admin' }];
  const invite = await reconcile(initialState(), s, now);
  assert.equal(invite.alerts.length, 1); assert.match(invite.alerts[0].text, /not active/);
  s.admins.push({ id: 99, login: 'new-admin' }); s.invitations = [];
  const active = await reconcile(invite.state, s, now);
  assert.equal(active.alerts.length, 1); assert.match(active.alerts[0].subject, /New Admin/);
  assert.equal((await reconcile(active.state, s, now)).alerts.length, 0);
  const revoked = await reconcile(active.state, snapshot(), now);
  assert.equal(revoked.alerts.length, 1); assert.match(revoked.alerts[0].subject, /revoked/);
});
test('signatures match the GitHub published golden vector and reject tampering', async () => {
  const secret = "It's a Secret to Everybody";
  const signature = 'sha256=757107ea0eb2509fc211221cce984b8a37570b6d7586c22c46f4379c8b043e17';
  assert.equal(await sign(secret, 'Hello, World!'), signature);
  assert.equal(await validSignature(secret, signature, 'Hello, World!'), true);
  assert.equal(await validSignature(secret, signature, 'Hello, world!'), false);
  assert.equal(await validSignature(secret, '', 'Hello, World!'), false);
});
test('unrelated repositories cannot trigger work; organization/team events can', () => {
  assert.equal(relevantEvent('member', { repository: { full_name: 'someone/else' }, organization: { login: 'matheconlib' } }), false);
  assert.equal(relevantEvent('membership', { organization: { login: 'matheconlib' } }), true);
  assert.equal(relevantEvent('issues', { repository: { full_name: 'matheconlib/matheconlib' } }), false);
});
test('public receiver rejects unsigned payloads without touching durable state', async () => {
  let touched = false;
  const r = await worker.fetch(new Request('https://alerts.example/webhook', { method: 'POST', body: '{}' }),
    { WEBHOOK_SECRET: 'secret', MONITOR: { idFromName() { touched = true; } } });
  assert.equal(r.status, 401); assert.equal(touched, false);
});
test('signed ping is accepted and duplicate IDs are idempotent', async () => {
  const storage = memoryStorage(), env = { WEBHOOK_SECRET: 'secret' }, monitor = new GovernanceMonitor({ storage }, env);
  env.MONITOR = { idFromName: x => x, get: () => ({ fetch: (...args) => monitor.fetch(new Request(...args)) }) };
  const body = '{}', headers = { 'x-hub-signature-256': await sign('secret', body), 'x-github-event': 'ping', 'x-github-delivery': 'test-ping-1' };
  assert.equal((await worker.fetch(new Request('https://alerts.example/webhook', { method: 'POST', headers, body }), env)).status, 202);
  const repeated = await worker.fetch(new Request('https://alerts.example/webhook', { method: 'POST', headers, body }), env);
  assert.deepEqual(await repeated.json(), { duplicate: true });
});
test('old signed backup requests are rejected', async () => {
  const body = JSON.stringify({ capturedAt: '2020-01-01', snapshot: snapshot() });
  const r = await worker.fetch(new Request('https://alerts.example/backup', { method: 'POST',
    headers: { 'x-hub-signature-256': await sign('secret', body) }, body }), { BACKUP_SECRET: 'secret' });
  assert.equal(r.status, 400);
});
function memoryStorage() {
  const data = new Map(); return { data, alarm: null, async get(k) { return copy(data.get(k)); },
    async put(k, v) { data.set(k, copy(v)); }, async delete(k) { data.delete(k); },
    async list({ prefix }) { return new Map([...data].filter(([k]) => k.startsWith(prefix)).map(([k, v]) => [k, copy(v)])); },
    async setAlarm(x) { this.alarm = x; },
    async transaction(fn) { const saved = copy(data); try { await fn(this); } catch (e) { data.clear(); for (const [k, v] of saved) data.set(k, v); throw e; } } };
}
test('failed email persists, retries, then deduplicates across a restarted instance', async () => {
  const storage = memoryStorage(); let attempts = 0, fail = true;
  const env = { ALERT_FROM: 'alerts@example.org', ALERT_TO: 'bo.cowgill.work@gmail.com', EMAIL: { async send(m) {
    attempts++; assert.equal(m.to, 'bo.cowgill.work@gmail.com'); if (fail) throw new Error('offline'); return { messageId: 'sent-1' };
  } } };
  let monitor = new GovernanceMonitor({ storage }, env);
  await monitor.enqueue({ key: 'one-change', subject: 'Test', text: 'Test', createdAt: now });
  await assert.rejects(monitor.flush(), /delivery failed/);
  assert.ok(storage.alarm); assert.equal([...storage.data.values()][0].sent, false);
  fail = false; monitor = new GovernanceMonitor({ storage }, env);
  await monitor.flush(); await monitor.enqueue({ key: 'one-change' }); await monitor.flush();
  assert.equal(attempts, 2); assert.equal([...storage.data.values()][0].providerId, 'sent-1');
});
test('a failed scheduled check returns failure and preserves the prior successful checkpoint', async () => {
  const storage = memoryStorage(), state = initialState(); state.lastSuccessfulCheck = now;
  await storage.put('state', state); let delivered = 0;
  const monitor = new GovernanceMonitor({ storage }, { ALERT_TO: 'bo.cowgill.work@gmail.com',
    EMAIL: { async send() { delivered++; return { messageId: 'failure-notice' }; } } });
  const r = await monitor.fetch(new Request('https://monitor.internal/reconcile', { method: 'POST' }));
  assert.equal(r.status, 503); assert.equal((await r.json()).checkedAt, now);
  assert.equal((await storage.get('state')).lastSuccessfulCheck, now); assert.equal(delivered, 1);
});
function fakeReader({ missingRule = false, partial = false } = {}) {
  const root = 'repos/matheconlib/matheconlib'; const calls = [];
  const read = async path => {
    calls.push(path);
    if (path === root) return { data: { permissions: { admin: true } } };
    if (path === `${root}/rulesets/26805968`) return missingRule ? { status: 404 } : { data: APPROVED_POLICY };
    if (path.includes('/rulesets?')) return { data: [] };
    if (path.includes('/history?')) return { data: [{ version_id: 56843070 }] };
    if (path.includes('/rules/branches')) return { data: [] };
    if (path.includes('/collaborators?')) return { data: APPROVED_ADMINS.map(a => ({ ...a, permissions: partial ? {} : { admin: true } })), next: 'https://api.github.com/second-page' };
    if (path.endsWith('/second-page')) return { data: [{ id: 19, login: 'writer', permissions: { admin: false } }] };
    if (path.includes('/invitations?')) return { data: [{ id: 1, permissions: 'write', invitee: { login: 'writer' } }, { id: 2, permissions: 'admin', invitee: { login: 'newadmin' } }] };
    throw new Error('Unexpected request: ' + path);
  }; return { read, calls };
}
test('authenticated collector follows pagination and ignores Write invitations', async () => {
  const { read, calls } = fakeReader(); const s = await collectSnapshot(read, [56843070]);
  assert.equal(s.admins.length, 3); assert.deepEqual(s.invitations, [{ id: 2, login: 'newadmin' }]);
  assert.ok(calls.includes('https://api.github.com/second-page'));
});
test('404 is checked against repository access and the ruleset list before deletion', async () => {
  const { read, calls } = fakeReader({ missingRule: true }); const s = await collectSnapshot(read);
  assert.equal(s.policy, null); assert.ok(calls.some(x => x.includes('/rulesets?')));
});
test('partial collaborator access fails without advancing any state', async () => {
  const { read } = fakeReader({ partial: true }); await assert.rejects(collectSnapshot(read, [56843070]), /incomplete/);
});
test('reader prevents credential forwarding to pagination URLs outside GitHub', async () => {
  let calls = 0; const read = githubReader('do-not-disclose', async () => { calls++; });
  await assert.rejects(read('https://example.com/steal'), /non-GitHub/); assert.equal(calls, 0);
});
test('read-only cloud snapshots do not call GitHub history endpoints requiring write access', async () => {
  const { read, calls } = fakeReader();
  await collectSnapshot(read, [56843070], { history: false });
  assert.equal(calls.some(x => x.includes('/history')), false);
});
test('signed rule events preserve a transient change and restoration without a history API', async () => {
  const disabled = { ...copy(APPROVED_POLICY), enforcement: 'disabled', updated_at: '2026-11-08T20:00:01Z' };
  const restored = { ...copy(APPROVED_POLICY), updated_at: '2026-11-08T20:00:02Z' };
  const events = await applySignals(initialState(), [{ id: 'a', event: 'repository_ruleset', action: 'edited', ruleset: disabled },
    { id: 'b', event: 'repository_ruleset', action: 'edited', ruleset: restored }], now);
  assert.equal(events.alerts.length, 2);
  assert.equal((await reconcile(events.state, snapshot(), now)).alerts.length, 0);
  const duplicate = await applySignals(events.state, [{ id: 'a', event: 'repository_ruleset', action: 'edited', ruleset: disabled }], now);
  assert.equal(duplicate.alerts.length, 0); assert.deepEqual(duplicate.state.observed.policy, APPROVED_POLICY);
  const history = snapshot(); history.history = [
    { version_id: 11, policy: disabled, updated_at: disabled.updated_at },
    { version_id: 12, policy: restored, updated_at: restored.updated_at }];
  assert.equal((await reconcile(events.state, history, now)).alerts.length, 0);
});
test('an ordinary event followed by its live snapshot sends one alert', async () => {
  const p = { ...copy(APPROVED_POLICY), enforcement: 'disabled', updated_at: now };
  const events = await applySignals(initialState(), [{ id: 'a', event: 'repository_ruleset', action: 'edited', ruleset: p }], now);
  assert.equal(events.alerts.length, 1);
  const s = snapshot(p); s.ruleUpdatedAt = now;
  assert.equal((await reconcile(events.state, s, now)).alerts.length, 0);
});
test('an incomplete rule event alerts safely, while a known name-only edit stays quiet', async () => {
  const rule = { id: 26805968, updated_at: now };
  assert.equal((await applySignals(initialState(), [{ id: 'a', event: 'repository_ruleset', action: 'edited', ruleset: rule }], now)).alerts.length, 1);
  assert.equal((await applySignals(initialState(), [{ id: 'b', event: 'repository_ruleset', action: 'edited', ruleset: rule, changes: { name: { from: 'old' } } }], now)).alerts.length, 0);
});
test('a direct Admin-grant event is reported even if the grant is already revoked at the snapshot', async () => {
  const event = { id: 'new-admin', event: 'member', action: 'edited', member: { id: 99, login: 'temporary-admin' }, permissionTo: 'admin', permissionFrom: 'write' };
  const events = await applySignals(initialState(), [event], now);
  assert.equal(events.alerts.length, 1);
  const result = await reconcile(events.state, snapshot(), now);
  assert.equal(result.alerts.length, 1); assert.match(result.alerts[0].subject, /revoked/);
});
test('mail bridge authenticates requests and requires a matching acknowledgment', async () => {
  const env = { MAIL_BRIDGE_URL: 'https://script.google.com/macros/s/test/exec', MAIL_BRIDGE_SECRET: 'secret' };
  let seen;
  const response = await sendEmail(env, { key: 'change-1', subject: '[MathEconLib governance] Test', text: 'An alert' }, async (url, options) => {
    assert.equal(url.origin, 'https://script.google.com'); seen = JSON.parse(options.body);
    assert.equal(await validSignature('secret', 'sha256=' + seen.signature, seen.payload), true);
    return Response.json({ sent: true, id: JSON.parse(seen.payload).id });
  });
  assert.equal(response.messageId, JSON.parse(seen.payload).id);
  await assert.rejects(sendEmail(env, { key: 'change-1' }, async () => Response.json({ sent: true, id: 'other' })), /acknowledge/);
});
test('Apps Script sender refuses forged messages, fixes recipient and deduplicates real retries', async () => {
  const data = { MAIL_BRIDGE_SECRET: 'secret' }, messages = [];
  const context = vm.createContext({ Date, Number, String, JSON, Error, Object, Utilities: {
    computeHmacSha256Signature: (body, secret) => [...createHmac('sha256', secret).update(body).digest()],
  }, PropertiesService: { getScriptProperties: () => ({ getProperty: k => data[k], setProperty: (k, v) => { data[k] = v; },
    getProperties: () => ({ ...data }), deleteProperty: k => { delete data[k]; } }) },
  LockService: { getScriptLock: () => ({ waitLock() {}, releaseLock() {} }) },
  MailApp: { sendEmail: x => messages.push(x) }, ContentService: { MimeType: { JSON: 'json' },
    createTextOutput: x => ({ setMimeType() { return x; } }) } });
  vm.runInContext(readFileSync(new URL('../gmail/Code.gs', import.meta.url), 'utf8'), context);
  const payload = JSON.stringify({ id: 'a'.repeat(64), subject: '[MathEconLib governance] Test', text: 'Test',
    to: 'attacker@example.com', createdAt: new Date().toISOString() });
  const call = signature => context.doPost({ postData: { contents: JSON.stringify({ payload, signature }) } });
  assert.throws(() => call('0'.repeat(64)), /Unauthorized/); assert.equal(messages.length, 0);
  const signature = (await sign('secret', payload)).slice(7);
  call(signature); call(signature);
  assert.equal(messages.length, 1); assert.equal(messages[0].to, 'bo.cowgill.work@gmail.com');
});
