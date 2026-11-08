import { REPO, RULE_URL, digest, failureNotice, initialState, reconcile, relevantEvent, sign, validSignature } from './core.mjs';
import { collectSnapshot, githubReader } from './github.mjs';

const json = (body, status = 200) => Response.json(body, { status, headers: { 'Cache-Control': 'no-store' } });
const allowedEvents = new Set(['ping', 'repository_ruleset', 'member', 'membership', 'organization', 'team', 'team_add', 'repository', 'meta']);
function stub(env) { return env.MONITOR.get(env.MONITOR.idFromName(REPO)); }
export async function sendEmail(env, message, fetcher = fetch) {
  if (env.EMAIL) return env.EMAIL.send({ from: env.ALERT_FROM, to: env.ALERT_TO, subject: message.subject, text: message.text });
  if (!env.MAIL_BRIDGE_URL || !env.MAIL_BRIDGE_SECRET) throw new Error('Gmail alert sender is not configured.');
  const url = new URL(env.MAIL_BRIDGE_URL);
  if (url.origin !== 'https://script.google.com' || !url.pathname.endsWith('/exec')) throw new Error('Invalid Gmail bridge URL.');
  const id = await digest(message.key);
  const payload = JSON.stringify({ id, subject: message.subject, text: message.text, createdAt: new Date().toISOString() });
  const response = await fetcher(url, { method: 'POST', headers: { 'content-type': 'application/json' },
    body: JSON.stringify({ payload, signature: (await sign(env.MAIL_BRIDGE_SECRET, payload)).slice(7) }), signal: AbortSignal.timeout(25000) });
  if (!response.ok) throw new Error('Gmail bridge request failed.');
  const result = await response.json();
  if (result.sent !== true || result.id !== id) throw new Error('Gmail bridge did not acknowledge this alert.');
  return { messageId: id };
}
async function boundedBody(request) {
  if (Number(request.headers.get('content-length') || 0) > 262144) throw new Error('Body too large.');
  const reader = request.body?.getReader();
  if (!reader) return '';
  const chunks = []; let size = 0;
  while (true) {
    const { done, value } = await reader.read(); if (done) break;
    size += value.length;
    if (size > 262144) { await reader.cancel(); throw new Error('Body too large.'); }
    chunks.push(value);
  }
  const bytes = new Uint8Array(size); let offset = 0;
  for (const c of chunks) { bytes.set(c, offset); offset += c.length; }
  return new TextDecoder('utf-8', { fatal: true }).decode(bytes);
}
export default {
  async fetch(request, env) {
    const path = new URL(request.url).pathname;
    if (path === '/health' && request.method === 'GET') return json({ service: 'MathEconLib governance alerts' });
    if (!['/webhook', '/backup', '/test'].includes(path) || request.method !== 'POST') return json({ error: 'Not found.' }, 404);
    let raw;
    try { raw = await boundedBody(request); } catch { return json({ error: 'Invalid or excessive body.' }, 413); }
    const secret = path === '/webhook' ? env.WEBHOOK_SECRET : env.BACKUP_SECRET;
    if (!await validSignature(secret, request.headers.get('x-hub-signature-256'), raw)) return json({ error: 'Invalid signature.' }, 401);
    let body; try { body = JSON.parse(raw); } catch { return json({ error: 'Invalid JSON.' }, 400); }
    if (path === '/webhook') {
      const event = request.headers.get('x-github-event');
      const id = request.headers.get('x-github-delivery');
      if (!id || !/^[a-zA-Z0-9-]{1,80}$/.test(id)) return json({ error: 'Missing delivery ID.' }, 400);
      if (!allowedEvents.has(event) || !relevantEvent(event, body)) return json({ ignored: true });
      return stub(env).fetch('https://monitor.internal/event', { method: 'POST', body: JSON.stringify({ id,
        event, action: body.action, actor: body.sender?.login, test: event === 'ping' }) });
    }
    // Timestamped admin requests prevent an old signed snapshot being replayed.
    const age = Date.now() - Date.parse(body.capturedAt);
    if (!Number.isFinite(age) || age < -60000 || age > 300000) return json({ error: 'Expired request.' }, 400);
    return stub(env).fetch(`https://monitor.internal${path}`, { method: 'POST', body: raw });
  },
  async scheduled(_event, env, context) {
    context.waitUntil(stub(env).fetch('https://monitor.internal/reconcile', { method: 'POST' }).then(r => {
      if (!r.ok) throw new Error('Scheduled governance check failed.');
    }));
  },
};

export class GovernanceMonitor {
  constructor(ctx, env) { this.ctx = ctx; this.env = env; this.serial = Promise.resolve(); }
  exclusive(fn) {
    const result = this.serial.then(fn); this.serial = result.catch(() => {}); return result;
  }
  fetch(request) { return this.exclusive(() => this.handle(request)); }
  alarm() { return this.exclusive(() => this.run()); }
  async handle(request) {
    const path = new URL(request.url).pathname;
    if (path === '/event') {
      const signal = await request.json();
      const key = `receipt:${signal.id}`;
      if (await this.ctx.storage.get(key)) return json({ duplicate: true });
      // Durable queue first; GitHub gets a fast acceptance without waiting for API/email.
      await this.ctx.storage.put(key, { ...signal, receivedAt: new Date().toISOString(), processed: false });
      await this.ctx.storage.setAlarm(Date.now() + 1000);
      return json({ accepted: true }, 202);
    }
    if (path === '/backup') {
      const body = await request.json();
      const state = await this.ctx.storage.get('state') || initialState();
      if (state.lastSuccessfulCheck && body.capturedAt < state.lastSuccessfulCheck) return json({ stale: true });
      const result = await reconcile(state, body.snapshot, body.capturedAt);
      await this.commit(result); await this.flush();
      return json({ checkedAt: result.state.lastSuccessfulCheck, alerts: result.alerts.length });
    }
    if (path === '/test') {
      await this.enqueue({ key: 'setup-test:' + await digest(await request.text()),
        subject: '[MathEconLib governance] Alert delivery test',
        text: `This is the requested MathEconLib governance alert setup test.\n\nFuture alerts cover merge-allowlist changes, changes or deletion of the governing rule, and new Admin access/invitations.\n\n${RULE_URL}`, createdAt: new Date().toISOString() });
      await this.flush(); return json({ sent: true });
    }
    if (path === '/reconcile') {
      await this.run(); return json({ checked: true });
    }
    return json({ error: 'Not found.' }, 404);
  }
  async enqueue(alert) {
    const key = `mail:${await digest(alert.key)}`;
    if (!await this.ctx.storage.get(key)) await this.ctx.storage.put(key, { ...alert, sent: false });
  }
  async commit(result) {
    // Observations and durable pending emails must be committed together: a
    // restart cannot advance a checkpoint and lose its unsent notification.
    await this.ctx.storage.transaction(async txn => {
      for (const alert of result.alerts) {
        const key = `mail:${await digest(alert.key)}`;
        if (!await txn.get(key)) await txn.put(key, { ...alert, sent: false });
      }
      await txn.put('state', result.state);
    });
  }
  async run() {
    const now = new Date().toISOString();
    let state = await this.ctx.storage.get('state') || initialState();
    try {
      const snapshot = await collectSnapshot(githubReader(this.env.GITHUB_READ_TOKEN), state.historySeen);
      const result = await reconcile(state, snapshot, now);
      await this.commit(result);
      state = result.state;
      const receipts = await this.ctx.storage.list({ prefix: 'receipt:' });
      for (const [key, receipt] of receipts) {
        if (!receipt.processed && receipt.test) await this.enqueue({ key: `github-ping:${receipt.id}`,
          subject: '[MathEconLib governance] GitHub webhook connected',
          text: `GitHub delivered a signed webhook ping. Authenticated baseline checks completed at ${now}.\n\n${RULE_URL}`, createdAt: now });
        if (!receipt.processed) await this.ctx.storage.put(key, { ...receipt, processed: true });
      }
    } catch (error) {
      const alert = failureNotice(error, now);
      // A failure notice does not advance the successful checkpoint.
      if (state.failure !== error.message) {
        state.failure = error.message;
        await this.commit({ state, alerts: [alert] });
      }
      await this.ctx.storage.setAlarm(Date.now() + 300000);
      console.error('Governance snapshot failed; checkpoint preserved.');
    }
    await this.flush();
    await this.cleanup();
  }
  async flush() {
    const messages = await this.ctx.storage.list({ prefix: 'mail:' });
    for (const [key, message] of messages) {
      if (message.sent) continue;
      try {
        const result = await sendEmail(this.env, message);
        await this.ctx.storage.put(key, { ...message, sent: true, sentAt: new Date().toISOString(), providerId: result?.messageId || null });
      } catch {
        await this.ctx.storage.setAlarm(Date.now() + 300000);
        console.error('Governance email is pending; retry scheduled.');
        throw new Error('Email delivery failed; durable retry is scheduled.');
      }
    }
  }
  async cleanup() {
    const cutoff = Date.now() - 180 * 86400000;
    for (const prefix of ['mail:', 'receipt:']) {
      const records = await this.ctx.storage.list({ prefix });
      for (const [key, value] of records) {
        if ((value.sent || value.processed) && Date.parse(value.sentAt || value.receivedAt) < cutoff) await this.ctx.storage.delete(key);
      }
    }
  }
}
