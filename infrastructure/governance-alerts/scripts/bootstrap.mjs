import assert from 'node:assert/strict';

// Initialize only the separately named Worker if it is missing. Existing
// deployments are left untouched until the tested code and secrets are ready.
const name = 'matheconlib-governance-alerts';
const account = process.env.CLOUDFLARE_ACCOUNT_ID;
const token = process.env.CLOUDFLARE_API_TOKEN;
assert.ok(token, 'Cloudflare deployment connection is missing.');
assert.equal(account, '2d76bd1b19fcf132d3acb21c49dd7cf0', 'Wrong governance-monitor hosting account.');
const base = `https://api.cloudflare.com/client/v4/accounts/${account}/workers/scripts`;
const headers = { authorization: `Bearer ${token}` };
const existing = await fetch(base, { headers, signal: AbortSignal.timeout(20000), redirect: 'error' });
assert.equal(existing.status, 200, 'Cannot inspect existing Workers.');
const list = await existing.json();
assert.equal(list.success, true);
assert.ok(Array.isArray(list.result));
if (list.result.some(worker => worker.id === name)) {
  console.log('Governance Worker already exists; bootstrap made no changes.');
} else {
  const body = new FormData();
  body.set('metadata', new Blob([JSON.stringify({ main_module: 'bootstrap.mjs', compatibility_date: '2026-11-08' })], { type: 'application/json' }));
  body.set('bootstrap.mjs', new Blob(['export default { fetch() { return new Response("Governance monitor setup in progress.", {status:503}); } };'], { type: 'application/javascript+module' }), 'bootstrap.mjs');
  const response = await fetch(`${base}/${name}`, { method: 'PUT', headers, body, signal: AbortSignal.timeout(30000), redirect: 'error' });
  const result = await response.json();
  if (!response.ok || !result.success) throw new Error(`Governance Worker initialization failed: HTTP ${response.status}; ${JSON.stringify(result.errors)}`);
  console.log('Created inert governance Worker; no schedule or website changed.');
}
