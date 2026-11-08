import assert from 'node:assert/strict';
import { collectSnapshot, githubReader } from '../src/github.mjs';
import { APPROVED_ADMINS, APPROVED_POLICY, stable } from '../src/core.mjs';
const snapshot = await collectSnapshot(githubReader(process.env.GITHUB_READ_TOKEN), [56843070], { history: false });
assert.equal(stable(snapshot.policy), stable(APPROVED_POLICY));
assert.equal(stable(snapshot.admins), stable(APPROVED_ADMINS));
assert.equal(snapshot.invitations.length, 0);
console.log('READ-ONLY GITHUB GOVERNANCE ACCESS VERIFIED');
assert.ok(process.env.CLOUDFLARE_ACCOUNT_ID && process.env.CLOUDFLARE_API_TOKEN, 'Cloudflare connection is missing.');
const r = await fetch(`https://api.cloudflare.com/client/v4/accounts/${process.env.CLOUDFLARE_ACCOUNT_ID}/workers/scripts`,
  { headers: { authorization: `Bearer ${process.env.CLOUDFLARE_API_TOKEN}` }, signal: AbortSignal.timeout(20000), redirect: 'error' });
assert.equal(r.status, 200, 'Cloudflare Workers read failed.');
const data = await r.json();
assert.equal(data.success, true);
assert.ok(Array.isArray(data.result) && data.result.some(s => s.id === 'matheconlib'), 'Expected the existing MathEconLib hosting account.');
console.log('EXISTING CLOUDFLARE WORKERS CONNECTION VERIFIED; NO CONFIGURATION CHANGED');
