import assert from 'node:assert/strict';
import { collectSnapshot, githubReader } from '../src/github.mjs';
import { APPROVED_ADMINS, APPROVED_POLICY, stable } from '../src/core.mjs';

for (const name of ['GITHUB_READ_TOKEN', 'WEBHOOK_SECRET', 'BACKUP_SECRET', 'MAIL_BRIDGE_URL', 'MAIL_BRIDGE_SECRET']) {
  assert.ok(process.env[name], `Missing deployment secret ${name}.`);
}
assert.ok(process.env.WEBHOOK_SECRET.length >= 32, 'Use a strong webhook secret.');
assert.ok(process.env.BACKUP_SECRET.length >= 32, 'Use a strong backup secret.');
assert.notEqual(process.env.WEBHOOK_SECRET, process.env.BACKUP_SECRET, 'Keep webhook and backup keys independent.');
const bridge = new URL(process.env.MAIL_BRIDGE_URL);
assert.equal(bridge.origin, 'https://script.google.com');
assert.ok(bridge.pathname.endsWith('/exec'));
const snapshot = await collectSnapshot(githubReader(process.env.GITHUB_READ_TOKEN), [56843070]);
assert.equal(stable(snapshot.policy), stable(APPROVED_POLICY), 'The current merge policy differs from the approved baseline; review before activation.');
assert.equal(stable(snapshot.admins), stable(APPROVED_ADMINS), 'Admin accounts differ from the approved baseline; review before activation.');
assert.equal(snapshot.invitations.length, 0, 'Review pending Admin invitations before activation.');
console.log('DEPLOYMENT READ-ACCESS AND BASELINE CHECK PASSED');
