import { execFile } from 'node:child_process';
import { promisify } from 'node:util';
import { readFile, writeFile } from 'node:fs/promises';
import { fileURLToPath } from 'node:url';
import { dirname, resolve } from 'node:path';
import { collectSnapshot } from '../src/github.mjs';
import { initialState, reconcile, sign } from '../src/core.mjs';
const exec = promisify(execFile);
const root = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const dry = process.argv.includes('--dry-run');
const capturedAt = new Date().toISOString();
let previous;
try { previous = JSON.parse(await readFile(resolve(root, 'backup-state.json'), 'utf8')); }
catch (e) { if (e.code !== 'ENOENT') throw e; previous = initialState(); }
async function read(path) {
  const url = new URL(path, 'https://api.github.com/');
  if (url.origin !== 'https://api.github.com') throw new Error('Refused non-GitHub URL.');
  let output;
  try { ({ stdout: output } = await exec(process.env.GH_BIN || '/opt/homebrew/bin/gh', ['api', '--hostname', 'github.com', '--method', 'GET', '--include', url.pathname + url.search], { timeout: 20000, maxBuffer: 8 * 1024 * 1024 })); }
  catch (e) { if (/HTTP[^\n]*\b404\b/.test(e.stdout || '')) return { status: 404 }; throw new Error('Authenticated GitHub CLI read failed for ' + url.pathname); }
  const separator = output.search(/\r?\n\r?\n/);
  if (separator < 0) throw new Error('Unrecognized GitHub CLI response.');
  const headers = output.slice(0, separator), data = JSON.parse(output.slice(separator).trim());
  return { status: 200, data, next: headers.match(/^link:.*?<([^>]+)>; rel="next"/im)?.[1] };
}
const snapshot = await collectSnapshot(read, previous.historySeen);
const result = await reconcile(previous, snapshot, capturedAt);
if (dry) {
  console.log(JSON.stringify({ authenticated: true, admins: snapshot.admins.map(a => a.login),
    pendingAdminInvitations: snapshot.invitations.length, newHistoryVersions: snapshot.history.length,
    wouldAlert: result.alerts.map(a => a.subject) }));
  console.log('AUTHENTICATED BACKUP DRY RUN PASSED');
} else {
  const config = JSON.parse(await readFile(resolve(root, 'deployment.local.json'), 'utf8'));
  const url = new URL('/backup', config.url);
  if (url.protocol !== 'https:') throw new Error('Backup endpoint must use HTTPS.');
  const body = JSON.stringify({ capturedAt, snapshot });
  const r = await fetch(url, { method: 'POST', redirect: 'error',
    headers: { 'content-type': 'application/json', 'x-hub-signature-256': await sign(config.backupSecret, body) }, body, signal: AbortSignal.timeout(30000) });
  if (!r.ok) throw new Error('Backup receiver rejected the check: HTTP ' + r.status);
  const ack = await r.json();
  if (ack.stale !== true && !ack.checkedAt) throw new Error('Backup acknowledgment is incomplete.');
  if (!ack.stale) await writeFile(resolve(root, 'backup-state.json'), JSON.stringify(result.state, null, 2) + '\n', { mode: 0o600 });
  console.log('Governance backup accepted: ' + (ack.checkedAt || 'newer check already exists'));
}
