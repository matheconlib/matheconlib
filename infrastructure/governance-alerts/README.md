# MathEconLib governance email alerts

Recipient: **bo.cowgill.work@gmail.com**. Repository: **matheconlib/matheconlib**.

This is conventional JavaScript infrastructure, with no LLM calls. It never
changes GitHub collaborators, rules, or pull requests.

## Current state

The implementation and read-only backup have been tested locally. **Production
email alerts and scheduled backup are not active until the activation steps
below are completed and verified.** `GATES.md` records activation evidence.

The existing hourly Codex automation remains in **MEL: New Issues?** and now
covers issue and PR follow-ups only.

## Operation

- A Cloudflare Worker validates GitHub's SHA-256 HMAC signature and queues each
  accepted event in a durable object. Unrelated repositories are ignored.
- The durable object reads the actual ruleset, effective main rules,
  all collaborators including inherited access, and pending invitations.
- Changes to the seven-person merge allowlist, governing rule, and effective
  Admin access or pending Admin invitations become persistent pending emails.
  The initial approved state is quiet. Name-only edits and ordinary Write
  invitations are quiet. Signed rule-change payloads record intervening edits
  and reversals. Direct Admin grants with an explicit destination permission
  are recorded even when revoked before the next snapshot.
- A send-only Google Apps Script bridge sends to the single fixed recipient.
  It requires a signed, timestamped request; it does not read the inbox or
  accept an arbitrary recipient. Its durable message IDs suppress retries.
- A Cloudflare Cron Trigger runs the same authenticated reconciliation every
  fifteen minutes. `scripts/check.mjs` is also an independent local backup:
  it uses the existing `gh` login without exporting that personal credential
  and can additionally inspect the ruleset history.
  Signed uploads never advance a local checkpoint before acknowledgment.
- Failed or partial GitHub reads preserve the last successful checkpoint;
  monitoring failures and recoveries are emailed once per material transition.
  Pending emails survive restarts and retry after five minutes.

The approved baseline is ruleset **26805968**, active on `refs/heads/main`,
restricting updates, with only these individual pull-request exceptions:
`bocowgill`, `Ruizsolveall`, `scduko`, `peabrainiac`, `danlyng`, `morankor`,
`jjaassoonn`. The three approved Admins are Bo, Ruiz and Scott. The original
PR/CI ruleset **25759286** is not edited.

## Activation

1. Deploy `gmail/Code.gs` and `gmail/appsscript.json` as a Google Apps Script Web
   App owned by **bo.cowgill.work@gmail.com**, executing as the owner. The only
   OAuth scope is `script.send_mail`. The owner must authorize this new sender.
   Run `authorizeAndTest`, verify the test arrives, and obtain the script's
   `MAIL_BRIDGE_SECRET` through Script Properties. Do not paste secrets in chat.
   The endpoint must accept service requests without an interactive sign-in;
   every request is still authenticated by its HMAC.
2. Supply a fine-grained GitHub token scoped to **only this repository**, with
   **Administration: read** and the mandatory Metadata read permission. Use an
   organization-authorized token owned by an existing Admin so collaborator
   and invitation reads work. It needs no code-write or merge permissions.
   Store it only as the Worker's `GITHUB_READ_TOKEN` secret; do not copy the
   broad personal GitHub CLI token to cloud hosting.
3. Deploy `wrangler.json` using an authorized Cloudflare deployment connection.
   It creates a separate Worker and durable object; it does not change the
   website Worker or any personal domain's DNS. Store `WEBHOOK_SECRET`,
   `BACKUP_SECRET`, `MAIL_BRIDGE_URL`, `MAIL_BRIDGE_SECRET`, and
   `GITHUB_READ_TOKEN` as Worker secrets. The webhook/backup secrets should be
   independently generated random 32-byte values.
4. Create a signed **organization webhook** in `matheconlib` targeting the
   Worker's `/webhook` endpoint. Subscribe to `repository_ruleset`, `member`,
   `membership`, `organization`, `team`, `team_add`, `repository`, and `meta`.
   Filter to the target repository in the receiver. Repository-only hooks omit
   organization/team events. The current CLI connection lacks `admin:org_hook`;
   an organization owner must authorize that scope or create the hook in the UI.
5. Verify a real GitHub ping, rejection of an unsigned request, receipt of the
   test email, and a successful production reconciliation and Cron Trigger.
   Do not test by weakening production rules or granting a new Admin.

For the optional independent local backup, store `url` and `backupSecret` in
owner-readable `deployment.local.json` (ignored by Git), then run
`node scripts/check.mjs`. Schedule the same command only once it succeeds.
It requires the Mac to be awake; the cloud Cron Trigger does not.

## Validation

`node --test` exercises semantic changes, signature golden values and negative
cases, event filtering, paging, partial access, transient rule history,
restart-safe mail retries, and deduplication. `node scripts/check.mjs --dry-run`
performs authenticated live reads, prints only a summary, and sends no email.

## Limits

GitHub's history API requires Administration **write** even for GET requests.
The cloud credential deliberately remains read-only and does not call that
endpoint. The optional local backup can read history using the existing login.

GitHub webhooks are near real time, not a delivery-time guarantee. API snapshots
are not atomic. Without an accessible audit-event feed, an Admin grant that is
revoked before both the event-triggered read and backup check may be missed
when its event does not include the resulting role. Rule changes whose event
omits the full bypass list are flagged for inspection. The local history check
can recover missed rule edits while that history is accessible.
There is a narrow at-least-once email edge case if a sender succeeds but crashes
before its deduplication write. Expired credentials or mail quotas produce a
monitoring failure, not an empty access list. No paid plan is purchased and no
domain mail configuration is changed as part of this implementation.
