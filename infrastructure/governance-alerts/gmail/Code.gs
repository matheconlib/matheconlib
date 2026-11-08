/** Send only MathEconLib governance alerts to Bo's specified work address.
 * Deploy as a Web App executing as bo.cowgill.work@gmail.com.
 * The shared secret is stored in Script Properties, never in this source.
 */
function doPost(event) {
  const envelope = JSON.parse(event.postData.contents);
  const properties = PropertiesService.getScriptProperties();
  const secret = properties.getProperty('MAIL_BRIDGE_SECRET');
  if (!secret || typeof envelope.payload !== 'string' || envelope.payload.length > 40000) throw new Error('Invalid request.');
  const expected = Utilities.computeHmacSha256Signature(envelope.payload, secret).map(function (x) {
    return ('0' + ((x + 256) % 256).toString(16)).slice(-2);
  }).join('');
  const signature = String(envelope.signature || '');
  if (signature.length !== 64) throw new Error('Unauthorized.');
  let different = 0;
  for (let i = 0; i < 64; i++) different |= expected.charCodeAt(i) ^ signature.charCodeAt(i);
  if (different) throw new Error('Unauthorized.');
  const message = JSON.parse(envelope.payload);
  const age = Date.now() - Date.parse(message.createdAt);
  if (!Number.isFinite(age) || age < -60000 || age > 300000 || !/^[a-f0-9]{64}$/.test(message.id)) throw new Error('Expired or invalid message.');
  if (!String(message.subject).startsWith('[MathEconLib governance] ') || String(message.subject).length > 250 || String(message.text).length > 30000) throw new Error('Invalid alert.');
  const lock = LockService.getScriptLock();
  lock.waitLock(20000);
  try {
    const key = 'sent:' + message.id;
    if (!properties.getProperty(key)) {
      MailApp.sendEmail({ to: 'bo.cowgill.work@gmail.com', subject: message.subject, body: message.text,
        name: 'MathEconLib governance alerts' });
      properties.setProperty(key, String(Date.now()));
    }
    // Retain identifiers for six months; no email contents are stored.
    const all = properties.getProperties();
    Object.keys(all).filter(function (k) { return k.startsWith('sent:') && Number(all[k]) < Date.now() - 180 * 86400000; })
      .forEach(function (k) { properties.deleteProperty(k); });
    return ContentService.createTextOutput(JSON.stringify({ sent: true, id: message.id })).setMimeType(ContentService.MimeType.JSON);
  } finally { lock.releaseLock(); }
}

/** Run once as the owner to request send-only Gmail authorization and test delivery.
 * Read or write access to the Gmail inbox is not requested.
 */
function authorizeAndTest() {
  const properties = PropertiesService.getScriptProperties();
  if (!properties.getProperty('MAIL_BRIDGE_SECRET')) properties.setProperty('MAIL_BRIDGE_SECRET', Utilities.getUuid() + Utilities.getUuid());
  MailApp.sendEmail({ to: 'bo.cowgill.work@gmail.com', subject: '[MathEconLib governance] Gmail sender test',
    body: 'This is the requested sender test for MathEconLib governance alerts. Alerts will cover changes to the merge allowlist, disabling or deleting the main protection rule, and new Admin grants.\n\nhttps://github.com/matheconlib/matheconlib/rules/26805968', name: 'MathEconLib governance alerts' });
}
