// Serve the generated API documentation from R2 under /docs/. Only paths listed
// in `assets.run_worker_first` reach this script; everything else is a static
// asset. CI uploads each documentation tree and then points current.json at it.

const DOCS = "/docs/";
const POINTER = "matheconlib/html/current.json";
const POINTER_TTL_MS = 60_000;
const CONTENT_TYPES = {
  css: "text/css; charset=utf-8",
  html: "text/html; charset=utf-8",
  js: "text/javascript; charset=utf-8",
  json: "application/json",
  md: "text/markdown; charset=utf-8",
  svg: "image/svg+xml",
};

let pointer = null;

async function currentPrefix(bucket) {
  if (pointer && pointer.expires > Date.now()) return pointer.prefix;
  const object = await bucket.get(POINTER);
  if (!object) return null;
  const { prefix } = await object.json();
  pointer = { prefix, expires: Date.now() + POINTER_TTL_MS };
  return prefix;
}

export default {
  async fetch(request, env) {
    const url = new URL(request.url);
    if (url.pathname === "/docs") {
      return Response.redirect(`${url.origin}${DOCS}${url.search}`, 301);
    }
    if (!url.pathname.startsWith(DOCS)) return env.ASSETS.fetch(request);
    if (request.method !== "GET" && request.method !== "HEAD") {
      return new Response(null, { status: 405, headers: { Allow: "GET, HEAD" } });
    }

    let path;
    try {
      path = decodeURIComponent(url.pathname.slice(DOCS.length));
    } catch {
      return new Response("Bad Request", { status: 400 });
    }
    if (path === "" || path.endsWith("/")) path += "index.html";

    const prefix = await currentPrefix(env.DOCS);
    const object = prefix && (await env.DOCS.get(prefix + path, { onlyIf: request.headers }));
    // Static assets have nothing under /docs/, so this renders the site's 404 page.
    if (!object) return env.ASSETS.fetch(request);

    const headers = new Headers();
    object.writeHttpMetadata(headers);
    headers.set("ETag", object.httpEtag);
    headers.set("Cache-Control", "public, max-age=300");
    const type = CONTENT_TYPES[path.slice(path.lastIndexOf(".") + 1)];
    if (type) headers.set("Content-Type", type);
    // R2 omits the body when a conditional request's precondition fails.
    if (!("body" in object)) return new Response(null, { status: 304, headers });
    return new Response(request.method === "HEAD" ? null : object.body, { headers });
  },
};
