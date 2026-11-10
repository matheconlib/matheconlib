# MathEconLib website

This directory contains the project's public website. It is built with
[Eleventy](https://www.11ty.dev/) and is deliberately separate from the Lean
build.

Production deployment is configured for [mathecon.dev](https://mathecon.dev/).

## Local development

```bash
cd website
npm install
npm run dev
```

Eleventy serves the site at `http://localhost:8080/` by default.

## Production build

```bash
npm run build
```

The generated static files are written to `website/_site/`. For a GitHub Pages
project URL, set `PATH_PREFIX` to the repository path when building, for example
`PATH_PREFIX=/matheconlib/ npm run build`. A custom domain or Cloudflare Workers
deployment uses the default `/` prefix.

## Cloudflare Workers deployment

The site is configured as a static-assets Worker named `matheconlib`. To deploy
it from a development machine after authenticating Wrangler:

```bash
npm run deploy
```

The GitHub Actions workflow at `.github/workflows/deploy_website.yaml` deploys
the site whenever website changes reach `main` or the workflow is manually
dispatched. Merging this configuration into `main` triggers deployment; wait
for the required content and launch approvals before merging. It requires
two GitHub Actions repository secrets:

- `CF_MATHECON_PASS`: a Cloudflare API token with Workers edit access
- `CF_MATHECON_ACCT`: the Cloudflare account ID that owns the Worker

## API documentation route

The Worker script in `worker/index.js` serves `/docs/` from the R2 bucket bound as `DOCS`; every other path is served from `_site`. The API reference and signature index are linked from the home page and repository README. The Lean CI workflow publishes the API HTML and signature index to that bucket from `main`. The bucket must exist before the site is deployed. Under `npm run preview:worker`, the route reads Wrangler's local R2 simulation, which is empty unless objects are added with `wrangler r2 object put --local`.

The bucket stores the current and previous HTML trees plus `current.json` under `matheconlib/html/`. Main-branch database snapshots live under `matheconlib/snapshots/` and are retained for 90 days by an R2 lifecycle rule. Tagged-release snapshots under `matheconlib/releases/<tag>/` are kept indefinitely. Neither releases nor HTML have a lifecycle expiration rule. Configure snapshot expiration with:

```sh
npx wrangler r2 bucket lifecycle add matheconlib-docs expire-snapshots matheconlib/snapshots/ --expire-days 90
```

The working project name and shared metadata are kept in
`src/_data/site.json`, so the site can be renamed without editing every page.

## 404 artwork

The 404 page displays three abstract compositions, `ps`, `gb`, and `ka`.
The inline SVG partials in `src/_includes/404/` are the canonical artwork.
Edit these partials directly; there are no separate image files or generation step.

Each composition consists of SVG units that wrap without splitting. All pieces
share 15px squares, shrinking together only when the longest unit would exceed
the available width. Horizontal gaps are one square wide, row gaps are half a
square, and compositions are separated by 24px. Rendering requires no JavaScript
or image requests.

`art.njk` sets the composition order and `--longest-unit` (the maximum number of
squares in a unit). Each SVG declares its own `--unit-cells` and matching
`viewBox`. Keep these values consistent when editing. Layout styles live in
`art.css.njk`.
