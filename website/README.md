# MathEconLib website

This directory contains the project's public website. It is built with
[Eleventy](https://www.11ty.dev/) and is deliberately separate from the Lean
build.

The deployed site is [mathecon.dev](https://mathecon.dev/).

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
`PATH_PREFIX=/auctionlib/ npm run build`. A custom domain or Cloudflare Workers
deployment uses the default `/` prefix.

## Cloudflare Workers deployment

The site is configured as a static-assets Worker named `matheconlib`. To deploy
it from a development machine after authenticating Wrangler:

```bash
npm run deploy
```

The GitHub Actions workflow at `.github/workflows/deploy_website.yaml` deploys the site whenever website changes reach `main` or the workflow is manually dispatched. It requires two GitHub Actions repository secrets:

- `CF_MATHECON_PASS`: a Cloudflare API token with Workers edit access
- `CF_MATHECON_ACCT`: the Cloudflare account ID that owns the Worker

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
