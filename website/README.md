# MathEconLib website

This directory contains the project's public website. It is built with
[Eleventy](https://www.11ty.dev/) and is deliberately separate from the Lean
build.

The deployed site is [matheconlib.bo-cowgill.workers.dev](https://matheconlib.bo-cowgill.workers.dev/).

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

The GitHub Actions workflow at `.github/workflows/deploy_website.yaml` deploys
the site whenever website changes reach `main`. It requires two GitHub Actions
repository secrets:

- `CLOUDFLARE_API_TOKEN`: a Cloudflare API token with Workers edit access
- `CLOUDFLARE_ACCOUNT_ID`: the Cloudflare account ID that owns the Worker

The default Cloudflare address is
`https://matheconlib.bo-cowgill.workers.dev`. A custom domain can be attached
later without changing the website source.

The working project name and shared metadata are kept in
`src/_data/site.json`, so the site can be renamed without editing every page.

## Design provenance

The homepage design derives from Moran Koren's
[MathEconLib proposal](https://github.com/morankor/MathEconLib). The
[design-proposal inventory](design-proposals/README.md) records the imported
sources and revision.
