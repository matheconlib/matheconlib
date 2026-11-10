# Agent notes

## Declaration signatures

The [API reference](https://mathecon.dev/docs/) documents public declarations. The [signature index](https://mathecon.dev/docs/signatures/README.md) links a Markdown file for each top-level module. Download the index and every Markdown file it links into a scratch directory, then search with `rg`:

```sh
scratch=$(mktemp -d)
base=https://mathecon.dev/docs/signatures
curl -fsSL "$base/README.md" -o "$scratch/README.md"
for file in $(sed -n 's/.*](\([^)]*\.md\)).*/\1/p' "$scratch/README.md"); do
  mkdir -p "$scratch/$(dirname "$file")"
  curl -fsSL "$base/$file" -o "$scratch/$file"
done
rg 'declaration_name|signature_pattern' "$scratch"
```

The index's `Source revision:` line identifies the source commit. From the checkout, run `bash scripts/docs-inputs-changed.sh <revision> "$(git rev-parse HEAD)"`: exit 1 means the signatures match the checkout's library sources and documentation inputs; exit 0 means they differ, so read the Lean sources for anything changed; exit 2 means the comparison failed. The Lean sources in the checkout are authoritative.
