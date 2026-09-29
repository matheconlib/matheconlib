# Reviewer and contributor tooling

The command-level companion to REVIEWING.md: that file says what a review
must check, this one says how to do each check cheaply. Everything here is
open source or a public service - no internal infrastructure.

Maintenance rule: every entry carries a "verified working" date. If an entry
stops working, delete it; do not maintain a museum. (Last full verification:
2026-09-10.)

## Library search and duplication sweeps

- **lean-lsp-mcp** (https://github.com/oOo0oOo/lean-lsp-mcp, MIT). The
  standard Lean MCP server: live goal states and diagnostics via LSP, plus
  Loogle, LeanSearch, Lean Finder, State Search, and Hammer as agent tools
  in one install.
  Install: `claude mcp add lean-lsp -- uvx lean-lsp-mcp` (configs for Codex,
  VSCode, Cursor in its README).
- **Loogle, locally against this repo** (https://github.com/nomeata/loogle).
  Loogle's CLI runs against any Lake project on the same toolchain, which
  gives type-signature search over THIS library, not just mathlib. This is
  the duplication sweep (review order, step 4) as a command.
  Hosted mathlib instance: https://loogle.lean-lang.org/json?q=... (JSON API).
- **LeanSearch** (https://leansearch.net): natural-language search over
  mathlib, no auth. **LeanExplore** (https://github.com/justincasher/lean-explore,
  `pip install lean-explore`): hybrid semantic search, MCP/CLI/Python, and a
  local mode that can index a private project.

## Prior art in the community

Before ruling on a naming or design convention, check whether mathlib already
debated it.

- **Zulip archive search, no credentials**: the public archive repo
  (https://github.com/leanprover-community/archive) holds the raw JSON of
  every public-stream message. `gh search code --repo
  leanprover-community/archive "your term"` finds the topic files; fetch any
  of them raw for the full thread. Read-only, no account, no API key;
  refreshes roughly monthly.
- Live search, if the lag matters: the Zulip REST API on
  leanprover.zulipchat.com with a personal key from a free account, or
  **zulook** (https://github.com/nikomatsakis/zulook), a read-only Zulip
  CLI/MCP server. Read-only access only; this tooling never posts.
- **mathlib GitHub prior art**: plain gh -
  `gh search prs --repo leanprover-community/mathlib4 "your term"`.
- mathlib's official AI contribution policy is on the community contribute
  pages (https://leanprover-community.github.io/contribute/index.html) -
  worth knowing when contributors arrive from mathlib.

## Build and lint when CI did not run

Stacked PRs skip CI (it triggers against main only), so the reviewer checks
out the exact commit named by the review surface, records it, and runs the
missing build there rather than at a moving branch tip:

    git clone <repo>
    cd <repo>
    git checkout --detach <reviewed-commit>
    git rev-parse HEAD
    lake exe cache get
    lake build

Compare the printed SHA with the reviewed commit before relying on any result.
For a young layer, inspect its compatibility pin before the build:

    rg '^import ' MathEconLibTest/<Layer>/Compatibility.lean

The pin imports only the layer's documented umbrella. Adding a leaf or
implementation import to make the examples compile defeats the check: a missing
export or public dependency should fail here. Build the pins explicitly when
investigating that boundary:

    lake build MathEconLibTest

Then the escape-hatch sweep over the diff: grep for `sorry`,
`native_decide`, `nolint`, `set_option linter`, `maxHeartbeats`, and
`public import Mathlib`. Compare the linter warning census against main.

## LLM-assisted review workflow

1. Load `REVIEWING.md` before inspecting the change. It is the sole source of
   review policy; this file only supplies procedures and commands. Use the PR,
   issue, and linked discussions to recover scope and decisions. Distinguish an
   explicitly accepted ruling or clear consensus from a proposal that remains
   open, and never promote the latter to policy.
2. Verify checkable claims at the exact reviewed commit recorded above. Cite the
   file and line, and attach the compilation, search, or diff evidence produced
   at that commit; do not mix in results from main or a later branch tip.
3. Sort the report before presenting it according to the classifications below.

Use these classifications:

- **Blocker:** the change violates policy, an accepted decision, or its stated
  mathematical or API contract and must be fixed in this PR.
- **Optional improvement:** useful within the present design, but not required
  for the PR's claims or scope.
- **Future redesign:** a broader change to architecture, abstractions, or API;
  move it to a design issue instead of making it a review condition.

The model supplies this grounded analysis. The human reviewer owns the design
judgment, verdict, and tone described in `REVIEWING.md`.

## Agent workflow packs

- **lean4-skills** (https://github.com/cameronfreer/lean4-skills, MIT):
  twelve Lean workflows for coding agents, including `review`, `refactor`,
  `golf`, and `diagnose`. Installs as a Claude Code marketplace plugin and
  as a native Codex plugin. Recommended entry path for a new reviewer:
  install it, put REVIEWING.md in context, run the `review` workflow on the
  PR, then apply your own judgment to what comes back.
- Watch list (not yet adopted): mathlib-quality
  (https://github.com/CBirkbeck/mathlib-quality), the Lean FRO's
  TauCetiReview, and LeanExplore local indexing of this repo.
