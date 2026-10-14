# Beginner walkthrough — 8 October 2026

Preparatory verification for [launch checklist #78](https://github.com/matheconlib/matheconlib/issues/78).
Repeat the release checks against the final public repository and release commit.

## Revision and environment

- Source revision: [`c816d6fc40f04b157bf1222b2b90e4264a2aec7f`](https://github.com/matheconlib/matheconlib/commit/c816d6fc40f04b157bf1222b2b90e4264a2aec7f),
  current `main` when the walkthrough began.
- Lean: `4.28.0`, commit `7e01a1bf5c70fc6167d49c345d3bf80596e9a79b`;
  Lake: `5.0.0-src+7e01a1b`; platform: macOS, Apple silicon.
- Mathlib: `8f9d9cff6bd728b17a24e163c9402775d9e6a365`, as pinned in
  `lake-manifest.json`.
- A fresh GitHub clone initially had no `.lake/`. Dependencies were fetched
  through `lake exe cache get`; no other checkout's build directory was linked
  or copied into it. The machine already had elan, the pinned toolchain, VS Code,
  and the Lean extension, plus Mathlib's compressed download cache.
- GitHub authentication was required because the repository was still internal.
  This run does not certify signed-out access or a first installation of the editor.

## Reproduce the build

Authenticate Git for the private repository, then run. These commands use the
post-transfer URL; the recorded results below remain the 8 October verification
of the source revision above.

```bash
git clone --branch main --single-branch https://github.com/matheconlib/matheconlib.git
cd matheconlib
git checkout --detach c816d6fc40f04b157bf1222b2b90e4264a2aec7f
git rev-parse HEAD
lean --version
lake --version
lake exe cache get
bash scripts/update-imports.sh
git diff --exit-code -- MathEconLib.lean MathEconLibTest.lean
lake build
lake build MathEconLibTest.Manual.HandsOn
bash scripts/update-imports.sh --check
```

| Step | Result |
|---|---|
| Dependency and cache retrieval | Passed in 390.59 seconds; fetched dependency sources, built the cache utility, and restored 8,007 artifacts from the local compressed cache |
| Import regeneration and validation | Passed in 12.45 seconds; all four generator runs reported no update necessary; no generated diff |
| First full project build | Passed in 46.55 seconds, 8,105 jobs; included API pins, tests, and `MathEconLibTest.Manual.HandsOn` |
| Explicit hands-on target | Passed |
| Final import validation and incremental build | Passed |

Times describe this machine and cache state, not a setup-time guarantee. Existing
library linter warnings did not prevent the build; no Lean source was changed.

## Exercise checks and corrections

Scratch files under the ignored `MathEconLib/Playground/` directory checked the
first arithmetic example, the renamed library import and projections, the actual
`exact?` search, and the Part 5 proof. Live Lean language-server queries matched
each printed Part 5 goal and confirmed no goals remained after the final line.
The manual's local file links all resolved.

Twenty-one deliberate-failure variants were also run separately, covering
arithmetic, punctuation, a name collision, tactic selection, unapplied hypotheses,
invalid or missing proof fields, global versus restricted properties, omitted
`simp` attributes, noncomputable definitions, proof order, and search limitations.
Each failed for the intended reason. In particular, `exact?` succeeded on the
product of nonnegative reals and failed on the interval-membership example, both
before and after rewriting its hypothesis.

Three instruction corrections followed from the walkthrough:

1. Distinguish dependency/cache retrieval from compilation of MathEconLib.
2. In Hands-on 0, place the library import at the top of the scratch file.
   Appending it after the first exercise produced the invalid-import error;
   moving it to the top compiled successfully.
3. In Exercise 2, the unchanged clamp proof first produces a type mismatch.
   Replacing the proof with the documented `norm_num` variant produced the
   advertised `⊢ False`.

VS Code and its Lean extension were present. Native editor automation was
interrupted by window-state changes, so keyboard entry and the graphical
InfoView were not independently certified in this run. The compiled examples
and live language-server goal checks above passed.
