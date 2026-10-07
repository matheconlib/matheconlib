# Contributing to auctionlib

Thanks for contributing! This is a short guide to how changes land in this repository.

New to Lean 4 or to this library? Start with
[*Lean 4 and `auctionlib` — A Beginner's Manual*](docs/BeginnersManual.md),
which covers the toolchain, the editor loop, and how to read the library's
core files. Small, well-scoped additions to `ForMathlib/` can be suitable first
contributions; the folder also contains substantial results.

## Design first for core layers

The project-wide framework for choosing abstractions, theorem scope,
transformations, and public interfaces lives in
[`DESIGN.md`](DESIGN.md).

Changes to the foundational layers — `Mechanism/`, `BidderProblem/`, `GameTheory/`,
`Auction/Basic.lean` — or the introduction of a new foundational layer start with a
**design issue** before implementation. Sketch the intended definitions and the main
statements, and get agreement on the shape before writing the proofs.

Leaf contributions — new theorems in existing chapters, documentation, applications
built on the existing layers — can go straight to a PR.

## ForMathlib and upstream contributions

`ForMathlib/` contains general mathematical definitions and results needed by
MathEconLib that are missing from the Mathlib version we use and may be suitable
for upstream contribution. Keep this material independent of economics-specific
definitions, follow Mathlib conventions, and check for existing results before
adding duplicates. Economic models and economics-specific definitions and
theorems belong in the relevant topic folders.

Contributors are encouraged to submit suitable material to Mathlib when they
have the time and interest. Placement in `ForMathlib/` does not imply a commitment
to submit it, a deadline, or guaranteed acceptance. Upstream submission is not
required before merging into MathEconLib; the code must meet our usual review and
build requirements. Link any upstream PR from the corresponding file. Once an
upstream result is available in our Mathlib dependency, replace the local
duplicate through a reviewed change. A volunteer can open or select a scoped
issue to coordinate an upstream contribution.

## Public API

The statements, names, hypotheses, and binder names of existing public declarations
are API. Downstream files and external users rely on them, so any change to them —
however small — is called out explicitly in the PR description, with a sentence on
why the change is needed.

Following the naming ruling in #45, general carrier structures keep short names in
a sufficiently specific namespace, such as `Auction` or `MatchingWithContracts.Market`.
Behavioral, optimality, and normalization predicates instead use precise,
setting-specific names that state the condition they impose. If two carriers with
the same short name routinely co-occur, distinguish the carrier names too.

## Verification bar

Every PR must satisfy:

- `lake build` is green.
- No `sorry`, `admit`, or `native_decide` anywhere in the change.
- `#print axioms` on new main results shows only `propext`, `Classical.choice`,
  and `Quot.sound`.
- Both library and test imports are regenerated and verified with
  `bash scripts/update-imports.sh`.

From the repository root, use:

```bash
lake exe cache get                 # first checkout, or after a dependency/toolchain change
git add path/to/NewFile.lean        # if adding a file: --git reads tracked/staged paths
bash scripts/update-imports.sh      # regenerate both root import files, then verify them
lake build                         # includes API pins and AuctionlibTest/Manual/HandsOn.lean
```

Omit the `git add` line if you have not added a file. Include changes to
`Auctionlib.lean` and `AuctionlibTest.lean` in your commit. The helper runs
`lake exe mk_all --lib Auctionlib --git` and
`lake exe mk_all --lib AuctionlibTest --git`, then checks both with `--check`.
For these single-library commands, exit 1 can mean one file was updated rather
than a failure; the helper checks that a file actually changed and verifies the
result. Do not join the raw generation commands with `&&` or hide their errors
with `|| true`. `bash scripts/update-imports.sh --check` verifies without writing.

Same-repository PRs may receive an automated commit containing only those two
generated files. Fork PRs are built using GitHub's merge ref and only check the
import lists: CI does not commit or push to a fork. Fix stale imports locally
and push the generated files with your change.

## API stability pins

`ApiStability.lean` at the repository root pins the exact statements of the
library's core theorems and definitions; it is built by the default `lake build`.

If your change turns that file red, the change alters a public statement (an added
hypothesis, a changed conclusion, a renamed or deleted declaration). A red pin is a
question, not permission to change the contract: open a design issue and get
agreement before changing the statement, and do not edit the pin merely to make the
build pass. Once the API change is approved, update the signature and its pin
together in the same PR.

New layers pin their own public API next to themselves in `AuctionlibTest/` (see
`AuctionlibTest/SingleParameter/Compatibility.lean`), so early iteration stays cheap
while a layer is young. Once a layer has downstream users inside the library, its
pins are promoted into `ApiStability.lean`; from then on its statements follow the
design-first rule.

## Review

- PRs touching the core layers get a maintainer review before merge.
- Before merging, confirm that the applicable GitHub Actions checks pass on the
  latest PR revision and that review requests have been addressed. Report the
  build, import checks, and any relevant axiom/API-pin checks in the PR description.
- Foundational changes require design agreement before implementation. If an
  API change breaks a stability pin, obtain design agreement and update the
  declaration and pin together. Leaf contributions can go straight to a PR;
  changes that also touch a core layer still need maintainer review.
- Keep PRs single-purpose and reviewable: one theme per PR, with a short
  description of what is proved and where it sits in the library.
