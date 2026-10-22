# Contributing to MathEconLib

Thanks for contributing! This is a short guide to how changes land in this repository.

New to Lean 4 or to this library? Start with
[*Lean 4 and `MathEconLib` — A Beginner's Manual*](docs/BeginnersManual.md),
which covers the toolchain, the editor loop, and how to read the library's
core files. Small, well-scoped additions to `ForMathlib/` can be suitable first
contributions; the folder also contains substantial results.

For a small documentation task, start with
[documenting the BidderProblem umbrella (#118)](https://github.com/matheconlib/matheconlib/issues/118).
The issue gives the starting file, expected result, and build check.

## Design first for core layers

The project-wide framework for choosing abstractions, theorem scope,
transformations, and public interfaces lives in
[`DESIGN.md`](DESIGN.md).
For economic model families and their instances, also follow the
[economic model design principles](DESIGN.md#design-principles-for-economic-models).

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

## Examples and tests

- `MathEconLib/`: reusable definitions, results, constructions, and instances,
  alongside the relevant topic's core API.
- `MathEconLibExamples/`: worked demonstrations of the public API. Definitions
  and instances used only by an example may stay here; this is not the general
  home for instances.
- `MathEconLibTest/`: API and regression checks. When testing a worked example,
  import its development instead of maintaining a second copy.

Keep one canonical development. Move reusable parts of an example into the core
when another application needs them. Core code must not import examples or tests.

## Applying main results

For a new or materially changed theorem presented as a main result in the
README or website, include a checked theorem application: a Lean development
that compiles, constructs a concrete model, proves all the theorem's assumptions
for that model, and applies the named theorem to derive a meaningful conclusion.
An existing development can qualify. Checking only the theorem's type
(a "signature pin") does not.

Additional applications of older main results remain post-launch work under
[#47](https://github.com/matheconlib/matheconlib/issues/47).

## Citing sources

Use the author–year format shown below as the default, with complete references.
Detailed formatting guidance is tracked in
[style conventions (#109)](https://github.com/matheconlib/matheconlib/issues/109).

Contributions may cover selected results or complete papers, subject to our
integration and review standards. Paper-specific developments may remain downstream,
with reusable components contributed here following the [placement guidance](#examples-and-tests).

For work based on a paper or book, give the author, year, and title in the module
documentation, and include a DOI or stable link when available. Include the theorem
or section number when available. State which source results are covered, any
adapted assumptions, and important omissions, as in the example below:

```lean
/-!
# A Becker-inspired crime choice

This example specializes risk-neutral binary choice from the cited analysis:
offending gives payoff `v - p * f`; abstaining gives zero. It does not formalize
the full enforcement model.

## References

Gary S. Becker (1968), *Crime and Punishment: An Economic Approach*,
*Journal of Political Economy* **76**(2), 169–217.
[DOI: 10.1086/259394](https://doi.org/10.1086/259394).
-/
```

Standard textbook examples do not need to be cited. Sources without a DOI can use
a stable link. For ported Lean code, record its source and preserve author credit.

## Copyright headers

Every Lean file starts with the Mathlib-style header below; CI checks it. Add your name to the copyright and `Authors` lines of a file you contribute to substantially.

```lean
/-
Copyright (c) 2026 Your Name. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Your Name
-/
```

## Public API

The statements, names, hypotheses, and binder names of existing public declarations
are API. Downstream files and external users rely on them, so any change to them —
however small — is called out explicitly in the PR description, with a sentence on
why the change is needed.

Project-owned declarations live under `MathEconLib`; see the
[public-name mapping](docs/NamespaceMigration.md). Following the naming ruling
in #45, general carrier structures keep short names in a sufficiently specific
topic namespace, such as `MathEconLib.Auction`.
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
git add path/to/NewFile.lean        # if adding a Lean file
bash scripts/update-imports.sh      # regenerate both root import files, then verify them
lake build                         # includes API pins and MathEconLibTest/Manual/HandsOn.lean
```

Omit the `git add` line if you have not added a file. Include changes to
`MathEconLib.lean` and `MathEconLibTest.lean` in your commit.
Use `bash scripts/update-imports.sh --check` to verify imports without changing files.

### Build warnings

Contributions should avoid introducing new compiler or linter warnings. Fix new
warnings where practical; otherwise explain in the PR why they are needed. Keep
any linter suppression narrow and justified.

CI's warning-count comparison is informational; an increase does not fail CI.
All verification requirements above still apply.

## API stability pins

`ApiStability.lean` at the repository root pins the exact statements of the
library's core theorems and definitions; it is built by the default `lake build`.

If your change turns that file red, the change alters a public statement (an added
hypothesis, a changed conclusion, a renamed or deleted declaration). A red pin is a
question, not permission to change the contract: open a design issue and get
agreement before changing the statement, and do not edit the pin merely to make the
build pass. Once the API change is approved, update the signature and its pin
together in the same PR.

New layers pin their own public API next to themselves in `MathEconLibTest/` (see
`MathEconLibTest/SingleParameter/Compatibility.lean`), so early iteration stays cheap
while a layer is young. Once a layer has downstream users inside the library, its
pins are promoted into `ApiStability.lean`; from then on its statements follow the
design-first rule.

## Branches and stacked PRs

Start a short-lived topic branch from current `main`; ordinary PRs target `main`.
For dependent work, branch from the parent and target its branch so the child diff
shows only the dependent change. Each PR description names its base and links its
parent and any known children.

For example, a shared lemma and its application can be reviewed separately:

| PR | Head branch | Base branch | Description |
| --- | --- | --- | --- |
| A | `envelope-lemma` | `main` | Shared lemma; child: B |
| B | `envelope-example` | `envelope-lemma` | Application; depends on A |

1. Merge A first and fetch current `main`. Keep a reference to the last parent
   commit contained in B until the child is refreshed.
2. Refresh B onto `main` and retarget its PR to `main`. After a squash merge,
   replay only B's commits, using [git rebase --onto](https://git-scm.com/docs/git-rebase)
   with that parent commit as the boundary. Coordinate any rewrite of a shared
   branch; use `--force-with-lease` when pushing rewritten history. Check that B's
   diff contains only its intended application before deleting the parent branch.
3. After a refresh or conflict resolution, rerun the import checks and `lake build`
   from the [verification bar](#verification-bar), and wait for applicable CI on
   the latest revision. Verify against current `main` before merging: an old
   green check can predate changes to build requirements. CI currently runs only
   for PRs targeting `main`; check children locally until they are retargeted.
4. Leave a brief update naming the new base, conflicts resolved, substantive
   changes, and check results. Request another review when statements, APIs,
   implementation, or guidance changed substantively; carry forward
   earlier feedback and confirm that required changes are addressed.

The [stack-review guidance](docs/REVIEWING.md#how-to-write-the-review) explains
where to put shared feedback and which PR owns a blocker.

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
