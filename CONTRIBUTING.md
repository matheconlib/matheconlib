# Contributing to auctionlib

Thanks for contributing! This is a short guide to how changes land in this repository.

New to Lean 4 or to this library? Start with
[*Lean 4 and `auctionlib` — A Beginner's Manual*](docs/BeginnersManual.md),
which covers the toolchain, the editor loop, and how to read the library's
core files. The `ForMathlib/` folder is a good place for a first contribution.

## Design first for core layers

Changes to the foundational layers — `Mechanism/`, `BidderProblem/`, `GameTheory/`,
`Auction/Basic.lean` — or the introduction of a new foundational layer start with a
**design issue** before implementation. Sketch the intended definitions and the main
statements, and get agreement on the shape before writing the proofs.

Leaf contributions — new theorems in existing chapters, documentation, applications
built on the existing layers — can go straight to a PR.

## Public API

The statements, names, hypotheses, and binder names of existing public declarations
are API. Downstream files and external users rely on them, so any change to them —
however small — is called out explicitly in the PR description, with a sentence on
why the change is needed.

## Verification bar

Every PR must satisfy:

- `lake build` is green.
- No `sorry`, `admit`, or `native_decide` anywhere in the change.
- `#print axioms` on new main results shows only `propext`, `Classical.choice`,
  and `Quot.sound`.
- Imports are regenerated with `lake exe mk_all --lib Auctionlib --git`.

## API stability pins

`ApiStability.lean` at the repository root pins the exact statements of the
library's core theorems and definitions; it is built by the default `lake build`.

If your change turns that file red, the change alters a public statement (an added
hypothesis, a changed conclusion, a renamed or deleted declaration). That is a
signal to **discuss first**: open a design issue and get agreement before changing
the statement. Do not edit the pin to make it pass.

New layers pin their own public API next to themselves in `AuctionlibTest/` (see
`AuctionlibTest/SingleParameter/Compatibility.lean`), so early iteration stays cheap
while a layer is young. Once a layer has downstream users inside the library, its
pins are promoted into `ApiStability.lean`; from then on its statements follow the
design-first rule.

## Review

- PRs touching the core layers get a maintainer review before merge.
- Keep PRs single-purpose and reviewable: one theme per PR, with a short
  description of what is proved and where it sits in the library.
