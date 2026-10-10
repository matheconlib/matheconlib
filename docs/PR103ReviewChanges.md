# PR 103 review changes

This record maps the review requests to focused commits on
`38-design-matching-with-contracts`. It records implementation, not reviewer
approval or GitHub thread resolution. The pull request remains open for review.

## Previously applied inline comments

| Comment | Existing commit |
| --- | --- |
| S01 | [f3e4667](https://github.com/AxiomMath/auctionlib/commit/f3e46677bb8b23e99ff00f46d5b322139ed84e56) |
| S02 | [c0b09dc](https://github.com/AxiomMath/auctionlib/commit/c0b09dcf648db5583d2ff31295010b4996d9a70f) |
| S03 | [fc9f59e](https://github.com/AxiomMath/auctionlib/commit/fc9f59e9aa29ce56071ada9fefd1661475aba8e4) |
| S04 | [2a9ef75](https://github.com/AxiomMath/auctionlib/commit/2a9ef75c1f3dc62f0f0488084d63d30b72f9c9ec) |
| S09 | [224bab7](https://github.com/AxiomMath/auctionlib/commit/224bab794d51ad858b6a08e75d7566da1400d453) |

## Focused implementation commits

Each commit body identifies its review comment and, for broad reviews, the
particular subitem. API changes include their affected callers; client checks
were added alongside the new public APIs.

| Review item | Commit | Change |
| --- | --- | --- |
| [S05](https://github.com/AxiomMath/auctionlib/pull/103#discussion_r4206398351) | [24237f2](https://github.com/AxiomMath/auctionlib/commit/24237f2900d07da3eeffe697c181c3bb976fef64) | docs(matching): clarify generalized DA endpoints |
| [S06](https://github.com/AxiomMath/auctionlib/pull/103#discussion_r4206398368) | [c2c305a](https://github.com/AxiomMath/auctionlib/commit/c2c305a433dca206dec05aac078cf6fba44f7267) | docs(matching): clarify deferred acceptance fuel bounds |
| [S07](https://github.com/AxiomMath/auctionlib/pull/103#discussion_r4206398387) | [3a898c7](https://github.com/AxiomMath/auctionlib/commit/3a898c79fb2f7d4e5dbdfcaa2919bcd2e9043b17) | docs(choice): explain IRC menu reductions |
| [S08](https://github.com/AxiomMath/auctionlib/pull/103#discussion_r4206398402) | [7f54c83](https://github.com/AxiomMath/auctionlib/commit/7f54c831328783ef544aade34949fb232db0ed69) | refactor(order): simplify fixed-point endpoint projections |
| [Architecture integration prerequisite](https://github.com/AxiomMath/auctionlib/pull/103#pullrequestreview-5434835152) | [bab3bcb](https://github.com/AxiomMath/auctionlib/commit/bab3bcb636f474494d2ab008a5f355699bab6d36) | merge: integrate current main while preserving matching coverage |
| [Architecture integration items 1, 2 and 4](https://github.com/AxiomMath/auctionlib/pull/103#issuecomment-6089971657) | [3f0def2](https://github.com/AxiomMath/auctionlib/commit/3f0def2956991c74140499574bdcce960dc996ba) | refactor(matching): adopt MathEconLib namespaces and module layout |
| [Bo API clarification](https://github.com/AxiomMath/auctionlib/pull/103#issuecomment-6089971657) | [0e9ef2d](https://github.com/AxiomMath/auctionlib/commit/0e9ef2de4cab2691041a5093b146101c39987047) | refactor(matching): remove obsolete correspondence wrappers |
| [Architecture improvement 1](https://github.com/AxiomMath/auctionlib/pull/103#pullrequestreview-5434835152) | [909e1a0](https://github.com/AxiomMath/auctionlib/commit/909e1a0981657754228f992f52833a13677a42a0) | refactor(choice): package the substitute hull as a closure operator |
| [Architecture improvement 2](https://github.com/AxiomMath/auctionlib/pull/103#pullrequestreview-5434835152) | [08278d1](https://github.com/AxiomMath/auctionlib/commit/08278d17b5cef93e8991eef68ab86453d5bf9960) | refactor(order): reuse Mathlib finite iteration machinery |
| [Architecture improvement 3](https://github.com/AxiomMath/auctionlib/pull/103#pullrequestreview-5434835152) | [c340039](https://github.com/AxiomMath/auctionlib/commit/c3400399f42f6376e360a3a029d934efb4c38263) | refactor(choice): share finite partner selection |
| [Architecture improvement 4](https://github.com/AxiomMath/auctionlib/pull/103#pullrequestreview-5434835152) | [54a13f0](https://github.com/AxiomMath/auctionlib/commit/54a13f056a45c50b49d579b2e536c258b0b812aa) | feat(choice): expose greatest feasible bundle interfaces |
| [Architecture improvement 5](https://github.com/AxiomMath/auctionlib/pull/103#pullrequestreview-5434835152) | [008f217](https://github.com/AxiomMath/auctionlib/commit/008f2171443e254b9ffe9d1117b9e09afbd4a8f2) | feat(choice): bundle choice transport as an order embedding |
| [Architecture improvement 6: finiteness](https://github.com/AxiomMath/auctionlib/pull/103#pullrequestreview-5434835152) | [60162ec](https://github.com/AxiomMath/auctionlib/commit/60162ec328c8f375ba0fbfbd1ea1b71f73f8fbb8) | refactor(choice): derive finiteness from the function coercion |
| [Architecture improvement 6: shared support](https://github.com/AxiomMath/auctionlib/pull/103#pullrequestreview-5434835152) | [4f02e77](https://github.com/AxiomMath/auctionlib/commit/4f02e77db4aa260f933d7b64745ee15276084bba) | refactor(matching): share graph fiber and off-support lemmas |
| [Dan suggestion 1](https://github.com/AxiomMath/auctionlib/pull/103#issuecomment-6085033992) | [4fad40d](https://github.com/AxiomMath/auctionlib/commit/4fad40dffa009f390032a061715f37222cf8d417) | refactor(matching): require IRC in stable outcome interfaces |
| [Dan suggestion 2: predicate-based alternative](https://github.com/AxiomMath/auctionlib/pull/103#issuecomment-6085033992) | [8984534](https://github.com/AxiomMath/auctionlib/commit/89845344555c054136a78edf008d118727765693) | feat(matching): make market locality explicit |
| [Economic review citation request](https://github.com/AxiomMath/auctionlib/pull/103#pullrequestreview-5436306136) | [5c7acc8](https://github.com/AxiomMath/auctionlib/commit/5c7acc843a315acfb68818cb3879f049e304c9ac) | docs(matching): replace unverified theorem citations with checked references |
| [Architecture integration/client checks and review traceability](https://github.com/AxiomMath/auctionlib/pull/103#pullrequestreview-5434835152) | [97e22a0](https://github.com/AxiomMath/auctionlib/commit/97e22a0aa936a49a618ab68242fa359d97523c1f) | docs(matching): document architecture and review changes |
| [Architecture improvement 2: explicit dependency after iteration refactor](https://github.com/AxiomMath/auctionlib/pull/103#pullrequestreview-5434835152) | [5f9665c](https://github.com/AxiomMath/auctionlib/commit/5f9665cbeda8f7bb17d4bc8ff0422b9861c1ebba) | fix(choice): import the repair termination pigeonhole theorem explicitly |
| [Dan suggestion 2: locality proof elaboration](https://github.com/AxiomMath/auctionlib/pull/103#issuecomment-6085033992) | [92cd6ad](https://github.com/AxiomMath/auctionlib/commit/92cd6ad6dd4348d55266d525db3ba2e2f5c9ee2a) | fix(matching): make locality proof congruences explicit |
| [Dan suggestion 1: stable outcome accessor elaboration](https://github.com/AxiomMath/auctionlib/pull/103#issuecomment-6085033992) | [1f3d813](https://github.com/AxiomMath/auctionlib/commit/1f3d8132f33bbe2320972da11fb56d8ab786285c) | fix(matching): restore stable outcome field notation |

The subsequent [checklist commit](https://github.com/AxiomMath/auctionlib/commit/5e7cf3ce95aa5899f11da3c9f6c66fcc8d02a317)
records the completed build and these follow-ups. The subsequent
[survey citation audit](https://github.com/AxiomMath/auctionlib/commit/6fdc9fe9eee5ffae6da7197cb34a15edfb1d3136)
and [published-article audit](https://github.com/AxiomMath/auctionlib/commit/e1837f1499e01fe5e579a8b1ac8100beb5a00394)
established the reference map used by the Lean docstring alignment described
under Citation disposition below.

The final three fixes address concrete Lean errors found while compiling the
complete series: an explicit pigeonhole import, typed locality congruences, and
stable-outcome accessor wrappers. They retain the theorem statements and
economic assumptions of the corresponding review changes.

The intervening merge by the branch author at
[`5f2ba6b`](https://github.com/AxiomMath/auctionlib/commit/5f2ba6b96fb05b30040079ea7852b4a11400ba9b)
was preserved. Its tree was identical to the preceding import fix.

## Interpretation of the two modeling changes

- `StableOutcomes hsub hcons` explicitly requests IRC, while `FixedPointStates hsub`
  exposes the raw carrier. The former is a reducible abbreviation: the proof
  parameter is an interface convention, not a distinct proof-carrying type.
- Locality is an explicit `Market.Local` predicate, derived from consistency
  and proved directly for marriage markets. This adopts the predicate-based
  alternative described in the implementation plan; it does not add mandatory
  locality fields to the support-only base market.

## Citation disposition

The supplied published 2025 chapter has now been checked directly. The exact
survey definition, lemma and theorem locators are recorded in
[MatchingReferences.md](MatchingReferences.md), including the distinction
between its many-to-one and many-to-many results. The chapter supplies published
references for the completion definitions and example previously mapped to the
2016 Hidden Substitutes manuscript. The map also flags the apparent printed
wording error in Theorem 3.3 and preserves the finite-domain and IRC qualifications.

HK2010's published definitions and Litvakov's published Russian hull formula
have been checked. The three subsequently supplied published articles have
also been checked directly: Hatfield–Kominers (2017), Zhang (2016) and
Monjardet–Raderanirina (2004). The reference map records their exact locators
and the scope of each comparison. No further PDFs are needed for this set of
checks; Litvakov's English translation is optional for English pagination.

Hatfield–Kominers' published Theorem 4, p. 95, supplies the unambiguous
many-to-many rural-hospitals reference. The paper's Theorem 1 preference-order
lattice statement is distinguished from Lean's choice-order formulation.
Zhang's Lemma 2, Proposition 2 and §5 repair proof are all on p. 233; his paper
explicitly does not establish an IRC completion. The map separates that bare completion
result from Lean's IRC and finite-valued strengthenings and repair schedule
results. Monjardet–Raderanirina is cited for finite choice-lattice background,
with Litvakov retained as the direct hull-formula reference.

The Lean docstrings now use the independently checked `HKContractDesign2017`
locators and the published survey's completion definitions and example.
The source bibliography identifies Litvakov's Russian original as the checked
source of the hull formula, and adds the exact published Zhang and
Monjardet–Raderanirina locators. The choice-order lattice and rural-hospitals
modules now carry their verified published references. Existing distinctions
between source results and the stronger Lean statements are retained.

The survey and article audit commits changed Markdown only. The subsequent
commit, `docs(matching): align Lean citations with published sources for #103`,
updates comments and docstrings in eleven Lean files and reconciles this
record and the reference map. It changes no imports, declarations, theorem
statements or proofs.

## Validation

The complete revised source at
[`1f3d813`](https://github.com/AxiomMath/auctionlib/commit/1f3d8132f33bbe2320972da11fb56d8ab786285c)
passed [Lean CI run 38088964202](https://github.com/AxiomMath/auctionlib/actions/runs/38088964202).
The completed job log confirms that exact checkout and reports
`Build completed successfully (8141 jobs)`. It includes both public-import
clients, API stability pins, the namespace guard, the moved counterexamples,
and all three corrected modules, with no Lean errors. The citation alignment
was checked by comparing every Lean file with the pre-alignment snapshot
after removing comments, with identical remaining source. Balanced nested
comments and the absence of stale manuscript citations were also checked.
This is a documentation-only verification, not a new full Lean build of the
citation commit; the previously compiled declarations and proofs are unchanged.

Earlier exact-checkout builds also passed for the main integration
[`bab3bcb`](https://github.com/AxiomMath/auctionlib/commit/bab3bcb636f474494d2ab008a5f355699bab6d36)
and mechanical namespace migration
[`3f0def2`](https://github.com/AxiomMath/auctionlib/commit/3f0def2956991c74140499574bdcce960dc996ba).

Before the three CI corrections above, the reconstructed 32 matching modules
were compared byte for byte with the reviewed local revision. The corrected
published source tree was then compared by Git blob hash with all 157 local
files. Structural checks cover local imports, import cycles, Choice independence,
production/test separation, generated root imports, and absence of proof
placeholders. The 11 Python import-helper tests also pass.

For later revisions, consult the
[PR checks](https://github.com/AxiomMath/auctionlib/pull/103/checks) and verify the
actual checked-out commit in the job logs. A historical green result does not
certify subsequent source changes.

## Deferred work

Market side swapping/relabeling, utility adapters, ties, broader preference
relations, removing finiteness from graph/stability translation, general
chain-condition extensions, other optional generalizations, and post-merge
issue management remain outside this series, as agreed in the discussion.
No review replies or thread resolutions were posted by this implementation
sequence.
