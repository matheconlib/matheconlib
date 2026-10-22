# Reviewing for MathEconLib

How review works here, written down for the second reviewer and everyone
after. This is observed practice from the first ~60 PRs, not aspiration.
Authoring rules live in CONTRIBUTING.md; this file is the other side of the
table. A case index at the end maps each rule to the PRs where it happened.
Project-wide design principles live in [`DESIGN.md`](../DESIGN.md); this file
describes how review applies them.
When reviewing an economic model family or instance, use the
[economic model design principles](../DESIGN.md#design-principles-for-economic-models)
alongside the review order below.

## What review is for

CI builds the library, API pins, tests, and examples and checks both import
lists. Reviewers also check for `sorry`, `admit`, and `native_decide` and inspect
axioms on new main results, as required by
[CONTRIBUTING.md](../CONTRIBUTING.md#verification-bar). Review checks meaning:
is the headline statement the theorem the cited paper states, are the
hypotheses honest and load-bearing,
and is the API something the next file can build on. A wrong hypothesis in a
docstring is treated as a pre-merge blocker.

## The review order

1. Statements first. Read the headline against the cited economics:
   quantifiers, claimed generality, silently strong hypotheses. Junk values
   and edge behavior get documented, not engineered away. Assumptions enter
   where they become necessary: measure-level before density, division-free
   identities before quotient formulas, and pointwise derivatives before
   global smoothness.
2. Hypotheses. An assumption the proof never consumes is a defect. The
   strongest check is constructive: build an instance or a counterexample to
   show a guard is load-bearing and the hypotheses are satisfiable.
3. Useful abstractions. A named definition is expensive: ask which theorem it
   supports and wait for a second consumer. Distinguish a richer interface from
   a more general result; avoid unused generality and unnecessary public helpers.
4. API surface. Sweep for duplication against our own layers and mathlib:
   nothing forks, and when two abstractions can express the same object,
   require a bridge lemma, not coexistence. At a transformation boundary,
   record what is preserved, which deviations remain expressible, and what is
   lost; reverse implications need an explicit bridge, and transport instances
   must not create search cycles. Check downstream use through the documented
   umbrella: a young layer's pin file imports only that umbrella, so a missing
   export or public dependency fails the build; what pins do not exercise stays
   a prose check. Approved signature changes and their pins move together; a
   red pin is a question, not a permit. Naming follows the #45 ruling recorded
   in CONTRIBUTING.md.
5. Witnesses. Headline hypotheses and advertised features are certified by an
   instance or end-to-end example that actually exercises them; constructing
   only the input certifies nothing. Reuse existing examples and cross-check an
   independent formula when available. Check the
   [placement rules](../CONTRIBUTING.md#examples-and-tests): reusable definitions,
   results, constructions, and instances belong with the core API; worked
   demonstrations belong in examples; API and regression checks belong in tests.
   Example-local definitions and instances may stay with their demonstration.
   Tests should import a worked example rather than duplicate it, and core code
   must not import examples or tests.
6. Machines first, then you. Do not relitigate what CI checks. When CI did
   not run (stacked PRs skip it), do the missing run yourself and say so in
   the review. Check the [warning comparison](../CONTRIBUTING.md#build-warnings)
   and review justifications for new warnings or linter suppressions.
7. Docs and attribution. Docstrings and README claims are checked against
   the actual declarations. Check the
   [citation guidance](../CONTRIBUTING.md#citing-sources): paper- or book-based
   work names its author, year, and title, and includes a DOI or stable link when
   available, with theorem or section numbers when available and adaptations
   stated. Standard toy examples
   need no invented citation. Ported files carry correct author lines and a
   provenance note.

## How to write the review

Verdict in the first sentence. Praise specifically, naming the verified
thing: it is evidence you read the work. Number the blocking asks, label
everything else ("Non-blocking:", "take or leave"); blockers and nits never
mix, and curation is kindness - a ten-item review is help, a forty-five-item
review is hostility.

For a stack: systemic feedback is stated once on the tracking issue and the
per-PR reviews point back to it. Request Changes only on the PRs that own a
concrete blocker; siblings get Comment. For base branches, refreshes, and review
handoff after a parent merges, see the
[branch and stacked-PR guidance](../CONTRIBUTING.md#branches-and-stacked-prs).

Decide, do not deflect. State maintainer decisions so the author does not
have to guess; accept-now-with-bridge versus redesign-later is a ruling, and
the reviewer opens the follow-up issue. Open design questions move to a
design issue, never a review thread. Hand the author the fix, not just the
complaint. And own the project's gaps in the review itself: "our gap, not
yours."

## Reviewing with an LLM

Policy set at the 2026-09-03 meeting: LLM-assisted review is the normal
working mode here. A frontier model does the legwork of the review order
above - the statement audit against the cited paper, the duplication sweep,
building the branch when CI did not run, the linter census. Hold it to the
house grounding standard: every claim cites a file and line, and checkable
claims get compiled before they are asserted. Tooling for the legwork is
cataloged in TOOLING.md. What stays human: the design
judgment, the verdict, and the tone. If you are not a Lean expert, that is
fine - spend your judgment on the small definitional core where the modeling
choices live, not on the machine-checked derivation.

## Case index

- Statement audit: #58, #59. Doc-hypothesis blockers: #37, #39.
- Assumptions at the right layer: #37 (division-free weight first), #55
  (measure-level formulations), #61 (pointwise derivative).
- Constructive checks: the Dirac instance in #37, the uniform
  interior-optimum instance in #39, the tried-and-excluded sweep in #30.
- Unused-hypothesis sweep, restatements recompiled before asserting:
  #49 -> #53.
- Useful abstractions and transformation boundaries: #30. Downstream use
  through public imports: #35, #61.
- Duplication sweeps and bridge-over-coexistence: #55, #54, #57, #59.
- Pins moving with signatures: #53, #59; pins by named declaration: #56.
- Naming ruling: #45, implemented in #62.
- Witness policy: #47; meaningful theorem applications: #35, #39; delivered
  early in #59.
- Stack reviewed as a unit, systemic-once, local tip build where CI did not
  run: #54 over #55-#59.
- Verdict-first, decisions batched ("Two decisions so you do not have to
  guess"), merge plan at the end: the #54 comment.
- Design-first flow: #40 -> #61; off-GitHub decisions written back onto the
  issue: #40.
- Handing the fix: #15 (ready branch to cherry-pick).
