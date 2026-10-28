# Semantic audit: 23 October 2026

The audit examined the economic meaning of 430 definition-like declarations in
128 library modules at revision
[`1d9f8cc`](https://github.com/matheconlib/matheconlib/commit/1d9f8cc233cdaeee0364b51befb84feea657a4da).
It identified six groups of mismatches between the advertised concepts and the
formal assumptions. The findings concern model semantics; they do not identify a
Lean-kernel inconsistency. [#211](https://github.com/matheconlib/matheconlib/issues/211)
tracks the repairs, and [#218](https://github.com/matheconlib/matheconlib/issues/218)
tracks preservation and migration evidence.

## Findings and repair links

The first two repairs were merged in
[#210](https://github.com/matheconlib/matheconlib/pull/210), through
[`8d9de80`](https://github.com/matheconlib/matheconlib/commit/8d9de809c56cd0080e73536840b875a97e41f6c8).
The remaining design and implementation work belongs to the linked issues.

| Finding | Minimal witness and intended distinction | Repair |
| --- | --- | --- |
| F1: marginal beliefs used for interim incentives and participation | Perfectly correlated Bernoulli types make unconditional opponent averages misclassify both incentive compatibility and interim IR. Hold the true type and its conditional beliefs fixed while comparing reports. | #210 supplies the quasilinear conditional-belief API and its IPV specialization. The conditional all-purchase adapter remains in [#212](https://github.com/matheconlib/matheconlib/issues/212). |
| F2: revenue averages already-marginalized payments | With diagonal Bernoulli reports and one payment `b₀ * b₁`, actual revenue is `1/2`, while the old expression gives `1/4`. Integrate realized joint payments; an unconditional marginal-payment bridge needs independence and integrability. | Implemented in #210; follow-up [#213](https://github.com/matheconlib/matheconlib/issues/213). |
| F3: atomlessness checks only bidder zero | One uniform type and one constant type satisfy the old field while the second marginal has an atom. Quantify over every bidder, or explicitly require a common law. | [#214](https://github.com/matheconlib/matheconlib/issues/214). Identical-law assumptions protect the inspected symmetric consumers. |
| F4: raw signal weights need not define a probability law | The zero density with exponential values satisfies `SignalValueEnv`, independence, IPV and affiliation, but has total mass zero. Distinguish the algebraic weight layer from a measurable, normalized probability environment. | [#215](https://github.com/matheconlib/matheconlib/issues/215). |
| F5: global value conditions constrain infeasible profiles | Global nonnegativity and strict own monotonicity force strictly positive values everywhere, excluding `v(x) = x` at zero on `[0,1]`. Global private-value comparisons also constrain off-support extensions. State the intended conditions on feasible profiles. | [#216](https://github.com/matheconlib/matheconlib/issues/216). |
| F6: pointwise density predicates depend on null-set values | Changing a uniform-square density at a single point preserves its probability law but can break pointwise product factorization and affiliation. Distinguish algebraic predicates on a representative from properties of the represented law. | [#217](https://github.com/matheconlib/matheconlib/issues/217). |

The algebraic affiliation predicate and finite weighted-average results retain
their documented meaning without probability normalization. F4 and F6 concern
their use to describe probability environments and distribution-level concepts.
BIC itself requires neither independent types nor quasilinear preferences; the
repaired mechanism API is explicitly its quasilinear specialization. See
[the BIC migration guide](BICMigration.md) for the implemented names and assumptions.

## Maintained tests and proof limits

- [CorrelatedValues.lean](../MathEconLibTest/Auction/CorrelatedValues.lean) and
  [IndependentValues.lean](../MathEconLibTest/Auction/IndependentValues.lean),
  merged with #210, exercise the actual auction interfaces: conditional
  incentives, profitable deviations, belief-version dependence and realized
  revenue, including an independent positive control.
- [SignalValueBoundaries.lean](../MathEconLibTest/Auction/SignalValueBoundaries.lean)
  retains seven supporting proofs: the zero-density environment's private-value,
  independence, IPV, affiliation and zero-mass properties, and the strict-positive
  value obstruction. These witnesses record current limitations. The F4/F5
  repairs should replace affected witnesses with tests of the corrected contracts.

The seven signal proofs do not formalize the complete atomlessness or
density-version countermodels, or the off-support private-values example. Those
arguments are recorded in the linked issues and full archive. Finite Python
enumerations establish only their encoded cases. The original audit's build
covered the library and umbrella; later full-project builds are separate checks.
The audit's independent workstreams were automated and do not replace maintainer
review of the findings or repair contracts.

Run `lake build MathEconLibTest.Auction.SignalValueBoundaries` for the focused
signal tests. The default `lake build` includes all three modules above, and
`python3 scripts/check-proof-integrity.py` checks their transitive axiom dependencies.

## Full historical archive

The complete pre-curation checkout is preserved by the annotated tag
[`codex/archive-semantic-audit-2026-10-23`](https://github.com/matheconlib/matheconlib/tree/codex/archive-semantic-audit-2026-10-23),
which points to immutable revision
[`aa0aed0`](https://github.com/matheconlib/matheconlib/commit/aa0aed0563b562a763e48c4fd048b1285db5f0fe).
Its [archive README](https://github.com/matheconlib/matheconlib/blob/aa0aed0563b562a763e48c4fd048b1285db5f0fe/docs/audits/2026-10-23-semantic/README.md)
links all area assessments, the declaration inventory, source fingerprints,
reproduction scripts, saved outputs and original twelve supporting statements.

Check out that tag in a separate clone to reproduce the full record; the coverage
verifier needs Git history containing the audited revision. Use the dependencies
pinned in that checkout. The archive checkout uses Lean/Mathlib 4.35.0, while the
audited source and initial publication used 4.28.0. Historical verification and
repair-status entries apply to their recorded revisions; consult the linked
issues and PRs for subsequent decisions.
