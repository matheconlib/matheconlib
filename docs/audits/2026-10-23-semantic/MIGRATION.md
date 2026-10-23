# Repair contracts and migration status

Audited revision: `1d9f8cc233cdaeee0364b51befb84feea657a4da`. This table records the accepted
direction and current implementation separately. A linked design issue does not itself establish
maintainer approval or completion.

| Finding | Original mismatch | Accepted repair and public migration | Implementation and remaining work |
|---|---|---|---|
| F1 — conditional incentives/participation | Unconditional opponent averages misclassify correlated models in both directions. | Keep economic BIC broad. The implemented mechanism interface is explicitly quasilinear and uses true-type conditional beliefs and integrable utilities. `Auction.BIC B` is a proposition; scalar payment clients use `[A.IsIPV] [Auction.IPV.BIC A]`. `InterimIR` takes beliefs; `MarginalIR` names the old marginal inequality. | [#210](https://github.com/matheconlib/matheconlib/pull/210) implements the conditional interface and IPV bridge. [#212](https://github.com/matheconlib/matheconlib/issues/212) remains open for the conditional all-purchase adapter. |
| F2 — expected receipts | `expectedRevenue` integrated already-marginalized payments, which can differ from realized receipts. | The same public name now integrates `A.rules.revenue (A.θ · ω)` under the actual joint prior. The marginal-payment bridge requires independence, measurable rules and integrable realized payments. Payment/revenue theorem assumptions, callers and pins migrate together. | Implemented in [#210](https://github.com/matheconlib/matheconlib/pull/210); [#213](https://github.com/matheconlib/matheconlib/issues/213) requires final review and a merge link before closure. |
| F3 — atomlessness | Only bidder zero was checked without an identical-laws prerequisite. | Quantify over every marginal, or explicitly restrict/name a common-law specialization. Preserve downstream uses already protected by identical laws. | [#214](https://github.com/matheconlib/matheconlib/issues/214), open; no repair claimed here. |
| F4 — probability environment | Raw nonnegative signal weights need not be measurable or have mass one. | Keep raw weights separate from a genuine probability environment and prove the representation/normalization bridge. | [#215](https://github.com/matheconlib/matheconlib/issues/215), open; coordinate the carrier with F5/F6. |
| F5 — feasible profiles | Global sign/strict-monotonicity and private-values comparisons exclude valid on-support models. | State regularity and private values on the feasible signal box, preserving restriction directions without claiming arbitrary global extensions. | [#216](https://github.com/matheconlib/matheconlib/issues/216), open. |
| F6 — density versions | Pointwise density predicates can change under a null-set modification of the same law. | Use law-level dependence properties or an appropriate representative-existence condition. Retain algebraic pointwise predicates with their exact scope. | [#217](https://github.com/matheconlib/matheconlib/issues/217), open; depends on F4's law interface and F5's domain. |

## Auction implementation and regression links

The published baseline [#210 revision `2bbb5b8`](https://github.com/matheconlib/matheconlib/commit/2bbb5b84d04ecafe20d7f8081826d9cce30a60b6)
is stacked on the Lean 4.35 upgrade and remains unmerged. The review follow-up adds a substantive
`isBICOn_iff` pin, a version-uniform negative control, and a null-type-only change of beliefs that
defeats the square positive control. Local verification passes the full 9,220-job build, thirteen
standard-only axiom reports, three rejected characterization mutations, 11 import-helper tests,
28 warning-helper tests and exact arithmetic. Remote CI and maintainer review are recorded on
the PR; older build/CI counts certify only their stated heads.

- [Quasilinear conditional BIC](https://github.com/matheconlib/matheconlib/blob/2bbb5b84d04ecafe20d7f8081826d9cce30a60b6/MathEconLib/Mechanism/Core/BayesianIC.lean)
  composes the existing rules, environment, prior and selected conditional beliefs. IPV is a
  specialization; independence and private values are not prerequisites of BIC.
- [Correlated auction regressions](https://github.com/matheconlib/matheconlib/blob/2bbb5b84d04ecafe20d7f8081826d9cce30a60b6/MathEconLibTest/Auction/CorrelatedValues.lean)
  compile complete old/new F1/F2 examples. The symmetric polynomial example charges two bidders:
  old revenue zero versus realized revenue two. The audit's minimal single-paying-bidder
  `b₀*b₁` example instead gives `1/4` versus `1/2`; these are distinct witnesses.
- [Independent posted-price client](https://github.com/matheconlib/matheconlib/blob/2bbb5b84d04ecafe20d7f8081826d9cce30a60b6/MathEconLibTest/Auction/IndependentValues.lean)
  constructs the IPV specialization, applies the scalar payment identity and obtains nonzero
  revenue through the joint/marginal bridge.
- [Migration documentation](https://github.com/matheconlib/matheconlib/blob/2bbb5b84d04ecafe20d7f8081826d9cce30a60b6/docs/BICMigration.md)
  records binder/namespace and interpretation changes. [#222](https://github.com/matheconlib/matheconlib/issues/222)
  retains older incentive-name migration and the broader utility-adapter design.

Pointwise BIC is relative to a selected belief version. The prior fixes conditional beliefs
only almost everywhere. Version-uniform rejection at supported types and null-type version
dependence of a positive example are different statements and require different tests.

This publication does not assert a merge, close F1's remaining adapter work, or certify the full
continuous symmetric-IPV theorem application still tracked in
[#47](https://github.com/matheconlib/matheconlib/issues/47).
