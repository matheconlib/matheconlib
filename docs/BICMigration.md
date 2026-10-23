# Quasilinear conditional BIC and its IPV specialization

Design: [#211](https://github.com/matheconlib/matheconlib/issues/211),
repair: [#212](https://github.com/matheconlib/matheconlib/issues/212),
implementation: [#210](https://github.com/matheconlib/matheconlib/pull/210).
Bo authorized this API revision on 23 October 2026. Core-maintainer review is
still required before merge.

Bayesian incentive compatibility means that truthful reports maximize expected
utility given the agent's true-type beliefs and truthful opponents. It does not
require independent types, private values, or quasilinear utility. The mechanism
API implemented here is the quasilinear specialization: utility is outcome
value plus the signed transfer received. It is general with respect to type
correlation, value interdependence and type dimension, within that utility model.
The defect in the old auction API was averaging opponents unconditionally,
even when observing one's own value
changed their conditional distribution. Adding independence to the definition
of BIC would exclude valid correlated mechanisms.

## Quasilinear mechanism incentive API

`Mechanism.DirectMechanism.Quasilinear.IsBICOn E M μ B D` composes the existing valuation
environment, induced Bayesian game, probability prior, conditional-belief
version, and declared type/report sets. `E : QuasilinearEnvironment I T O` can
have interdependent values. The `Quasilinear` namespace makes the utility
restriction visible without assigning it to the mechanism rules.
`B.opponents i s` is held fixed when the report changes from `s` to `r`; the
valuation environment also continues to see the true type profile.

Every compared conditional utility must be integrable. This prevents a
nonintegrable Bochner integral's default value of zero from certifying BIC.
The probability-measure hypothesis is explicit. No independence, density,
symmetry, private-values, or atomlessness assumption is present.

The predicate is **pointwise relative to a selected belief version**, including
declared types with marginal probability zero. A prior alone specifies
conditional beliefs only almost everywhere. `IsBIC` is the full-type-space
case. `IsBIC.isBNE` proves truthful Bayesian Nash equilibrium using the existing
equilibrium API, with jointly measurable payoffs and integrable truthful
realized utilities. The reverse implication to pointwise BIC is not asserted:
an a.e. equilibrium cannot determine incentives or beliefs at null types.

## Scalar auctions and IPV

`Auction.BIC B` is the quasilinear mechanism predicate on the auction's stated
type/report intervals, with joint prior `A.typeLaw` and selected beliefs `B`.
It is an ordinary proposition, replacing the old typeclass. `Auction.InterimIR B`
likewise uses integrable conditional truthful utility; `Auction.MarginalIR`
retains the old unconditional inequality under an explicit name.

The scalar `Auction` carrier already fixes private, linear, quasilinear values.
`A.IsIPV` is therefore a thin alias for `A.HasIndependentTypes`. It does not add
identical distributions, symmetry, density, boundedness, or atomlessness.
Those remain separate hypotheses or the existing stronger `IsSymmetricIPV`
convenience bundle.

`A.independentBeliefs` constructs constant opponent beliefs from independence
and proves that they disintegrate the actual joint prior. `Auction.IPV.BIC A`
is a convenience class containing exactly `A.BIC A.independentBeliefs`.
Its limited purpose is compatibility with the existing inferred
`BidderProblem.HasTypeDeviationIC → HasEnvelopeIC` chain. The caller supplies
the BIC proof; typeclass search propagates it through that fixed chain.
It selects no beliefs or equilibrium and introduces no reverse inference
from quasilinear BIC to independence. Quasilinear BIC remains an ordinary predicate.
`IPV.bic_iff_marginal` proves equivalence with the familiar marginal
`s * q(r) - p(r) ≤ U(s)` inequalities when allocations lie in `[0,1]` and all
compared conditional utilities are integrable. This is pointwise on the
declared intervals, including their unrealized interior types.

`IPV.BIC.marginal_ic` extracts those inequalities from conditional BIC. Its
proof derives payment integrability from conditional utility integrability
and bounded allocations, then separates the integral. It never splits a
nonintegrable utility integral into totalized allocation/payment integrals.

## Naming and broader concepts

`Mechanism` and `DirectMechanism` store rules, with no preference assumption.
They can be paired with other utility models; renaming them to
`QuasilinearMechanism` would assign the restriction to the wrong object.
Payment signs, realized receipts and budget conditions do not assume
quasilinear preferences. Scalar envelope/payment and revenue-equivalence
results do use quasilinearity and their advertised scope must say so.

The new conditional incentive API is under `DirectMechanism.Quasilinear`.
Its `truthfulStrategy`, `interimUtility`, `interimUtility_eq_integral`,
`IsBICOn`, `IsBIC` and `IsBIC.isBNE` names move together in this unmerged PR.
The older `DirectMechanism.IsDSIC`, `IsExPostIR` and `IsEfficient` APIs still
bind `QuasilinearEnvironment`; a consistent namespace migration and its
compatibility policy are tracked in [#222](https://github.com/matheconlib/matheconlib/issues/222).
The existing efficiency predicate maximizes summed valuations, rather than
providing a general arbitrary-preference Pareto-efficiency concept.

BIC for broader preferences should reuse the arbitrary-payoff Bayesian game
and equilibrium machinery. A broader utility-environment adapter, with a
checked quasilinear specialization, can be designed when a concrete
non-quasilinear application needs it. No such adapter is implemented here.
Multidimensional types do not require non-quasilinear preferences; #221
therefore remains scoped to quasilinear vector/implementability theory.

## Public migration

- Replace `[A.BIC]` in scalar payment/envelope applications with
  `[A.IsIPV] [Auction.IPV.BIC A]`. Symmetric-IPV environments already supply
  the independence instance. Both auctions need the specialization in
  `payment_equivalence` and `revenue_equivalence`.
- Construct `IPV.BIC` from a proof of conditional quasilinear BIC, or use
  `IPV.bic_iff_marginal` with a proof of conditional integrability. An old
  record supplying only scalar inequalities is insufficient.
- General correlated incentive arguments use a hypothesis `h : A.BIC B`
  and its `h.bic` and `h.integrable` fields. BIC does not produce an
  independence instance.
- `InterimIR` now takes a conditional-belief version and includes
  integrability; the former marginal predicate is named `MarginalIR`.
- `hasTypeDeviationIC_of_bic`, `payment_formula`, and
  `payment_equivalence` explicitly use the IPV specialization. Their
  public API pins change together with their statements.
- General mechanism clients import `MathEconLib.Mechanism`. The BIC regression
  consumes this umbrella, so a missing public export fails compilation.
- `BayesianPrior.insert_drop_eq_update` is shared by arbitrary dependent type
  profiles; the earlier auction-specific helper moves to that general layer.
- The scalar `toBidderProblem` still describes a fixed marginal menu.
  Conditional correlated menus generally depend on both true type and
  report and do not automatically satisfy the scalar envelope theorem.
  The all-purchase conditional adapter remains tracked in #212.

Expected revenue continues to integrate realized joint payments, with no BIC
or IPV prerequisite. The marginal-payment bridge requires independence and
measurable, integrable realized payments. The explicit payment hypotheses on
`revenue_equivalence` and `total_revenue` from the earlier #210 repair remain.

## Regression and verification map

- `MathEconLibTest/Auction/CorrelatedValues.lean`: the old false-positive
  inequalities still hold, but quasilinear BIC rejects the mechanism through a
  profitable conditional deviation. Truthful realized revenue is two.
  Squared-disagreement payments give a correlated BIC positive control for
  every real report; the old marginal inequalities reject that mechanism.
  Both examples also check the old marginal and repaired conditional IR
  outcomes in the corresponding directions.
- `MathEconLibTest/Auction/IndependentValues.lean`: the nonzero posted-price
  example constructs IPV BIC through the equivalence theorem, exposes its
  general conditional BIC proof, and applies the revenue bridge to obtain
  total expected revenue one quarter. It applies the migrated payment
  formula to derive the allocation integral one quarter.
- `MathEconLibTest/Mechanism/BayesianIC.lean`: a provably interdependent
  valuation environment satisfies quasilinear BIC over all real types/reports;
  applying `IsBIC.isBNE` certifies truthful Bayesian equilibrium. A separate
  two-good posted-price client supplies vector reports, proves quasilinear BIC
  for every report pair, instantiates a concrete prior, and checks payment.

Verification uses the full default `lake build`, regenerated and checked
library/test imports, public API pins, header/whitespace checks, transitive
standard-only axiom reports, and independent exact arithmetic. See the PR
for the tested commit and actual results. These checks do not close the
remaining all-purchase work or the other audit repairs in #214–#217.

`python3 scripts/check-bic-regressions.py` independently checks the finite
conditional/marginal counterexample arithmetic, realized receipts, and
independent-revenue calculations using exact fractions. Its finite report
checks supplement the Lean proofs over all real reports.

## Design and inheritance boundary

The general mechanism, environment, probability law and selected beliefs are
composed as explicit arguments. Scalar auction BIC and IPV BIC specialize that
same predicate. No second payoff or conditional-belief foundation is defined,
and incentive compatibility does not imply independence.

The narrow IPV class is an adapter for the existing bidder IC inference chain,
not a new definition of incentive compatibility or a selected model. The
ordinary general predicate remains the preferred interface for new clients.
Changing the legacy bidder class chain is a separate API migration.

The generic profile-update identity belongs to `BayesianPrior` with arbitrary
dependent type carriers. It is shared directly rather than reproved in the
auction specialization. Quasilinear BIC is exported by the public mechanism
umbrella and checked through that import.

The current interface already accepts vector and agent-specific type spaces.
The two-dimensional regression validates this without introducing another
carrier or BIC predicate. The larger affine-menu and implementability theory
is deferred to [design issue #221](https://github.com/matheconlib/matheconlib/issues/221).
That work should compose the general primitives and prove scalar agreement;
inheriting the scalar auction carrier would impose its real-report restriction.

## Reference

Roger B. Myerson (1985), *Bayesian equilibrium and incentive-compatibility:
an introduction*, §§1 and 5.
<https://home.uchicago.edu/~rmyerson/research/myerson1985pazner.pdf>

Matthew O. Jackson (2003), *Mechanism Theory*, §§4.1–4.7.
<https://web.stanford.edu/~jacksonm/mechtheo.pdf>
