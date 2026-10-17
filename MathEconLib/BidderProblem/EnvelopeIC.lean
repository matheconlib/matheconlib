/-
Copyright (c) 2026 Bo Cowgill, Jujian Zhang, Scott Duke Kominers, Ruiz Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill, Jujian Zhang, Scott Duke Kominers, Ruiz Chen
-/
module

public import MathEconLib.BidderProblem.Basic
public import MathEconLib.SingleParameter.EnvelopeIC

/-!
# Envelope IC (Level 0) for `BidderProblem`

This file preserves the original bidder-facing envelope API while obtaining
its general analytic conclusions from `SingleParameterProblem`.

The conversion `BidderProblem.toSingleParameterProblem` treats a real-valued
bid as the action, `winProb` as the allocation rule, and `cost` as the payment
rule. The compatibility lemmas in `BidderProblem.Basic` show that the
conversion leaves `payoff`, `q`, and `U` unchanged.

Consequently, existing auction code can continue to use:

* `BidderProblem.HasEnvelopeIC`;
* `BidderProblem.lipschitz`;
* `BidderProblem.q_monotoneOn`;
* `BidderProblem.aeDifferentiable`;
* `BidderProblem.integral_rep`.

Their statements have not changed. The proofs now reuse the action-parametric
single-parameter results.
-/

namespace MathEconLib

@[expose] public section

open Set MeasureTheory

namespace BidderProblem

variable (B : BidderProblem)

/-- **Envelope IC** (Level 0): the increasing-differences form of incentive
compatibility. This is the weakest bidder IC condition and is sufficient for
the envelope theorem. -/
class HasEnvelopeIC (B : BidderProblem) : Prop where
  envelopeIC : ∀ s ∈ B.typeInterval, ∀ s' ∈ B.typeInterval,
    (s - s') * B.q s' ≤ B.U s - B.U s'

/-- Bidder envelope IC supplies envelope IC for the corresponding general
single-parameter problem. -/
instance instSingleParameterHasEnvelopeIC
    {B : BidderProblem} [hIC : HasEnvelopeIC B] :
    SingleParameterProblem.HasEnvelopeIC B.toSingleParameterProblem where
  envelopeIC v hv v' hv' := by
    simpa using hIC.envelopeIC v hv v' hv'

/-- Conversely, general envelope IC for the converted problem supplies the
original bidder envelope IC condition.

This direction is an explicit theorem rather than an instance, which avoids a
typeclass-search cycle between the two equivalent formulations. -/
theorem hasEnvelopeIC_of_toSingleParameterProblem
    {B : BidderProblem}
    (hIC : SingleParameterProblem.HasEnvelopeIC B.toSingleParameterProblem) :
    HasEnvelopeIC B where
  envelopeIC v hv v' hv' := by
    simpa using hIC.envelopeIC v hv v' hv'

/-! ## Envelope theorem -/

/-- `U` is `1`-Lipschitz on the type interval. -/
theorem lipschitz [HasEnvelopeIC B] :
    LipschitzOnWith 1 B.U B.typeInterval := by
  simpa using B.toSingleParameterProblem.lipschitz

/-- `q` is monotone on the type interval. -/
theorem q_monotoneOn [HasEnvelopeIC B] :
    MonotoneOn B.q B.typeInterval := by
  simpa using B.toSingleParameterProblem.q_monotoneOn

/-- `U` has derivative `q` almost everywhere on the type interval. -/
theorem aeDifferentiable [HasEnvelopeIC B] :
    ∀ᵐ s ∂volume.restrict B.typeInterval, HasDerivAt B.U (B.q s) s := by
  simpa using B.toSingleParameterProblem.aeDifferentiable

/-- Integral representation:
`U(s) = U(lowestType) + ∫ lowestType..s, q(ψ) dψ`. -/
theorem integral_rep [HasEnvelopeIC B]
    (s : ℝ) (hs : s ∈ B.typeInterval) :
    B.U s = B.U B.lowestType + ∫ ψ in B.lowestType..s, B.q ψ := by
  simpa using B.toSingleParameterProblem.integral_rep s hs

/-! ## Additional bidder consequences -/

/-- **Weak monotonicity.** If `winProb` is strictly monotone, then `strategy`
is weakly increasing on the type interval.

The general theorem supplies monotonicity of `q = winProb ∘ strategy`;
strict monotonicity of `winProb` then permits comparison of the bids. -/
theorem strategy_monotoneOn [HasEnvelopeIC B]
    (hG : StrictMono B.winProb) :
    MonotoneOn B.strategy B.typeInterval :=
  fun _ hx _ hy hxy => hG.le_iff_le.mp (B.q_monotoneOn hx hy hxy)

/-- If the lowest type has nonnegative utility, then every type in the type
interval has nonnegative utility. -/
theorem U_nonneg [HasEnvelopeIC B]
    (hU0 : 0 ≤ B.U B.lowestType) (v : ℝ) (hv : v ∈ B.typeInterval) :
    0 ≤ B.U v := by
  simpa using B.toSingleParameterProblem.U_nonneg hU0 v hv

end BidderProblem

end

end MathEconLib
