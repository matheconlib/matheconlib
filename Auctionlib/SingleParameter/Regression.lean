module

import Auctionlib.BidderProblem
import Auctionlib.SingleParameter.PostedPrice

/-!
# Regression Checks for the Single-Parameter Foundation

This file contains compile-time examples rather than new library definitions.
It checks the two paths that the first pricing-foundations pull request is
intended to support:

1. a new problem with a non-real action type can use the complete generic IC,
   envelope, payment, and participation API;
2. an existing `BidderProblem` can use the same general results without
   changing its original public assumptions or conclusions.

If a later refactor accidentally breaks one of these paths, this module will
fail to compile as part of the ordinary `lake build`.
-/

open Set MeasureTheory

namespace SingleParameterRegression

/-! ## A new problem with a finite action type -/

section PostedPrice

variable (lowestType highestType price : ℝ)

local notation "P" =>
  SingleParameterProblem.postedPriceProblem lowestType highestType price

/-- The concrete posted-price instance provides the strongest generic IC
condition. -/
example :
    SingleParameterProblem.HasUniversalIC P
      (Set.univ : Set SingleParameterProblem.PurchaseDecision) :=
  inferInstance

/-- The generic instance chain exposes type-deviation IC. -/
example :
    SingleParameterProblem.HasTypeDeviationIC P :=
  inferInstance

/-- The same chain exposes envelope IC. -/
example :
    SingleParameterProblem.HasEnvelopeIC P :=
  inferInstance

/-- Consequently, the generic allocation-monotonicity theorem applies. -/
example :
    MonotoneOn (P).q (P).typeInterval :=
  (P).q_monotoneOn

/-- The generic envelope representation applies to the finite-action problem. -/
example (v : ℝ) (hv : v ∈ (P).typeInterval) :
    (P).U v =
      (P).U (P).lowestType + ∫ w in (P).lowestType..v, (P).q w :=
  (P).integral_rep v hv

/-- The generic payment identity also applies without specializing the action
type to real-valued bids. -/
example (v : ℝ) (hv : v ∈ (P).typeInterval) :
    (P).payment ((P).strategy v) =
      v * (P).q v - (P).U (P).lowestType -
        ∫ w in (P).lowestType..v, (P).q w :=
  (P).payment_identity v hv

/-- The posted-price construction separately supplies participation. -/
example :
    (P).IsIndividuallyRational :=
  SingleParameterProblem.postedPriceProblem_isIndividuallyRational
    lowestType highestType price

end PostedPrice

/-! ## Preservation of the existing bidder API -/

section BidderProblem

variable (B : BidderProblem)

/-- Existing bidder envelope IC automatically supplies general envelope IC. -/
example [BidderProblem.HasEnvelopeIC B] :
    SingleParameterProblem.HasEnvelopeIC B.toSingleParameterProblem :=
  inferInstance

/-- Existing bidder type-deviation IC automatically supplies its general
counterpart. -/
example [BidderProblem.HasTypeDeviationIC B] :
    SingleParameterProblem.HasTypeDeviationIC B.toSingleParameterProblem :=
  inferInstance

/-- Applying the general payment theorem reproduces the original bidder
payment statement. -/
example [BidderProblem.HasTypeDeviationIC B]
    (v : ℝ) (hv : v ∈ B.typeInterval) :
    B.cost (B.strategy v) =
      v * B.q v - B.U B.lowestType -
        ∫ w in B.lowestType..v, B.q w := by
  simpa using B.toSingleParameterProblem.payment_identity v hv

/-- The explicit reverse bridge recovers bidder envelope IC without creating
a typeclass-search cycle. -/
example
    (hIC :
      SingleParameterProblem.HasEnvelopeIC B.toSingleParameterProblem) :
    BidderProblem.HasEnvelopeIC B :=
  BidderProblem.hasEnvelopeIC_of_toSingleParameterProblem hIC

/-- The corresponding reverse bridge also exists for type-deviation IC. -/
example
    (hIC :
      SingleParameterProblem.HasTypeDeviationIC B.toSingleParameterProblem) :
    BidderProblem.HasTypeDeviationIC B :=
  BidderProblem.hasTypeDeviationIC_of_toSingleParameterProblem hIC

variable (S : Set ℝ)

/-- Existing bidder universal IC automatically supplies general universal IC
over the same feasible set. -/
example [BidderProblem.HasUniversalIC B S] :
    SingleParameterProblem.HasUniversalIC B.toSingleParameterProblem S :=
  inferInstance

/-- Universal IC also has an explicit reverse bridge. -/
example
    (hIC :
      SingleParameterProblem.HasUniversalIC B.toSingleParameterProblem S) :
    BidderProblem.HasUniversalIC B S :=
  BidderProblem.hasUniversalIC_of_toSingleParameterProblem hIC

end BidderProblem

end SingleParameterRegression
