module

import Auctionlib.BidderProblem
import Auctionlib.SingleParameter.PostedPrice
import Auctionlib.SingleParameter.Revelation

/-!
# Compatibility Checks for the Single-Parameter Foundation

This file contains compile-time examples rather than new library definitions.
It checks the two paths that the first pricing-foundations pull request is
intended to support:

1. a new problem with a non-real action type can use the complete generic IC,
   envelope, payment, and participation API;
2. an existing `BidderProblem` can use the same general results without
   changing its original public assumptions or conclusions;
3. the single-agent revelation principle: reduction to a direct problem
   preserves the interim quantities and yields universal IC.

If a later refactor accidentally breaks one of these paths, this module will
fail to compile as part of the ordinary `lake build`. It belongs to the
separate `AuctionlibTest` library so compile-time checks are not part of the
production `Auctionlib` import graph.
-/

open Set MeasureTheory

namespace SingleParameterCompatibility

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

/-! ## Strategy replacement and reduced forms -/

section ReducedForm

variable {Action : Type*} (P : SingleParameterProblem Action)

/-- Replacing the strategy with itself changes no data. -/
example :
    P.withStrategy P.strategy = P :=
  P.withStrategy_self

/-- Reduction preserves the induced allocation. -/
example :
    P.reduce.q = P.q :=
  P.reduce_q

/-- Reduction preserves on-strategy utility. -/
example :
    P.reduce.U = P.U :=
  P.reduce_U

/-- A reduced report has the payoff of its corresponding original action. -/
example (v w : ℝ) :
    P.reduce.payoff v w = P.payoff v (P.strategy w) :=
  P.reduce_payoff v w

/-- Envelope IC is available automatically on the reduced form. -/
example [SingleParameterProblem.HasEnvelopeIC P] :
    SingleParameterProblem.HasEnvelopeIC P.reduce :=
  inferInstance

/-- Envelope IC can be transferred back without a reverse instance. -/
example (hIC : SingleParameterProblem.HasEnvelopeIC P.reduce) :
    SingleParameterProblem.HasEnvelopeIC P :=
  SingleParameterProblem.hasEnvelopeIC_of_reduce hIC

/-- Type-deviation IC is available automatically on the reduced form. -/
example [SingleParameterProblem.HasTypeDeviationIC P] :
    SingleParameterProblem.HasTypeDeviationIC P.reduce :=
  inferInstance

/-- Type-deviation IC can also be transferred back explicitly. -/
example (hIC : SingleParameterProblem.HasTypeDeviationIC P.reduce) :
    SingleParameterProblem.HasTypeDeviationIC P :=
  SingleParameterProblem.hasTypeDeviationIC_of_reduce hIC

/-- The reduced form can invoke the generic envelope theorem directly. -/
example [SingleParameterProblem.HasEnvelopeIC P]
    (v : ℝ) (hv : v ∈ P.typeInterval) :
    P.U v = P.U P.lowestType + ∫ w in P.lowestType..v, P.q w :=
  P.reduce.integral_rep v hv

end ReducedForm

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

/-! ## The single-agent revelation principle -/

section Revelation

universe u

variable {Action : Type u} (P : SingleParameterProblem Action)

/-- The reduced form has the identity strategy. -/
example : P.reduce.HasIdentityStrategy :=
  P.reduce_hasIdentityStrategy

/-- Reduction is idempotent. -/
example : P.reduce.reduce = P.reduce :=
  P.reduce_reduce

/-- Type-deviation IC yields truthfulness of the reduced form: universal IC
over in-interval reports. -/
example [SingleParameterProblem.HasTypeDeviationIC P] :
    SingleParameterProblem.HasUniversalIC P.reduce P.typeInterval :=
  inferInstance

/-- The headline single-agent revelation principle. -/
example [SingleParameterProblem.HasTypeDeviationIC P] :
    ∃ D : SingleParameterProblem ℝ,
      D.HasIdentityStrategy ∧
      SingleParameterProblem.HasUniversalIC D D.typeInterval ∧
      D.lowestType = P.lowestType ∧
      D.highestType = P.highestType ∧
      D.q = P.q ∧
      D.U = P.U ∧
      ∀ w : ℝ, D.payment w = P.payment (P.strategy w) :=
  P.revelation_principle

/-- Participation holds for the reduced form iff it holds for the original. -/
example : P.reduce.IsIndividuallyRational ↔ P.IsIndividuallyRational :=
  P.reduce_isIndividuallyRational

/-- The binding participation constraint at the lowest type: likewise. -/
example : P.reduce.HasZeroLowestTypeUtility ↔ P.HasZeroLowestTypeUtility :=
  P.reduce_hasZeroLowestTypeUtility

end Revelation

/-! ## An example: the posted price `1/2` on `[0, 1]` -/

section RevelationPostedPrice

local notation "PP" => SingleParameterProblem.postedPriceProblem 0 1 (1/2)

/-- The revelation principle instantiated at a concrete problem. The direct
problem it produces has type interval `[0, 1]`, the same allocation and
utility as the threshold strategy, and collects at report `w` what the
original rules collect at the action the strategy chooses for `w`. -/
example :
    ∃ D : SingleParameterProblem ℝ,
      D.HasIdentityStrategy ∧
      SingleParameterProblem.HasUniversalIC D D.typeInterval ∧
      D.lowestType = 0 ∧
      D.highestType = 1 ∧
      D.q = (PP).q ∧
      D.U = (PP).U ∧
      ∀ w : ℝ, D.payment w = (PP).payment ((PP).strategy w) :=
  (PP).revelation_principle

/-- Truthful reporting is incentive compatible in the direct posted-price
problem, over reports in `[0, 1]`. -/
example :
    SingleParameterProblem.HasUniversalIC (PP).reduce (PP).typeInterval :=
  inferInstance

/-- In the direct problem, a report of `3/4` wins the object. -/
example : (PP).reduce.q (3/4) = 1 := by
  simp only [SingleParameterProblem.reduce_q,
    SingleParameterProblem.postedPriceProblem_q]
  norm_num

/-- In the direct problem, a report of `1/4` does not. -/
example : (PP).reduce.q (1/4) = 0 := by
  simp only [SingleParameterProblem.reduce_q,
    SingleParameterProblem.postedPriceProblem_q]
  norm_num

end RevelationPostedPrice

end SingleParameterCompatibility
