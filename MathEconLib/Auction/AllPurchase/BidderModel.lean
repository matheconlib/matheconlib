/-
Copyright (c) 2026 Ruiz Chen, Scott Duke Kominers, Daniel Lyng, Jujian Zhang, Bo Cowgill.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiz Chen, Scott Duke Kominers, Daniel Lyng, Jujian Zhang, Bo Cowgill
-/
module

public import MathEconLib.Auction.Basic
public import MathEconLib.Mechanism.Auctions.AllPurchase.Spec

/-!
# All-purchase bidder models

`AllPurchaseBidderSpec` describes the scalar net-cost model used by the all-purchase bidding and
revenue-decomposition proofs. Its payments are purchase expenditure less resale value. This is an
auxiliary model of bidders' incentives: its `Mechanism.revenue` and `Auction.expectedRevenue` are
net costs, not the seller's monetary receipts.

`toMechanism` constructs the actual all-purchase mechanism, recording both prize shares and
purchases and charging gross expenditure. Its `AllPurchaseSpec.environment` includes resale value.
`utility_toMechanism` proves that this mechanism and environment reproduce every bidder utility
of the auxiliary scalar model, including at deviations. No action-domain restriction is imposed.

`AllPurchaseBidderModel` packages this scalar model without a coercion to `Auction`. Use
`expectedSellerRevenue β` for actual receipts and `expectedNetCost β` for bidder net costs.
Both require an explicit strategy. Access to the raw auction and its misleading revenue name
requires the deliberate `toNetCostAuction` projection.

The net-cost formula is adapted from Auctionlib/Mechanism/AllPurchase.lean (commit 384acbf).
The separation of receipts and resale value repairs the accounting issue reported by
@yoshiki-pramaana in https://github.com/matheconlib/matheconlib/issues/239.
-/

@[expose] public section

namespace MathEconLib.Mechanism.Auctions

universe u

/-- Scalar bidder model with net costs. The monetary mechanism is `toMechanism`; the revenue of
this auxiliary model is not seller revenue. -/
structure AllPurchaseBidderSpec {I : Type u} [Fintype I]
    (M : Mechanism I (fun _ ↦ ℝ) (I → ℝ)) where
  /-- Positive posted unit price. -/
  price : ℝ
  /-- The posted unit price is positive. -/
  price_pos : 0 < price
  /-- Per-edition resale value as a function of total purchases. -/
  φ : ℝ → ℝ
  /-- The scarcity schedule is continuous. -/
  φ_continuous : Continuous φ
  /-- The scarcity schedule is strictly decreasing. -/
  φ_strictAnti : StrictAnti φ
  /-- The unique strictly highest purchaser wins; highest ties receive no prize. -/
  usesStrictHighestBidAllocation : UsesStrictHighestBidAllocation M (fun o i ↦ o i)
  /-- The auxiliary model subtracts net cost from prize value. -/
  transfer_eq : ∀ i b, M.transfer i b = -((price - φ (∑ j, b j)) * b i)

namespace AllPurchaseBidderSpec

variable {I : Type u} [Fintype I]
variable {M : Mechanism I (fun _ ↦ ℝ) (I → ℝ)}

/-- Net cost in the auxiliary bidder model. -/
theorem payment_eq (spec : AllPurchaseBidderSpec M) (i : I) (b : I → ℝ) :
    M.payment i b = (spec.price - spec.φ (∑ j, b j)) * b i := by
  simp [Mechanism.payment, spec.transfer_eq]

/-- Prize shares of the bidder model lie in the unit interval. -/
theorem isUnitIntervalAllocation (spec : AllPurchaseBidderSpec M) :
    IsUnitIntervalAllocation M (fun o i ↦ o i) :=
  spec.usesStrictHighestBidAllocation.isUnitIntervalAllocation

/-- Outcomes carry both the prize shares and the purchased editions. -/
structure Outcome (I : Type u) where
  /-- Prize allocation shares. -/
  prize : I → ℝ
  /-- Purchased edition quantities. -/
  purchases : I → ℝ

/-- Actual seller receipts charge only the posted purchase price. -/
def toMechanism (spec : AllPurchaseBidderSpec M) :
    Mechanism I (fun _ ↦ ℝ) (Outcome I) where
  outcome b := ⟨M.outcome b, b⟩
  transfer i b := -(spec.price * b i)

/-- The actual mechanism satisfies the accounting and outcome requirements. -/
def toSpec (spec : AllPurchaseBidderSpec M) :
    AllPurchaseSpec spec.toMechanism Outcome.prize Outcome.purchases where
  price := spec.price
  price_pos := spec.price_pos
  φ := spec.φ
  φ_continuous := spec.φ_continuous
  φ_strictAnti := spec.φ_strictAnti
  usesStrictHighestBidAllocation := spec.usesStrictHighestBidAllocation
  purchases_eq _ := rfl
  transfer_eq _ _ := rfl

/-- Prize-only valuation in the scalar bidder model. -/
def prizeEnvironment :
    Mechanism.QuasilinearEnvironment I (fun _ ↦ ℝ) (I → ℝ) :=
  Mechanism.QuasilinearEnvironment.ofPrivate fun i s o ↦ s * o i

/-- Moving resale from net costs into outcome value preserves utility at every action profile. -/
theorem utility_toMechanism (spec : AllPurchaseBidderSpec M) (i : I) (θ b : I → ℝ) :
    spec.toSpec.environment.utility spec.toMechanism i θ b =
      prizeEnvironment.utility M i θ b := by
  change θ i * M.outcome b i + spec.φ (∑ j, b j) * b i + -(spec.price * b i) =
    θ i * M.outcome b i + M.transfer i b
  rw [spec.transfer_eq]
  ring

/-- All preferences over deviations agree on the unchanged action domain. -/
theorem preference_toMechanism (spec : AllPurchaseBidderSpec M) (i : I) (θ b c : I → ℝ) :
    (spec.toSpec.environment.utility spec.toMechanism i θ b ≤
        spec.toSpec.environment.utility spec.toMechanism i θ c) ↔
      prizeEnvironment.utility M i θ b ≤ prizeEnvironment.utility M i θ c := by
  rw [spec.utility_toMechanism, spec.utility_toMechanism]

end AllPurchaseBidderSpec

end MathEconLib.Mechanism.Auctions

namespace MathEconLib

open MeasureTheory ProbabilityTheory Mechanism.Auctions

/-- An all-purchase bidder model with an explicit escape hatch to the auxiliary net-cost auction.
There is no coercion to `Auction`: seller receipts and bidder net costs have distinct APIs. -/
structure AllPurchaseBidderModel (Ω : Type) [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] (n : ℕ) where
  /-- Auxiliary scalar auction for bidding proofs. Its payments and revenue are net costs. -/
  toNetCostAuction : Auction Ω n
  /-- Price, scarcity value, and prize rule for the auxiliary bidder model. -/
  spec : AllPurchaseBidderSpec toNetCostAuction.rules

namespace AllPurchaseBidderModel

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {n : ℕ} (A : AllPurchaseBidderModel Ω n)

/-- The monetary mechanism records purchases and charges gross expenditure. -/
def toMechanism := A.spec.toMechanism

/-- The monetary mechanism's valuations include prize value and resale value. -/
def environment := A.spec.toSpec.environment

/-- Actual seller receipts at the supplied purchase profile. -/
def sellerRevenue (b : Fin n → ℝ) : ℝ := A.toMechanism.revenue b

/-- Actual expected seller receipts under the explicitly supplied common strategy.
This totalized integral needs integrability for a finite-expectation interpretation. -/
noncomputable def expectedSellerRevenue (β : ℝ → ℝ) : ℝ :=
  𝔼[fun ω ↦ A.sellerRevenue (fun i ↦ β (A.toNetCostAuction.θ i ω))]

/-- Expected total bidder net cost under the supplied common strategy, including resale value.
This is not seller revenue. The integral is totalized. -/
noncomputable def expectedNetCost (β : ℝ → ℝ) : ℝ :=
  𝔼[fun ω ↦ ∑ i, A.spec.toSpec.netCost i (fun j ↦ β (A.toNetCostAuction.θ j ω))]

/-- Actual receipts equal posted price times total purchases. -/
theorem sellerRevenue_eq (b : Fin n → ℝ) :
    A.sellerRevenue b = A.spec.price * ∑ i, b i := A.spec.toSpec.revenue_eq b

/-- Seller revenue uses the same supplied strategy for every purchase on both sides. -/
theorem expectedSellerRevenue_eq (β : ℝ → ℝ) :
    A.expectedSellerRevenue β =
      A.spec.price * 𝔼[fun ω ↦ ∑ i, β (A.toNetCostAuction.θ i ω)] := by
  simp_rw [expectedSellerRevenue, A.sellerRevenue_eq]
  exact integral_const_mul _ _

/-- Integrable individual purchases give integrable actual seller receipts. -/
theorem sellerRevenue_integrable (β : ℝ → ℝ)
    (hβ : ∀ j, Integrable (fun ω ↦ β (A.toNetCostAuction.θ j ω)) ℙ) :
    Integrable (fun ω ↦ A.sellerRevenue (fun j ↦ β (A.toNetCostAuction.θ j ω))) ℙ := by
  simp_rw [A.sellerRevenue_eq]
  exact (integrable_finsetSum _ fun j _ ↦ hβ j).const_mul A.spec.price

end AllPurchaseBidderModel

end MathEconLib
