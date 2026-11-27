/-
Copyright (c) 2026 Scott Duke Kominers, Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Duke Kominers, Bo Cowgill
-/
module

public import MathEconLib.Auction.AllPurchase.LinearScarcity

/-!
# An all-purchase model with two bidders

These examples use a posted unit price of `2` and scarcity value `3 - B` at total purchases `B`.
The unique highest purchaser receives the prize, and a tie leaves it unallocated. The probability
space and the two bidders' values remain parameters. The deterministic welfare and uniform
examples share the auxiliary scalar bidder model and its associated monetary mechanism.

`bidderRules` subtract net costs for the existing incentive analysis. `monetaryRules` instead
record purchases and charge gross expenditure. Pair `monetarySpec` with
`monetarySpec.environment bidderSpec.φ` to value resale separately from monetary transfers.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open MathEconLib.Mechanism.Auctions

namespace MathEconLib.Examples.AllPurchase

/-- Auxiliary scalar bidder rules: transfers subtract net costs, not seller receipts. -/
def bidderRules : Mechanism (Fin 2) (fun _ ↦ ℝ) (Fin 2 → ℝ) where
  outcome b i := {r | ∀ j ≠ i, r j < r i}.indicator 1 b
  transfer i b := -((2 - (3 - ∑ j, b j)) * b i)

/-- Each prize-allocation coordinate is measurable in the bid profile. -/
theorem bidderRules_outcome_measurable (i : Fin 2) :
    Measurable (fun b ↦ bidderRules.outcome b i) := by
  classical
  change Measurable ({b : Fin 2 → ℝ | ∀ j ≠ i, b j < b i}.indicator (1 : (Fin 2 → ℝ) → ℝ))
  apply measurable_const.indicator
  have hset : {b : Fin 2 → ℝ | ∀ j ≠ i, b j < b i} =
      ⋂ j : Fin 2, ⋂ (_ : j ≠ i), {b : Fin 2 → ℝ | b j < b i} := by
    ext b
    simp
  rw [hset]
  exact MeasurableSet.iInter fun j ↦ MeasurableSet.iInter fun _ ↦
    measurableSet_lt (measurable_pi_apply j) (measurable_pi_apply i)

/-- Price and resale schedule for the auxiliary net-cost analysis. -/
def bidderSpec : AllPurchaseBidderSpec bidderRules where
  price := 2
  price_pos := by norm_num
  φ := fun total ↦ 3 - total
  φ_continuous := continuous_const.sub continuous_id
  φ_strictAnti := fun _ _ h ↦ sub_lt_sub_left h 3
  usesStrictHighestBidAllocation _ := rfl
  transfer_eq _ _ := rfl

/-- Actual monetary rules record purchases and charge the full posted price. -/
def monetaryRules :
    Mechanism (Fin 2) (fun _ ↦ ℝ) (AllPurchaseBidderSpec.Outcome (Fin 2)) :=
  bidderSpec.toMechanism

/-- The monetary specification is independent of the resale valuation. -/
def monetarySpec : AllPurchaseSpec monetaryRules (fun o ↦ o.prize) (fun o ↦ o.purchases) :=
  bidderSpec.toSpec

/-- Equip the shared bidder model with measurable values and stated bounds `[0, 2]`.
Containment in these bounds and distributional assumptions are proved by each example. -/
def auction {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (θ : Fin 2 → Ω → ℝ) (hθ : ∀ i, Measurable (θ i)) : LinearScarcityAuction Ω 2 where
  toNetCostAuction := {
    rules := bidderRules
    outcome_measurable := bidderRules_outcome_measurable
    θmin := fun _ ↦ 0
    θmax := fun _ ↦ 2
    θ := θ
    θ_measurable := hθ
  }
  spec := bidderSpec
  φ_bar := 3
  α_coeff := 1
  α_pos := by norm_num
  φ_bar_pos := by norm_num
  scarcity_is_linear := by funext b; simp [bidderSpec]

end MathEconLib.Examples.AllPurchase

end

end
