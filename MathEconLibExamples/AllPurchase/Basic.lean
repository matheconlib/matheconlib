module

public import MathEconLib.Auction.AllPurchase.LinearScarcity

/-!
# A two-bidder all-purchase auction

These examples use a posted unit price of two and scarcity value `3 - B` at total purchases `B`.
The unique highest purchaser receives the prize, and a tie leaves it unallocated. The probability
space and the two bidders' values remain parameters, so the deterministic welfare example and the
uniform equilibrium example use exactly the same mechanism.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open MathEconLib.Mechanism.Auctions

namespace MathEconLib.Examples.AllPurchase

/-- The shared price-two mechanism with scarcity value `3 - B`. -/
def rules : Mechanism (Fin 2) (fun _ => ℝ) (Fin 2 → ℝ) where
  outcome b i := {r | ∀ j ≠ i, r j < r i}.indicator 1 b
  transfer i b := -((2 - (3 - ∑ j, b j)) * b i)

/-- Each prize-allocation coordinate is measurable in the bid profile. -/
theorem rules_outcome_measurable (i : Fin 2) :
    Measurable (fun b => rules.outcome b i) := by
  classical
  change Measurable ({b : Fin 2 → ℝ | ∀ j ≠ i, b j < b i}.indicator (1 : (Fin 2 → ℝ) → ℝ))
  apply measurable_const.indicator
  have hset : {b : Fin 2 → ℝ | ∀ j ≠ i, b j < b i} =
      ⋂ j : Fin 2, ⋂ (_ : j ≠ i), {b : Fin 2 → ℝ | b j < b i} := by
    ext b
    simp
  rw [hset]
  exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
    measurableSet_lt (measurable_pi_apply j) (measurable_pi_apply i)

/-- The shared mechanism satisfies the library's all-purchase specification. -/
def spec : AllPurchaseSpec rules (fun o i => o i) where
  price := 2
  price_pos := by norm_num
  φ := fun total => 3 - total
  φ_continuous := continuous_const.sub continuous_id
  φ_strictAnti := fun _ _ h => sub_lt_sub_left h 3
  usesStrictHighestBidAllocation _ := rfl
  transfer_eq _ _ := rfl

/-- Equip the shared mechanism with any measurable pair of values, with stated bounds `[0, 2]`.
Containment of values in these bounds and other distributional assumptions are proved separately
for each example. -/
def auction {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (θ : Fin 2 → Ω → ℝ) (hθ : ∀ i, Measurable (θ i)) : LinearScarcityAuction Ω 2 where
  rules := rules
  outcome_measurable := rules_outcome_measurable
  θmin := fun _ => 0
  θmax := fun _ => 2
  θ := θ
  θ_measurable := hθ
  spec := spec
  φ_bar := 3
  α_coeff := 1
  α_pos := by norm_num
  φ_bar_pos := by norm_num
  scarcity_is_linear := by funext b; simp [spec]

end MathEconLib.Examples.AllPurchase
