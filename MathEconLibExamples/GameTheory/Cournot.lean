/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.GameTheory.Strategic.Existence
import Mathlib.MeasureTheory.Measure.DiracProba

/-!
# A compact continuous Cournot game

Two firms simultaneously choose quantities in the real interval `[0,1]`, their capacity constraints.
Both know the inverse demand `2 - q₀ - q₁` and the constant unit production cost `1`. Each firm's
payoff is its profit: quantity times price minus production cost. Producing zero is feasible and
gives zero profit, with no fixed cost. Price is nonnegative on every feasible profile.

This is one concrete instance of `StrategicGame`, not a general Cournot model family. It reuses the
library's mixed strategies, expected payoffs, and Nash predicate. Firms are risk neutral and may
independently randomize using any Borel probability measure on `[0,1]`; a unilateral deviation may
replace that firm's entire law. Compactness and continuity give integrability under every such
profile, so the payoff integrals are genuine expected profits.

`exists_mixedNash` directly applies `StrategicGame.exists_isMixedNash_of_isCompact` and derives
nonnegative equilibrium expected profits from the zero-production deviation. Quantities are not
discretized. Existence allows Dirac strategies; this result does not select an equilibrium or claim
uniqueness or nondegenerate randomization.

## Main statements

* `payoff_integrable`: Every firm's profit is integrable under every independent mixed profile.
* `mixedNash_payoff_nonneg`: Every mixed equilibrium gives each firm nonnegative expected profit.
* `exists_mixedNash`: A mixed equilibrium with nonnegative expected profits exists.

## Tags

cournot competition, compact games, mixed strategies, nash equilibrium
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityMeasure MathEconLib.GameTheory

namespace MathEconLibExamples.GameTheory.Cournot

/-- A firm's feasible output, with capacity one and zero production allowed. -/
abbrev Quantity := Set.Icc (0 : ℝ) 1

instance : Nonempty Quantity := ⟨⟨0, by norm_num⟩⟩

/-- The action space is a continuum, not a finite grid. -/
instance : Infinite Quantity := Set.Icc.infinite (by norm_num)

/-- Market price at a feasible quantity profile. -/
def price (q : Fin 2 → Quantity) : ℝ := 2 - (q 0 : ℝ) - (q 1 : ℝ)

/-- Capacity constraints keep market price nonnegative. -/
lemma price_nonneg (q : Fin 2 → Quantity) : 0 ≤ price q := by
  have h0 := (q 0).property.2
  have h1 := (q 1).property.2
  dsimp [price]
  linarith

/-- Profit is revenue minus the cost of producing the firm's quantity at unit cost one. -/
def game : StrategicGame (Fin 2) (fun _ ↦ Quantity) ℝ where
  payoff i q := (q i : ℝ) * (price q - 1)

/-- The inherited interval topology makes each firm's profit jointly continuous in quantities. -/
instance : game.Continuous where
  continuous_payoff i :=
    (continuous_subtype_val.comp (continuous_apply i)).mul
      (((continuous_const.sub
        (continuous_subtype_val.comp (continuous_apply 0))).sub
        (continuous_subtype_val.comp (continuous_apply 1))).sub continuous_const)

/-- Continuous profits on a compact profile space are integrable under every mixed profile. -/
lemma payoff_integrable (σ : Fin 2 → ProbabilityMeasure Quantity) (i : Fin 2) :
    Integrable (game.payoff i) (Measure.pi (fun j ↦ (σ j : Measure Quantity))) :=
  (StrategicGame.Continuous.continuous_payoff (G := game) i).integrable

private def zeroQuantity : Quantity := ⟨0, by norm_num⟩

private lemma mixed_payoff_zero (σ : Fin 2 → ProbabilityMeasure Quantity) (i : Fin 2) :
    game.mixedExtension.payoff i (Function.update σ i (diracProba zeroQuantity)) = 0 := by
  change (∫ q, game.payoff i q
    ∂Measure.pi (fun j ↦ (Function.update σ i (diracProba zeroQuantity) j :
      Measure Quantity))) = 0
  have hi : ∀ᵐ q ∂Measure.pi
      (fun j ↦ (Function.update σ i (diracProba zeroQuantity) j : Measure Quantity)),
      q i = zeroQuantity := by
    apply (Measure.tendsto_eval_ae_ae (i := i)
      (μ := fun j ↦ (Function.update σ i (diracProba zeroQuantity) j :
        Measure Quantity))).eventually (p := fun x ↦ x = zeroQuantity)
    simpa only [Function.update_self] using (ae_eq_dirac (fun x : Quantity ↦ x))
  apply integral_eq_zero_of_ae
  filter_upwards [hi] with q hq
  simp [game, hq, zeroQuantity]

/-- Producing zero is an admissible deviation, so equilibrium expected profit cannot be negative. -/
theorem mixedNash_payoff_nonneg (σ : Fin 2 → ProbabilityMeasure Quantity)
    (hσ : game.IsMixedNash σ) (i : Fin 2) :
    0 ≤ game.mixedExtension.payoff i σ := by
  have h := ((StrategicGame.isMixedNash_iff game σ).1 hσ).2 i
    (diracProba zeroQuantity) (payoff_integrable _ i)
  simpa only [mixed_payoff_zero] using h

/-- Compact mixed-game existence supplies an equilibrium with nonnegative expected profits. -/
theorem exists_mixedNash :
    ∃ σ : Fin 2 → ProbabilityMeasure Quantity,
      game.IsMixedNash σ ∧ ∀ i, 0 ≤ game.mixedExtension.payoff i σ := by
  obtain ⟨σ, hσ⟩ := game.exists_isMixedNash_of_isCompact
  exact ⟨σ, hσ, mixedNash_payoff_nonneg σ hσ⟩

end MathEconLibExamples.GameTheory.Cournot

end
