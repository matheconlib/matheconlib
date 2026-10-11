/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import MathEconLibTest.GameTheory.Transport

/-!
# Strategic equilibrium under constant action maps

The quadratic game and constant action maps from `Transport` give concrete examples of strategic
Nash equilibrium under action translation. The constant map to the optimal action is neither
injective nor surjective, but Nash equilibrium still pulls back. The constant map to a suboptimal
action makes every new action an equilibrium, although its image is not an equilibrium in the
original game.

## Main statements

* `optimalMap_neither_injective_nor_surjective`: The optimal map is neither injective nor
  surjective.
* `quadratic_translated_isNash` pulls equilibrium back through the optimal map.
* `quadratic_restricted_isNash` and `quadratic_restricted_image_not_isNash` show why the reverse
  implication can fail.

## Tags

strategic games, nash equilibrium, action translation
-/

@[expose] public section

open MathEconLib.GameTheory

namespace MathEconLibTest.GameTheory.Transport

/-- The constant optimal action map misses zero, so it is not surjective. -/
lemma optimalMap_not_surjective : ¬ Function.Surjective (optimalMap ()).1 := by
  intro h
  obtain ⟨a, ha⟩ := h 0
  norm_num [optimalMap] at ha

/-- The constant optimal map is neither injective nor surjective. -/
lemma optimalMap_neither_injective_nor_surjective :
    ¬ Function.Injective (optimalMap ()).1 ∧ ¬ Function.Surjective (optimalMap ()).1 :=
  ⟨optimalMap_not_injective, optimalMap_not_surjective⟩

/-- Choosing one is Nash in the quadratic game at every fixed true type. -/
lemma quadratic_optimal_isNash (θ : Unit → ℝ) :
    (game.toStrategicGame θ).IsNash (fun _ ↦ 1) := by
  rw [StrategicGame.isNash_iff]
  intro i a
  cases i
  change -(a - 1) ^ 2 ≤ -(1 - 1) ^ 2
  simpa using neg_nonpos.mpr (sq_nonneg (a - 1))

/-- Nash equilibrium pulls back through the constant optimal map without injectivity or
surjectivity. -/
lemma quadratic_translated_isNash (θ : Unit → ℝ) :
    ((game.toStrategicGame θ).comapActions (fun i ↦ (optimalMap i).1)).IsNash (fun _ ↦ 0) := by
  apply StrategicGame.IsNash.comapActions
  simpa only [optimalMap] using quadratic_optimal_isNash θ

/-- Restricting every action to zero makes all available deviations payoff-equivalent. -/
lemma quadratic_restricted_isNash (θ : Unit → ℝ) :
    ((game.toStrategicGame θ).comapActions (fun i ↦ (restrictedMap i).1)).IsNash
      (fun _ ↦ 0) := by
  rw [StrategicGame.isNash_iff]
  intro i a
  change (-((0 : ℝ) - 1) ^ 2) ≤ -((0 : ℝ) - 1) ^ 2
  exact le_rfl

/-- The image of the restricted equilibrium is not Nash because moving to one improves payoff. -/
lemma quadratic_restricted_image_not_isNash (θ : Unit → ℝ) :
    ¬ (game.toStrategicGame θ).IsNash (fun i ↦ (restrictedMap i).1 0) := by
  intro h
  have hdeviation := (StrategicGame.isNash_iff _ _).1 h () 1
  norm_num [BayesianGame.toStrategicGame_payoff, game, restrictedMap] at hdeviation

end MathEconLibTest.GameTheory.Transport

end
