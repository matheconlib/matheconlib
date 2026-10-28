/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLibExamples

/-!
# Cournot client regression checks

Import the worked development through the examples umbrella. Check the existence conclusion and
two profit calculations: Output one half against zero earns one quarter; full capacity by both
firms loses one each. Nonnegative equilibrium profit is therefore a substantive incentive result,
not a restriction imposed on all payoffs.
-/

open MeasureTheory MathEconLibExamples.GameTheory.Cournot

namespace MathEconLibTest.GameTheory.Cournot

example : Infinite Quantity := inferInstance

example : ∃ σ : Fin 2 → ProbabilityMeasure Quantity,
    game.IsMixedNash σ ∧ ∀ i, 0 ≤ game.mixedExtension.payoff i σ :=
  exists_mixedNash

example : game.payoff 0 ![⟨1 / 2, by norm_num⟩, ⟨0, by norm_num⟩] = 1 / 4 := by
  norm_num [game, price]

example (i : Fin 2) : game.payoff i (fun _ ↦ ⟨1, by norm_num⟩) = -1 := by
  norm_num [game, price]

end MathEconLibTest.GameTheory.Cournot
