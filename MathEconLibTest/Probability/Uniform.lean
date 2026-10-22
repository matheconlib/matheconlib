/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
import MathEconLib

/-!
Public-import checks linking uniform PMF integrals, finite distributions, and finite averages.
-/

namespace MathEconLibTest.Probability.Uniform

open MathEconLib.Probability MeasureTheory
open scoped BigOperators

example {α : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (f : α → ℝ) :
    (∫ a, f a ∂(PMF.uniformOfFintype α).toMeasure) =
      (FinDist.uniform (α := α)).expect f := by
  rw [PMF.integral_uniformOfFintype, FinDist.expect_uniform]

example {α : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α] :
    (FinDist.uniform (α := α)).toMeasure = (PMF.uniformOfFintype α).toMeasure := by
  simp [FinDist.toMeasure]

-- A payoff statistic on three outcomes uses the same finite-average identity as matching.
example : (FinDist.uniform (α := Fin 3)).expect (fun i ↦ (i.val + 1 : ℝ)) = 2 := by
  rw [FinDist.expect_uniform, Fintype.expect_eq_sum_div_card]
  norm_num [Fin.sum_univ_succ]

#print axioms PMF.integral_uniformOfFintype
#print axioms MathEconLib.Probability.FinDist.expect_uniform
#print axioms MathEconLib.Probability.FinDist.toPMF_uniform

end MathEconLibTest.Probability.Uniform
