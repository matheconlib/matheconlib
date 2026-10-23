/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
import MathEconLibExamples.SingleParameter.BeckerCrime

open MathEconLib MathEconLibExamples.SingleParameter

namespace Manual.BeckerResearch

/-- For a fixed distribution and nonnegative detection probability, a higher fine weakly
reduces the aggregate crime rate. -/
theorem aggregateCrime_antitone_in_fine
    (D : ValueDistribution) (lo hi p f₁ f₂ : ℝ)
    (hp : 0 ≤ p) (hf : f₁ ≤ f₂) :
    D.expectedAllocation (crimeProblem lo hi p f₂) ≤
      D.expectedAllocation (crimeProblem lo hi p f₁) := by
  apply crimeProblem_expectedAllocation_antitone_in_expectedSanction
  exact mul_le_mul_of_nonneg_left hf hp

example (D : ValueDistribution) :
    D.expectedAllocation (crimeProblem 0 2 (1 / 2) 3) ≤
      D.expectedAllocation (crimeProblem 0 2 (1 / 2) 2) := by
  apply aggregateCrime_antitone_in_fine
  all_goals norm_num

example :
    let D : ValueDistribution := (MeasureTheory.Measure.dirac (1 : ℝ)).toProbabilityMeasure
    D.expectedAllocation (crimeProblem 0 2 (1 / 2) 2) = 1 ∧
      D.expectedAllocation (crimeProblem 0 2 (1 / 2) 3) = 0 := by
  dsimp only
  rw [crimeProblem_expectedAllocation_eq_probAtLeast,
    crimeProblem_expectedAllocation_eq_probAtLeast]
  norm_num [ValueDistribution.probAtLeast, MeasureTheory.ProbabilityMeasure.coeFn_def]

example (D : ValueDistribution) (lo hi f₁ f₂ : ℝ) :
    D.expectedAllocation (crimeProblem lo hi 0 f₂) =
      D.expectedAllocation (crimeProblem lo hi 0 f₁) := by
  rw [crimeProblem_expectedAllocation_eq_probAtLeast,
    crimeProblem_expectedAllocation_eq_probAtLeast]
  simp

end Manual.BeckerResearch

#print axioms Manual.BeckerResearch.aggregateCrime_antitone_in_fine
