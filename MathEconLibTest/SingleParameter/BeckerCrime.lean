/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
import MathEconLibExamples
import Mathlib.Order.Filter.Extr

/-!
# Becker model audit checks

These checks import the canonical example through its umbrella. They separate
optimal actions from the selected tie rule, verify the crime indicator's
integrability, and test the limits of the comparative-statics claims.
The model and its public declarations are unchanged.
-/

open MathEconLib MathEconLibExamples.SingleParameter MeasureTheory

namespace BeckerCrimeAudit

-- Mathlib's maximization predicate describes optimal actions independently
-- of the strategy stored in the problem. Both actions are optimal at the cutoff.
private theorem commit_isMaxOn_iff (lo hi p f v : ℝ) :
    IsMaxOn ((crimeProblem lo hi p f).payoff v) Set.univ CrimeDecision.commit ↔
      p * f ≤ v := by
  rw [isMaxOn_iff]
  constructor
  · intro h
    have h' := h .abstain (Set.mem_univ _)
    rw [crimeProblem_payoff_abstain, crimeProblem_payoff_commit] at h'
    exact sub_nonneg.mp h'
  · intro hv a _
    cases a with
    | commit => exact le_rfl
    | abstain =>
      rw [crimeProblem_payoff_abstain, crimeProblem_payoff_commit]
      exact sub_nonneg.mpr hv

private theorem abstain_isMaxOn_iff (lo hi p f v : ℝ) :
    IsMaxOn ((crimeProblem lo hi p f).payoff v) Set.univ CrimeDecision.abstain ↔
      v ≤ p * f := by
  rw [isMaxOn_iff]
  constructor
  · intro h
    have h' := h .commit (Set.mem_univ _)
    rw [crimeProblem_payoff_commit, crimeProblem_payoff_abstain] at h'
    exact sub_nonpos.mp h'
  · intro hv a _
    cases a with
    | commit =>
      rw [crimeProblem_payoff_commit, crimeProblem_payoff_abstain]
      exact sub_nonpos.mpr hv
    | abstain => exact le_rfl

example (lo hi p f : ℝ) :
    IsMaxOn ((crimeProblem lo hi p f).payoff (p * f)) Set.univ CrimeDecision.commit ∧
      IsMaxOn ((crimeProblem lo hi p f).payoff (p * f)) Set.univ CrimeDecision.abstain ∧
      (crimeProblem lo hi p f).strategy (p * f) = .commit := by
  exact ⟨(commit_isMaxOn_iff ..).mpr le_rfl, (abstain_isMaxOn_iff ..).mpr le_rfl,
    (crimeProblem_strategy_commit_iff ..).mpr le_rfl⟩

-- This is a genuine expectation even without bounded support or finite mean gains.
private theorem integrable_q (D : ValueDistribution) (lo hi p f : ℝ) :
    Integrable (crimeProblem lo hi p f).q (D : Measure ℝ) := by
  have h : (crimeProblem lo hi p f).q =
      (Set.Ici (p * f)).indicator (fun _ : ℝ ↦ (1 : ℝ)) := by
    funext v
    rw [crimeProblem_q]
    simp [Set.indicator]
  rw [h]
  exact (integrable_const (1 : ℝ)).indicator measurableSet_Ici

example (D : ValueDistribution) (lo hi p f : ℝ) :
    D.expectedAllocation (crimeProblem lo hi p f) ∈ Set.Icc (0 : ℝ) 1 := by
  rw [crimeProblem_expectedAllocation_eq_probAtLeast]
  exact ⟨D.probAtLeast_nonneg _, D.probAtLeast_le_one _⟩

-- Positive detection and a strictly higher fine need not give strict deterrence:
-- no type in this population crosses a cutoff. Its gain also lies outside [0, 2].
example :
    let D : ValueDistribution := (Measure.dirac (3 : ℝ)).toProbabilityMeasure
    D.expectedAllocation (crimeProblem 0 2 (1 / 2) 1) = 1 ∧
      D.expectedAllocation (crimeProblem 0 2 (1 / 2) 2) = 1 := by
  dsimp only
  rw [crimeProblem_expectedAllocation_eq_probAtLeast,
    crimeProblem_expectedAllocation_eq_probAtLeast]
  norm_num [ValueDistribution.probAtLeast, ProbabilityMeasure.coeFn_def]

-- Negative parameters lie outside the policy interpretation. These cases show
-- why the one-parameter corollaries retain their nonnegativity guards.
example :
    (crimeProblem (-2) 0 (-1) 1).q (-3 / 2) = 0 ∧
      (crimeProblem (-2) 0 (-1) 2).q (-3 / 2) = 1 := by
  rw [crimeProblem_q, crimeProblem_q]
  norm_num

example :
    (crimeProblem (-2) 0 (1 / 4) (-2)).q (-3 / 4) = 0 ∧
      (crimeProblem (-2) 0 (1 / 2) (-2)).q (-3 / 4) = 1 := by
  rw [crimeProblem_q, crimeProblem_q]
  norm_num

#print axioms commit_isMaxOn_iff
#print axioms abstain_isMaxOn_iff
#print axioms integrable_q

end BeckerCrimeAudit
