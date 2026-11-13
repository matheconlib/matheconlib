/-
Copyright (c) 2026 Siyang Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siyang Liu
-/
module

public import MathEconLib.Decision.RiskAversion
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# Risk aversion over finite lotteries: worked examples

Checked applications of `LotteryRiskAverse`:

* a two-outcome fair coin, where the square root satisfies `E[√X] = 3/2 ≤ √(5/2) = √E[X]`;
* a point mass, where the inequality is an equality for every utility;
* a zero-probability outcome outside the domain, which the definition does not constrain;
* the convex utility `x ↦ x²`, which fails the definition on the whole real line;
* a mean that stays in a convex domain containing the positive-probability outcomes;
* a constant utility on `{0, 1}`, which shows why the converse to concavity needs a convex domain.
-/

@[expose] public section

open MathEconLib.Probability MathEconLib.Decision

namespace MathEconLib.Decision.RiskAversionExamples

/-- The square root is risk averse against finite lotteries on `[0, ∞)`. -/
theorem lotteryRiskAverse_sqrt : LotteryRiskAverse Real.sqrt (Set.Ici 0) :=
  lotteryRiskAverse_of_concaveOn Real.strictConcaveOn_sqrt.concaveOn

/-- Two-outcome application. The fair coin on outcomes `1` and `4` gives expected square root
`3/2` and expected outcome `5/2`, and the risk-aversion inequality yields `3/2 ≤ √(5/2)`. -/
theorem coin_sqrt_le : (3 / 2 : ℝ) ≤ Real.sqrt (5 / 2) := by
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have h := lotteryRiskAverse_sqrt (Fin 2) (FinDist.uniform : FinDist (Fin 2)) ![1, 4] (by
    intro a _
    fin_cases a <;> norm_num)
  have hu : (FinDist.uniform : FinDist (Fin 2)).expect (Real.sqrt ∘ ![1, 4]) = 3 / 2 := by
    norm_num [FinDist.expect_eq_sum, Fin.sum_univ_two, h4]
  have hx : (FinDist.uniform : FinDist (Fin 2)).expect (![1, 4] : Fin 2 → ℝ) = 5 / 2 := by
    norm_num [FinDist.expect_eq_sum, Fin.sum_univ_two]
  rw [hu, hx] at h
  exact h

/-- Boundary case: a point mass gives equality for every utility, so it imposes no restriction. -/
theorem pure_expect_eq (u : ℝ → ℝ) {α : Type} [Fintype α] [DecidableEq α] (a : α)
    (x : α → ℝ) :
    (FinDist.pure a).expect (u ∘ x) = u ((FinDist.pure a).expect x) := by
  simp [FinDist.expect_pure]

/-- Boundary case: outcome `1` has zero probability and lies outside `[0, ∞)`. The definition
requires only the positive-probability outcome `4` to lie in the domain, so the inequality still
applies. -/
theorem zero_prob_outside_domain :
    (FinDist.pure (0 : Fin 2)).expect (Real.sqrt ∘ ![4, -5]) ≤
      Real.sqrt ((FinDist.pure (0 : Fin 2)).expect ![4, -5]) := by
  refine lotteryRiskAverse_sqrt (Fin 2) (FinDist.pure 0) ![4, -5] ?_
  intro a ha
  fin_cases a
  · norm_num
  · simp at ha

/-- Counterexample: the convex utility `x ↦ x²` is not risk averse on `ℝ`. For the fair coin on
`-1` and `1`, `E[X²] = 1 > 0 = (E[X])²`. -/
theorem not_lotteryRiskAverse_sq : ¬ LotteryRiskAverse (fun x : ℝ ↦ x ^ 2) Set.univ := by
  intro h
  have h' := h (Fin 2) (FinDist.uniform : FinDist (Fin 2)) ![-1, 1] (fun _ _ ↦ Set.mem_univ _)
  norm_num [FinDist.expect_eq_sum, Fin.sum_univ_two] at h'

/-- Regression: the mean of a fair coin on `1` and `4` stays in the convex domain `[1, 4]`
containing both outcomes. -/
theorem coin_mean_mem_Icc :
    (FinDist.uniform : FinDist (Fin 2)).expect (![1, 4] : Fin 2 → ℝ) ∈ Set.Icc (1 : ℝ) 4 :=
  FinDist.expect_mem_of_convex (convex_Icc 1 4) _ fun a _ ↦ by fin_cases a <;> norm_num

/-- Regression: the mean stays in the domain when only the positive-probability outcomes do. The
outcome `-5` has zero probability and lies outside `[0, ∞)`. -/
theorem zero_prob_mean_mem_Ici :
    (FinDist.pure (0 : Fin 2)).expect (![4, -5] : Fin 2 → ℝ) ∈ Set.Ici (0 : ℝ) := by
  refine FinDist.expect_mem_of_convex (convex_Ici 0) _ fun a ha ↦ ?_
  fin_cases a
  · norm_num
  · simp at ha

/-- Regression: a constant utility is risk averse on `{0, 1}` but not concave there, because
`{0, 1}` is not convex. The converse `concaveOn_of_lotteryRiskAverse` therefore needs its convexity
hypothesis. -/
theorem constant_pair_riskAverse_not_concaveOn :
    LotteryRiskAverse (fun _ : ℝ ↦ (0 : ℝ)) {0, 1} ∧
      ¬ ConcaveOn ℝ ({0, 1} : Set ℝ) (fun _ : ℝ ↦ (0 : ℝ)) := by
  refine ⟨fun _ _ d _ _ ↦ ?_, fun h ↦ ?_⟩
  · exact (d.expect_const (0 : ℝ)).le
  · have hmid := h.1 (show (0 : ℝ) ∈ ({0, 1} : Set ℝ) by simp)
      (show (1 : ℝ) ∈ ({0, 1} : Set ℝ) by simp)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
    norm_num at hmid

end MathEconLib.Decision.RiskAversionExamples
