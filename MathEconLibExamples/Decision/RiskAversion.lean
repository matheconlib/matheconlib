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
* the convex utility `x ↦ x²`, which fails the definition on the whole real line.
-/

@[expose] public section

open MathEconLib.Probability MathEconLib.Decision

namespace MathEconLib.Decision.RiskAversionExamples

/-- The square root is concave on `[0, ∞)`. -/
theorem concaveOn_sqrt : ConcaveOn ℝ (Set.Ici 0) Real.sqrt :=
  Real.strictConcaveOn_sqrt.concaveOn

/-- The square root is risk averse against finite lotteries on `[0, ∞)`. -/
theorem lotteryRiskAverse_sqrt : LotteryRiskAverse Real.sqrt (Set.Ici 0) :=
  lotteryRiskAverse_of_concaveOn concaveOn_sqrt

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

end MathEconLib.Decision.RiskAversionExamples
