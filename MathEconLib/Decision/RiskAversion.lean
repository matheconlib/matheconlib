/-
Copyright (c) 2026 Siyang Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siyang Liu
-/
module

public import MathEconLib.Probability.FinDist.Convex

/-!
# Risk aversion over finite lotteries

A real utility `u` is **risk averse against finite lotteries** on a set `I ⊆ ℝ` when, for every
finite distribution `d` and every assignment `x` of outcomes to its atoms, the expected utility of
the lottery does not exceed the utility of its expected outcome: `E[u(x)] ≤ u(E[x])`.

Only outcomes with positive probability must lie in `I`. A zero-probability outcome outside the
domain therefore does not affect the comparison.

The main result says that, on a convex domain, risk aversion is equivalent to concavity. The
concave direction is finite Jensen's inequality for `FinDist`; the converse applies the hypothesis
to two-point lotteries. Both directions use the `FinDist` and `FinDist.expect` interfaces.

The definition evaluates `u` at the mean of the lottery, and on a non-convex `I` that mean can fall
outside `I`. On `{0, 1}`, for example, the fair coin constrains `u (1 / 2)`. A convexity hypothesis
on `I` is therefore needed for the converse: a constant utility is risk averse on `{0, 1}` but not
concave there, because `ConcaveOn` requires a convex domain.

## Main definitions

* `MathEconLib.Decision.LotteryRiskAverse`: risk aversion against finite lotteries on `I`.

## Main statements

* `MathEconLib.Decision.lotteryRiskAverse_of_concaveOn`: concavity implies risk aversion.
* `MathEconLib.Decision.concaveOn_of_lotteryRiskAverse`: risk aversion implies concavity on a
  convex domain.
* `MathEconLib.Decision.lotteryRiskAverse_iff_concaveOn`: the equivalence on a convex domain.
* `MathEconLib.Decision.LotteryRiskAverse.expect_comp_le`: the inequality for lotteries indexed by
  a finite type in any universe.

## Implementation notes

Ported and redesigned from Siyang Liu's `lean_for_finance` library. The worked examples are in
`MathEconLibExamples/Decision/RiskAversion.lean`.

## References

Kerry E. Back (2017), *Asset Pricing and Portfolio Choice Theory*, 2nd ed., Oxford University
Press, §1.1, pp. 4–5.
-/

@[expose] public section

open MathEconLib.Probability

namespace MathEconLib.Decision

/-- A utility `u` is **risk averse against finite lotteries** on `I`: for every finite distribution
`d` on a finite type `α` and every assignment `x : α → ℝ` whose outcomes with positive probability
lie in `I`, the expected utility is at most the utility of the expected outcome,
`E[u(x)] ≤ u(E[x])`.

The outcome type ranges over `Type`, so that the universe need not be inferred at use sites. This
loses no generality: `LotteryRiskAverse.expect_comp_le` applies to finite types in any universe. -/
def LotteryRiskAverse (u : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∀ (α : Type) [Fintype α] (d : FinDist α) (x : α → ℝ),
    (∀ a, 0 < d.pmf a → x a ∈ I) → d.expect (u ∘ x) ≤ u (d.expect x)

/-- A finite lottery in any universe satisfies the risk-aversion inequality, by reindexing it along
`Fintype.equivFin`. -/
theorem LotteryRiskAverse.expect_comp_le {u : ℝ → ℝ} {I : Set ℝ} (hu : LotteryRiskAverse u I)
    {α : Type*} [Fintype α] (d : FinDist α) (x : α → ℝ) (hx : ∀ a, 0 < d.pmf a → x a ∈ I) :
    d.expect (u ∘ x) ≤ u (d.expect x) := by
  let e := Fintype.equivFin α
  let d' : FinDist (Fin (Fintype.card α)) :=
    ⟨d.pmf ∘ e.symm, fun _ ↦ d.nonneg _, (e.symm.sum_comp d.pmf).trans d.sum_one⟩
  have hexpect (f : α → ℝ) : d'.expect (f ∘ e.symm) = d.expect f :=
    e.symm.sum_comp fun a ↦ d.pmf a • f a
  have h := hu _ d' (x ∘ e.symm) fun i hi ↦ hx _ hi
  rwa [← Function.comp_assoc, hexpect, hexpect] at h

/-- Concavity implies risk aversion against finite lotteries: this is finite Jensen's inequality. -/
theorem lotteryRiskAverse_of_concaveOn {u : ℝ → ℝ} {I : Set ℝ} (hu : ConcaveOn ℝ I u) :
    LotteryRiskAverse u I :=
  fun _ _ d _ hx ↦ FinDist.expect_comp_le_of_concaveOn hu d hx

/-- Risk aversion against finite lotteries implies concavity on a convex domain. A two-point
lottery with masses `a` and `1 - a` gives the concavity inequality. -/
theorem concaveOn_of_lotteryRiskAverse {u : ℝ → ℝ} {I : Set ℝ} (hI : Convex ℝ I)
    (hu : LotteryRiskAverse u I) : ConcaveOn ℝ I u := by
  refine ⟨hI, fun x hx y hy a b ha hb hab ↦ ?_⟩
  obtain rfl : b = 1 - a := by linarith
  let weight : unitInterval := ⟨a, ha, by linarith⟩
  have hmem : ∀ i : Fin 2, ![x, y] i ∈ I := by
    intro i
    fin_cases i <;> simp [hx, hy]
  have h := hu (Fin 2) (FinDist.mixture weight (FinDist.pure 0) (FinDist.pure 1)) ![x, y]
    fun i _ ↦ hmem i
  simpa [FinDist.expect_mixture, FinDist.expect_pure, weight] using h

/-- On a convex domain, risk aversion against finite lotteries is equivalent to concavity. -/
theorem lotteryRiskAverse_iff_concaveOn {u : ℝ → ℝ} {I : Set ℝ} (hI : Convex ℝ I) :
    LotteryRiskAverse u I ↔ ConcaveOn ℝ I u :=
  ⟨concaveOn_of_lotteryRiskAverse hI, lotteryRiskAverse_of_concaveOn⟩

end MathEconLib.Decision
