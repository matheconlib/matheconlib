/-
Copyright (c) 2026 Siyang Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siyang Liu
-/
module

public import MathEconLib.Probability.FinDist.Expect
public import Mathlib.Analysis.Convex.Jensen

/-!
# Risk aversion over finite lotteries

A real utility `u` is **risk averse against finite lotteries** on a set `I ⊆ ℝ` when, for every
finite distribution `d` and every assignment `x` of outcomes to its atoms, the expected utility of
the lottery does not exceed the utility of its expected outcome: `E[u(x)] ≤ u(E[x])`.

Only outcomes with positive probability must lie in `I`. A zero-probability outcome outside the
domain therefore does not affect the comparison.

The main result says that, on a convex domain, risk aversion is equivalent to concavity. The
concave direction is finite Jensen's inequality (Mathlib's `ConcaveOn.le_map_sum`); the converse
applies the hypothesis to two-point lotteries. Both directions use the `FinDist` and
`FinDist.expect` interfaces.

## Main definitions

* `MathEconLib.Decision.LotteryRiskAverse`: risk aversion against finite lotteries on `I`.

## Main statements

* `MathEconLib.Decision.lotteryRiskAverse_of_concaveOn`: concavity implies risk aversion.
* `MathEconLib.Decision.concaveOn_of_lotteryRiskAverse`: risk aversion implies concavity on a
  convex domain.
* `MathEconLib.Decision.lotteryRiskAverse_iff_concaveOn`: the equivalence on a convex domain.

## Port coverage

Source: `AssetPricing/Preferences/{Basic,ExpectedUtility}.lean` and blueprint U1 in Siyang Liu's
private `lean_for_finance` library, at commit `edc24ed`. The code is redesigned for this library's
conventions and is not a copy.

| Source declaration | Status here |
|---|---|
| `riskAverse_iff_concaveOn` (U1) | Finite-lottery analogue; the wealth form waits for F2, F3. |
| `Gamble.eu_le_of_concaveOn`, `Gamble.add_mean_mem` | Subsumed by the Jensen step. |
| `le_of_concaveOn_integral` (U1′, general laws) | Deferred to F5 and F16. |
| `existsUnique_riskPremium`, `riskPremium_nonneg` | Deferred to F2. |
| `Gamble`, `RiskAverse`, `IsCertaintyEquiv`, `IsRiskPremium` | Deferred to F2 and F3. |
| Strict concavity ⇔ strict risk aversion (Back p. 5) | Open obligation. |

The worked examples are in `MathEconLibExamples/Decision/RiskAversion.lean`.

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
`E[u(x)] ≤ u(E[x])`. The outcome type ranges over `Type`. -/
def LotteryRiskAverse (u : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∀ (α : Type) [Fintype α] (d : FinDist α) (x : α → ℝ),
    (∀ a, 0 < d.pmf a → x a ∈ I) → d.expect (u ∘ x) ≤ u (d.expect x)

/-- The support of a distribution carries all of its probability. -/
private lemma sum_support_pmf {α : Type} [Fintype α] (d : FinDist α) :
    ∑ a ∈ d.support, d.pmf a = 1 := by
  rw [← d.sum_one]
  exact Finset.sum_filter_of_ne fun a _ h ↦ lt_of_le_of_ne (d.nonneg a) (Ne.symm h)

/-- Expectation of a real-valued function, summed over the support of the distribution. -/
private lemma expect_eq_sum_support {α : Type} [Fintype α] (d : FinDist α) (f : α → ℝ) :
    d.expect f = ∑ a ∈ d.support, d.pmf a • f a := by
  rw [FinDist.expect_eq_sum]
  refine (Finset.sum_filter_of_ne fun a _ h ↦ ?_).symm
  exact lt_of_le_of_ne (d.nonneg a) fun hz ↦ h (by rw [← hz, zero_smul])

/-- Concavity implies risk aversion against finite lotteries: this is finite Jensen's inequality
applied to the lottery's outcomes and probabilities. -/
theorem lotteryRiskAverse_of_concaveOn {u : ℝ → ℝ} {I : Set ℝ} (hu : ConcaveOn ℝ I u) :
    LotteryRiskAverse u I := by
  intro α _ d x hx
  have h := hu.le_map_sum (t := d.support) (w := d.pmf) (p := x)
    (fun a _ ↦ d.nonneg a) (sum_support_pmf d) fun a ha ↦ hx a (Finset.mem_filter.mp ha).2
  rw [expect_eq_sum_support, expect_eq_sum_support]
  exact h

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
