/-
Copyright (c) 2026 Siyang Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siyang Liu
-/
module

public import MathEconLib.Probability.FinDist.Expect
public import Mathlib.Analysis.Convex.Jensen

/-!
# Convexity and expectations for finite distributions

The mean of a lottery whose positive-probability outcomes lie in a convex set stays in that set,
and finite Jensen's inequality holds for concave functions on that set. Zero-probability outcomes
are unconstrained.

## Main statements

* `FinDist.expect_mem_of_convex`: The mean stays in a convex set containing the support.
* `FinDist.expect_comp_le_of_concaveOn`: Finite Jensen's inequality for concave functions.

## Tags

probability, finite distributions, expectation, convexity, Jensen
-/

@[expose] public section

namespace MathEconLib.Probability

namespace FinDist

variable {α E β : Type*} [Fintype α] [AddCommGroup E] [Module ℝ E]

/-- If the positive-probability outcomes lie in a convex set, so does the expectation. -/
lemma expect_mem_of_convex {s : Set E} (hs : Convex ℝ s) (d : FinDist α) {x : α → E}
    (hx : ∀ a, 0 < d.pmf a → x a ∈ s) : d.expect x ∈ s := by
  rw [expect_eq_sum_support]
  exact hs.sum_mem (fun a _ ↦ d.nonneg a) d.sum_support_pmf
    fun a ha ↦ hx a (Finset.mem_filter.mp ha).2

/-- **Jensen's inequality** for a concave function and a finite distribution. Only the
positive-probability outcomes need to lie in the domain. -/
lemma expect_comp_le_of_concaveOn [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β]
    [Module ℝ β] [IsStrictOrderedModule ℝ β] {s : Set E} {f : E → β} (hf : ConcaveOn ℝ s f)
    (d : FinDist α) {x : α → E} (hx : ∀ a, 0 < d.pmf a → x a ∈ s) :
    d.expect (f ∘ x) ≤ f (d.expect x) := by
  rw [expect_eq_sum_support, expect_eq_sum_support]
  exact hf.le_map_sum (fun a _ ↦ d.nonneg a) d.sum_support_pmf
    fun a ha ↦ hx a (Finset.mem_filter.mp ha).2

end FinDist

end MathEconLib.Probability
