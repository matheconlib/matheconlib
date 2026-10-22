/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Uniform finite expectations

Integrating a real-valued function under the uniform PMF on a nonempty finite discrete space
agrees with Mathlib's finite average. The integrand is arbitrary; applications supply their
own statistic and outcome rule.
-/

@[expose] public section

open scoped BigOperators
open MeasureTheory

namespace PMF

/-- A uniform finite expectation is the ordinary average over the outcome space. -/
theorem integral_uniformOfFintype {α : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (f : α → ℝ) :
    (∫ a, f a ∂(uniformOfFintype α).toMeasure) = 𝔼 a, f a := by
  rw [integral_eq_sum, Fintype.expect_eq_sum_div_card]
  simp only [uniformOfFintype_apply, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, smul_eq_mul, div_eq_inv_mul, Finset.mul_sum]

end PMF
