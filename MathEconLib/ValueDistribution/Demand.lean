/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.ValueDistribution.Basic
public import Mathlib.Probability.CDF

/-!
# Demand from a Real-Valued Distribution

A buyer facing price `price` purchases when `price ≤ value`. Demand is
therefore the probability of the closed upper tail `[price, ∞)`, not the
probability of the open upper tail `(price, ∞)`.

The distinction matters at atoms. If the distribution places positive mass
at the price, then demand includes that mass. The exact identity is

`Pr[value ≥ price] = 1 - F(price) + Pr[value = price]`.

The familiar formula `1 - F(price)` follows when the singleton `{price}` has
probability zero.
-/

namespace MathEconLib

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace ValueDistribution

/-- Demand at `price`: the probability that value is at least the price.

The result is real-valued so that it can be multiplied directly by prices and
used in expected-profit formulas. -/
def probAtLeast (D : ValueDistribution) (price : ℝ) : ℝ :=
  D (Ici price)

/-- Demand is nonnegative. -/
theorem probAtLeast_nonneg (D : ValueDistribution) (price : ℝ) :
    0 ≤ D.probAtLeast price := by
  exact (D (Ici price)).property

/-- Demand is at most one. -/
theorem probAtLeast_le_one (D : ValueDistribution) (price : ℝ) :
    D.probAtLeast price ≤ 1 := by
  exact_mod_cast D.apply_le_one (Ici price)

/-- Raising the price weakly lowers the probability of purchase. -/
theorem antitone_probAtLeast (D : ValueDistribution) :
    Antitone D.probAtLeast := by
  intro lowerPrice higherPrice hle
  unfold probAtLeast
  exact_mod_cast D.apply_mono (Ici_subset_Ici.mpr hle)

/-- Demand is one minus the probability that value is strictly below the
price. This identity is valid even when the distribution has an atom at the
price. -/
theorem probAtLeast_eq_one_sub_measure_Iio
    (D : ValueDistribution) (price : ℝ) :
    D.probAtLeast price = 1 - (D : Measure ℝ).real (Iio price) := by
  rw [probAtLeast, ← D.measureReal_eq_coe_coeFn]
  rw [← compl_Iio, measureReal_compl measurableSet_Iio]
  simp

/-- Demand equals one minus the CDF plus the probability mass at the price.

This is the atom-sensitive form of the posted-price demand identity. It makes
the tie-breaking convention explicit: a buyer whose value exactly equals the
price purchases. -/
theorem probAtLeast_eq_one_sub_cdf_add_mass
    (D : ValueDistribution) (price : ℝ) :
    D.probAtLeast price =
      1 - cdf (D : Measure ℝ) price + D {price} := by
  rw [probAtLeast, ← D.measureReal_eq_coe_coeFn]
  rw [← D.measureReal_eq_coe_coeFn]
  rw [cdf_eq_real]
  rw [← compl_Iio, measureReal_compl measurableSet_Iio]
  simp only [probReal_univ]
  have hsplit :
      (D : Measure ℝ).real (Iic price) =
        (D : Measure ℝ).real (Iio price) +
          (D : Measure ℝ).real {price} := by
    rw [← Iio_union_right]
    exact measureReal_union (μ := (D : Measure ℝ))
      (s₁ := Iio price) (s₂ := {price}) (by simp)
      (measurableSet_singleton price)
  rw [hsplit]
  ring

/-- When there is no probability mass exactly at the price, demand is the
usual survival probability `1 - F(price)`. -/
theorem probAtLeast_eq_one_sub_cdf_of_singleton_eq_zero
    (D : ValueDistribution) (price : ℝ)
    (hprice : D {price} = 0) :
    D.probAtLeast price = 1 - cdf (D : Measure ℝ) price := by
  rw [D.probAtLeast_eq_one_sub_cdf_add_mass price, hprice]
  simp

/-- For an atomless distribution, demand is one minus the CDF. -/
theorem probAtLeast_eq_one_sub_cdf
    (D : ValueDistribution) [NullSingletonClass (D : Measure ℝ)] (price : ℝ) :
    D.probAtLeast price = 1 - cdf (D : Measure ℝ) price := by
  apply D.probAtLeast_eq_one_sub_cdf_of_singleton_eq_zero price
  simp [ProbabilityMeasure.coeFn_def]

end ValueDistribution

end

end MathEconLib
