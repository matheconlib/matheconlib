/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.ValueDistribution.Demand
public import MathEconLib.ValueDistribution.Density
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Probability.Distributions.Uniform

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Uniform Value Distributions on Real Intervals

The uniform law on a nondegenerate interval is Mathlib's Lebesgue measure
conditioned on that interval, viewed as a `ValueDistribution`. The construction
adds no new measure representation. Its support, atomlessness, density, CDF,
and demand facts can be used independently of posted pricing.
-/

namespace MathEconLib

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace ValueDistribution

/-- The uniform probability distribution on `[a, b]`, for `a < b`.

This is Lebesgue measure conditioned on the interval. The strict inequality
ensures that the interval has positive measure, so conditioning produces a
probability measure. -/
def uniformInterval (a b : ℝ) (hab : a < b) : ValueDistribution :=
  ⟨ProbabilityTheory.cond volume (Icc a b), by
    apply ProbabilityTheory.cond_isProbabilityMeasure_of_finite
    · rw [Real.volume_Icc]
      exact ENNReal.ofReal_ne_zero_iff.mpr (sub_pos.mpr hab)
    · rw [Real.volume_Icc]
      exact ENNReal.ofReal_ne_top⟩

/-- The underlying measure is Mathlib's conditioned Lebesgue measure. -/
theorem toMeasure_uniformInterval (a b : ℝ) (hab : a < b) :
    ((uniformInterval a b hab : ValueDistribution) : Measure ℝ) =
      ProbabilityTheory.cond volume (Icc a b) :=
  rfl

/-- The interval-uniform law satisfies Mathlib's uniform-distribution predicate. -/
theorem isUniform_uniformInterval (a b : ℝ) (hab : a < b) :
    MeasureTheory.pdf.IsUniform (id : ℝ → ℝ) (Icc a b)
      ((uniformInterval a b hab : ValueDistribution) : Measure ℝ) volume := by
  rw [toMeasure_uniformInterval]
  exact MeasureTheory.pdf.IsUniform.cond

/-- An interval-uniform value lies in its defining interval almost surely. -/
theorem uniformInterval_supported (a b : ℝ) (hab : a < b) :
    (uniformInterval a b hab).IsSupportedOnInterval a b := by
  simpa only [IsSupportedOnInterval, toMeasure_uniformInterval] using
    (ProbabilityTheory.ae_cond_mem (μ := volume) measurableSet_Icc)

/-- The interval-uniform distribution is absolutely continuous with respect
to Lebesgue measure. -/
theorem uniformInterval_absolutelyContinuous (a b : ℝ) (hab : a < b) :
    ((uniformInterval a b hab : ValueDistribution) : Measure ℝ) ≪ volume := by
  rw [toMeasure_uniformInterval]
  exact ProbabilityTheory.cond_absolutelyContinuous

/-- A uniform distribution on a real interval has no point masses. -/
instance uniformInterval_noAtoms (a b : ℝ) (hab : a < b) :
    NullSingletonClass ((uniformInterval a b hab : ValueDistribution) : Measure ℝ) where
  measure_singleton point :=
    (uniformInterval_absolutelyContinuous a b hab) (measure_singleton point)

/-- On its support, the constant `1 / (b - a)` is a real-valued density
representative of the interval-uniform distribution.

The equality is almost everywhere because the Radon--Nikodym derivative is
not canonically determined at individual points. -/
theorem uniformInterval_density (a b : ℝ) (hab : a < b) :
    (fun _ : ℝ ↦ 1 / (b - a)) =ᵐ[volume.restrict (Icc a b)]
      (uniformInterval a b hab).realDensity := by
  have hpdf :=
    (isUniform_uniformInterval a b hab).pdf_toReal_ae_eq measurableSet_Icc
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    ae_restrict_of_ae hpdf] with value hvalue hpdfValue
  have hreal :
      (uniformInterval a b hab).realDensity value =
        ((Icc a b).indicator
          ((volume (Icc a b))⁻¹ • (1 : ℝ → ENNReal)) value).toReal := by
    simpa [MeasureTheory.pdf, Measure.map_id, realDensity] using hpdfValue
  rw [hreal, Set.indicator_of_mem hvalue]
  simp [Real.volume_Icc, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le), one_div]

/-- For a price in `[a, b]`, uniform demand is the fraction of the interval
lying at or above that price. -/
theorem uniformInterval_probAtLeast (a b : ℝ) (hab : a < b)
    (price : ℝ) (hprice : price ∈ Icc a b) :
    (uniformInterval a b hab).probAtLeast price = (b - price) / (b - a) := by
  rw [ValueDistribution.probAtLeast,
    ← (uniformInterval a b hab).measureReal_eq_coe_coeFn,
    toMeasure_uniformInterval, Measure.real,
    ProbabilityTheory.cond_apply' measurableSet_Ici volume]
  have hset : Icc a b ∩ Ici price = Icc price b := by
    ext value
    simp only [mem_inter_iff, mem_Ici, mem_Icc]
    constructor
    · rintro ⟨⟨_, hb⟩, hp⟩
      exact ⟨hp, hb⟩
    · rintro ⟨hp, hb⟩
      exact ⟨⟨hprice.1.trans hp, hb⟩, hp⟩
  rw [hset, Real.volume_Icc, Real.volume_Icc]
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv]
  rw [ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le),
    ENNReal.toReal_ofReal (sub_nonneg.mpr hprice.2)]
  ring

/-- On its support, the CDF of the interval-uniform law is affine. -/
theorem uniformInterval_cdf (a b : ℝ) (hab : a < b)
    (price : ℝ) (hprice : price ∈ Icc a b) :
    cdf ((uniformInterval a b hab : ValueDistribution) : Measure ℝ) price =
      (price - a) / (b - a) := by
  have hdemand := uniformInterval_probAtLeast a b hab price hprice
  rw [(uniformInterval a b hab).probAtLeast_eq_one_sub_cdf] at hdemand
  have hden : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  field_simp at hdemand ⊢
  linarith

/-- At an interior value, the CDF has derivative `1 / (b - a)`.

The statement is pointwise: the CDF need not have this derivative at the
endpoints, where its affine formula meets the constant outer pieces. -/
theorem uniformInterval_hasDerivAt_cdf (a b : ℝ) (hab : a < b)
    (price : ℝ) (hprice : price ∈ Ioo a b) :
    HasDerivAt
      (cdf ((uniformInterval a b hab : ValueDistribution) : Measure ℝ))
      (1 / (b - a)) price := by
  apply (((hasDerivAt_id price).sub_const a).div_const (b - a)).congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds hprice.1 hprice.2] with value hvalue
  exact uniformInterval_cdf a b hab value hvalue

end ValueDistribution

end

end

end MathEconLib
