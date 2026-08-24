/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Auctionlib.ForMathlib.Quantile
public import Auctionlib.ValueDistribution.Basic

/-!
# Quantiles of value distributions

Thin `ValueDistribution`-level restatements of the measure-theoretic CDF and quantile API.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

noncomputable section

namespace ValueDistribution

variable (D : ValueDistribution) {lower upper : ℝ}

/-- The CDF vanishes strictly below a support interval. -/
lemma cdf_eq_zero_of_lt (hsupport : D.IsSupportedOnInterval lower upper) {x : ℝ}
    (hx : x < lower) : cdf (D : Measure ℝ) x = 0 :=
  ProbabilityTheory.cdf_eq_zero_of_lt hsupport hx

/-- The CDF equals one at and above the upper endpoint of a support interval. -/
lemma cdf_eq_one_of_le (hsupport : D.IsSupportedOnInterval lower upper) {x : ℝ}
    (hx : upper ≤ x) : cdf (D : Measure ℝ) x = 1 :=
  ProbabilityTheory.cdf_eq_one_of_le hsupport hx

/-- An atomless distribution's CDF vanishes at the lower endpoint of its support interval. -/
lemma cdf_lower_eq_zero [NoAtoms (D : Measure ℝ)]
    (hsupport : D.IsSupportedOnInterval lower upper) : cdf (D : Measure ℝ) lower = 0 :=
  ProbabilityTheory.cdf_left_eq_zero hsupport

/-- Interior quantiles belong to every closed support interval. -/
lemma quantile_mem_Icc (hsupport : D.IsSupportedOnInterval lower upper) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) : Measure.quantile (D : Measure ℝ) t ∈ Icc lower upper :=
  Measure.quantile_mem_Icc hsupport ht

/-- An atomless distribution's CDF takes an interior level at the corresponding quantile. -/
lemma cdf_quantile [NoAtoms (D : Measure ℝ)] {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    cdf (D : Measure ℝ) (Measure.quantile (D : Measure ℝ) t) = t :=
  Measure.cdf_quantile ht

/-- Reverse absolute continuity makes the CDF strictly increasing on the support interval. -/
lemma strictMonoOn_cdf (hvol : volume.restrict (Icc lower upper) ≪ (D : Measure ℝ)) :
    StrictMonoOn (cdf (D : Measure ℝ)) (Icc lower upper) :=
  ProbabilityTheory.strictMonoOn_cdf hvol

/-- The CDF of an interior support point lies in `(0, 1)`. -/
lemma cdf_mem_Ioo [NoAtoms (D : Measure ℝ)]
    (hsupport : D.IsSupportedOnInterval lower upper)
    (hvol : volume.restrict (Icc lower upper) ≪ (D : Measure ℝ))
    {x : ℝ} (hx : x ∈ Ioo lower upper) : cdf (D : Measure ℝ) x ∈ Ioo (0 : ℝ) 1 :=
  ProbabilityTheory.cdf_mem_Ioo hsupport hvol hx

/-- Quantile is a left inverse of the CDF on the interior support interval. -/
lemma quantile_cdf [NoAtoms (D : Measure ℝ)]
    (hsupport : D.IsSupportedOnInterval lower upper)
    (hvol : volume.restrict (Icc lower upper) ≪ (D : Measure ℝ))
    {x : ℝ} (hx : x ∈ Ioo lower upper) :
    Measure.quantile (D : Measure ℝ) (cdf (D : Measure ℝ) x) = x :=
  Measure.quantile_cdf hsupport hvol hx

/-- Interior quantiles of an atomless distribution lie in the open support interval. -/
lemma quantile_mem_Ioo [NoAtoms (D : Measure ℝ)]
    (hsupport : D.IsSupportedOnInterval lower upper) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) : Measure.quantile (D : Measure ℝ) t ∈ Ioo lower upper :=
  Measure.quantile_mem_Ioo hsupport ht

/-- Quantile is continuous at every interior probability level under reverse absolute continuity. -/
lemma continuousAt_quantile [NoAtoms (D : Measure ℝ)]
    (hsupport : D.IsSupportedOnInterval lower upper)
    (hvol : volume.restrict (Icc lower upper) ≪ (D : Measure ℝ))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ContinuousAt (Measure.quantile (D : Measure ℝ)) t :=
  Measure.continuousAt_quantile hsupport hvol ht

/-- Composing a support-monotone function with quantile is monotone on `(0, 1)`. -/
lemma monotoneOn_comp_quantile {f : ℝ → ℝ}
    (hsupport : D.IsSupportedOnInterval lower upper)
    (hf : MonotoneOn f (Icc lower upper)) :
    MonotoneOn (f ∘ Measure.quantile (D : Measure ℝ)) (Ioo (0 : ℝ) 1) := by
  intro s hs t ht hst
  exact hf (D.quantile_mem_Icc hsupport hs) (D.quantile_mem_Icc hsupport ht)
    (Measure.monotoneOn_quantile hs ht hst)

/-- Continuity on a support interval gives a.e. strong measurability under the distribution. -/
lemma aestronglyMeasurable_of_continuousOn {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} (hsupport : D.IsSupportedOnInterval lower upper)
    (hf : ContinuousOn f (Icc lower upper)) : AEStronglyMeasurable f (D : Measure ℝ) := by
  have h_meas := hf.aestronglyMeasurable (μ := (D : Measure ℝ)) measurableSet_Icc
  rwa [Measure.restrict_eq_self_of_ae_mem hsupport] at h_meas

/-- Monotonicity on a support interval gives a.e. measurability under the distribution. -/
lemma aemeasurable_of_monotoneOn {f : ℝ → ℝ}
    (hsupport : D.IsSupportedOnInterval lower upper)
    (hf : MonotoneOn f (Icc lower upper)) : AEMeasurable f (D : Measure ℝ) := by
  have h_meas :=
    aemeasurable_restrict_of_monotoneOn (μ := (D : Measure ℝ)) measurableSet_Icc hf
  rwa [Measure.restrict_eq_self_of_ae_mem hsupport] at h_meas

/-- Integrals under a value distribution can be expressed on the quantile domain. -/
theorem integral_eq_integral_comp_quantile {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (hf : AEStronglyMeasurable f (D : Measure ℝ)) :
    (∫ x, f x ∂(D : Measure ℝ)) =
      ∫ t in Ioo (0 : ℝ) 1, f (Measure.quantile (D : Measure ℝ) t) :=
  Measure.integral_eq_integral_quantile f hf

/-- Integrability transfers from a value distribution to its quantile representation. -/
lemma integrableOn_comp_quantile {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} (hf : Integrable f (D : Measure ℝ)) :
    IntegrableOn (f ∘ Measure.quantile (D : Measure ℝ)) (Ioo (0 : ℝ) 1) volume := by
  let μ : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)
  have h_map : Measure.map (Measure.quantile (D : Measure ℝ)) μ = (D : Measure ℝ) :=
    Measure.map_quantile_volume_Ioo
  have hf' : Integrable f (Measure.map (Measure.quantile (D : Measure ℝ)) μ) := by
    rwa [h_map]
  exact (integrable_map_measure hf'.aestronglyMeasurable
    (Measure.aemeasurable_quantile_restrict_Ioo (μ := (D : Measure ℝ)))).mp hf'

end ValueDistribution

end
