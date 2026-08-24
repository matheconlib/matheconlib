/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Auctionlib.ForMathlib.ConvexEnvelope
public import Auctionlib.ForMathlib.StieltjesRegularization
public import Auctionlib.ForMathlib.TriangleFubini
public import Auctionlib.ValueDistribution.Quantile
public import Auctionlib.ValueDistribution.Regular

/-!
# Myerson ironing

For a score `ψ`, ironing takes the convex envelope of the primitive of `ψ ∘ F⁻¹` in quantile space
and returns its monotone right derivative to value space through the CDF.
-/

@[expose] public section

open Filter Function MeasureTheory ProbabilityTheory Set SingleParameterProblem
open scoped Topology

noncomputable section

namespace ValueDistribution

variable (D : ValueDistribution) (ψ : ℝ → ℝ) {lower upper : ℝ}

/-! ### Definitions -/

/-- The score pulled back to quantile space. -/
noncomputable def quantileScore (t : ℝ) : ℝ :=
  ψ (Measure.quantile (D : Measure ℝ) t)

/-- The primitive of the quantile score. -/
noncomputable def scorePrimitive (t : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..t, D.quantileScore ψ u

/-- The convex envelope of the score primitive on `[0, 1]`. -/
noncomputable def ironedPrimitive : ℝ → ℝ :=
  convexEnvelope 0 1 (D.scorePrimitive ψ)

/-- The globally monotone extension of the right derivative of the ironed primitive. -/
noncomputable def ironedQuantileScore : ℝ → ℝ :=
  rightDerivExtend (D.ironedPrimitive ψ) 0 1

/-- The ironed score in value space. -/
noncomputable def ironed (v : ℝ) : ℝ :=
  D.ironedQuantileScore ψ (cdf (D : Measure ℝ) v)

/-! ### Analytic properties -/

/-- The quantile score is bounded in absolute value on `(0, 1)`. -/
lemma exists_abs_quantileScore_le (hsupport : D.IsSupportedOnInterval lower upper)
    (hψ : ContinuousOn ψ (Icc lower upper)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioo (0 : ℝ) 1, |D.quantileScore ψ t| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hψ
  refine ⟨max C 0, le_max_right _ _, fun t ht => ?_⟩
  exact (hC _ (D.quantile_mem_Icc hsupport ht)).trans (le_max_left _ _)

/-- The quantile score is interval-integrable on `[0, 1]`. -/
lemma intervalIntegrable_quantileScore (hsupport : D.IsSupportedOnInterval lower upper)
    (hψ : ContinuousOn ψ (Icc lower upper)) :
    IntervalIntegrable (D.quantileScore ψ) volume 0 1 := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hψ
  let C := max B 0
  have hψmeas : AEStronglyMeasurable ψ (D : Measure ℝ) :=
    D.aestronglyMeasurable_of_continuousOn hsupport hψ
  have hψbound : ∀ᵐ v ∂(D : Measure ℝ), ‖ψ v‖ ≤ C := by
    filter_upwards [hsupport] with v hv
    exact (hB v hv).trans (le_max_left _ _)
  have hψint : Integrable ψ (D : Measure ℝ) :=
    Integrable.mono' (integrable_const C) hψmeas hψbound
  have hqint := D.integrableOn_comp_quantile hψint
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
  rw [IntegrableOn, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  exact hqint

/-- The score primitive is continuous on `[0, 1]`. -/
lemma continuousOn_scorePrimitive (hsupport : D.IsSupportedOnInterval lower upper)
    (hψ : ContinuousOn ψ (Icc lower upper)) :
    ContinuousOn (D.scorePrimitive ψ) (Icc (0 : ℝ) 1) := by
  have h := intervalIntegral.continuousOn_primitive_interval'
    (D.intervalIntegrable_quantileScore ψ hsupport hψ) (a := 0)
    (by rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]; simp)
  rwa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at h

/-- A bound on the quantile score gives a Lipschitz bound for its primitive. -/
lemma abs_scorePrimitive_sub_le (hsupport : D.IsSupportedOnInterval lower upper)
    (hψ : ContinuousOn ψ (Icc lower upper)) {C : ℝ}
    (hC : ∀ t ∈ Ioo (0 : ℝ) 1, |D.quantileScore ψ t| ≤ C)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    |D.scorePrimitive ψ s - D.scorePrimitive ψ t| ≤ C * |s - t| := by
  have hsub : ∀ r ∈ Icc (0 : ℝ) 1,
      IntervalIntegrable (D.quantileScore ψ) volume 0 r := fun r hr =>
    (D.intervalIntegrable_quantileScore ψ hsupport hψ).mono_set (by
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), uIcc_of_le hr.1]
      exact Icc_subset_Icc_right hr.2)
  have hdiff : D.scorePrimitive ψ s - D.scorePrimitive ψ t =
      ∫ u in t..s, D.quantileScore ψ u :=
    intervalIntegral.integral_interval_sub_left (hsub s hs) (hsub t ht)
  rw [hdiff, ← Real.norm_eq_abs]
  refine intervalIntegral.norm_integral_le_of_norm_le_const_ae ?_
  have hnull : ∀ᵐ u ∂volume, u ∉ ({(0 : ℝ), 1} : Set ℝ) := by
    rw [ae_iff]
    simp only [not_not]
    exact measure_union_null (measure_singleton 0) (measure_singleton 1)
  filter_upwards [hnull] with u hu huIoc
  rw [Real.norm_eq_abs]
  have hu_mem : u ∈ Icc (0 : ℝ) 1 := by
    rw [uIoc_eq_union] at huIoc
    rcases huIoc with h | h
    · exact ⟨le_trans ht.1 h.1.le, le_trans h.2 hs.2⟩
    · exact ⟨le_trans hs.1 h.1.le, le_trans h.2 ht.2⟩
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hu
  exact hC u ⟨lt_of_le_of_ne hu_mem.1 (Ne.symm hu.1), lt_of_le_of_ne hu_mem.2 hu.2⟩

/-- The ironed primitive is convex on `[0, 1]`. -/
lemma convexOn_ironedPrimitive (hsupport : D.IsSupportedOnInterval lower upper)
    (hψ : ContinuousOn ψ (Icc lower upper)) :
    ConvexOn ℝ (Icc (0 : ℝ) 1) (D.ironedPrimitive ψ) :=
  convexOn_convexEnvelope (by norm_num) (D.continuousOn_scorePrimitive ψ hsupport hψ)

/-- The ironed primitive is continuous on `[0, 1]`. -/
lemma continuousOn_ironedPrimitive (hsupport : D.IsSupportedOnInterval lower upper)
    (hψ : ContinuousOn ψ (Icc lower upper)) :
    ContinuousOn (D.ironedPrimitive ψ) (Icc (0 : ℝ) 1) := by
  obtain ⟨C, _, hC⟩ := D.exists_abs_quantileScore_le ψ hsupport hψ
  exact continuousOn_convexEnvelope (by norm_num)
    (D.continuousOn_scorePrimitive ψ hsupport hψ)
    (fun _ hs _ ht => D.abs_scorePrimitive_sub_le ψ hsupport hψ hC hs ht)

/-- The ironed primitive lies below the score primitive on `[0, 1]`. -/
lemma ironedPrimitive_le_scorePrimitive (hsupport : D.IsSupportedOnInterval lower upper)
    (hψ : ContinuousOn ψ (Icc lower upper)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    D.ironedPrimitive ψ t ≤ D.scorePrimitive ψ t :=
  convexEnvelope_le_self (by norm_num) (D.continuousOn_scorePrimitive ψ hsupport hψ) ht

/-- The ironed and raw primitives agree at zero. -/
lemma ironedPrimitive_zero (hsupport : D.IsSupportedOnInterval lower upper)
    (hψ : ContinuousOn ψ (Icc lower upper)) :
    D.ironedPrimitive ψ 0 = D.scorePrimitive ψ 0 := by
  obtain ⟨C, _, hC⟩ := D.exists_abs_quantileScore_le ψ hsupport hψ
  exact convexEnvelope_left (by norm_num) (D.continuousOn_scorePrimitive ψ hsupport hψ)
    (fun _ hs _ ht => D.abs_scorePrimitive_sub_le ψ hsupport hψ hC hs ht)

/-- The ironed and raw primitives agree at one. -/
lemma ironedPrimitive_one (hsupport : D.IsSupportedOnInterval lower upper)
    (hψ : ContinuousOn ψ (Icc lower upper)) :
    D.ironedPrimitive ψ 1 = D.scorePrimitive ψ 1 := by
  obtain ⟨C, _, hC⟩ := D.exists_abs_quantileScore_le ψ hsupport hψ
  exact convexEnvelope_right (by norm_num) (D.continuousOn_scorePrimitive ψ hsupport hψ)
    (fun _ hs _ ht => D.abs_scorePrimitive_sub_le ψ hsupport hψ hC hs ht)

/-- The right derivative of the ironed primitive is bounded below on `(0, 1)`. -/
lemma bddBelow_rightDeriv_ironedPrimitive (hsupport : D.IsSupportedOnInterval lower upper)
    (hψ : ContinuousOn ψ (Icc lower upper)) :
    BddBelow ((fun t => derivWithin (D.ironedPrimitive ψ) (Ioi t) t) '' Ioo (0 : ℝ) 1) := by
  obtain ⟨C, _, hC⟩ := D.exists_abs_quantileScore_le ψ hsupport hψ
  refine ⟨-C, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  exact (abs_le.mp (abs_rightDeriv_convexEnvelope_le (by norm_num)
    (D.continuousOn_scorePrimitive ψ hsupport hψ)
    (fun _ hs _ hu => D.abs_scorePrimitive_sub_le ψ hsupport hψ hC hs hu) ht)).1

/-- The right derivative of the ironed primitive is bounded above on `(0, 1)`. -/
lemma bddAbove_rightDeriv_ironedPrimitive (hsupport : D.IsSupportedOnInterval lower upper)
    (hψ : ContinuousOn ψ (Icc lower upper)) :
    BddAbove ((fun t => derivWithin (D.ironedPrimitive ψ) (Ioi t) t) '' Ioo (0 : ℝ) 1) := by
  obtain ⟨C, _, hC⟩ := D.exists_abs_quantileScore_le ψ hsupport hψ
  refine ⟨C, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  exact (abs_le.mp (abs_rightDeriv_convexEnvelope_le (by norm_num)
    (D.continuousOn_scorePrimitive ψ hsupport hψ)
    (fun _ hs _ hu => D.abs_scorePrimitive_sub_le ψ hsupport hψ hC hs hu) ht)).2

/-- The ironed quantile score is globally monotone. -/
lemma monotone_ironedQuantileScore (hsupport : D.IsSupportedOnInterval lower upper)
    (hψ : ContinuousOn ψ (Icc lower upper)) : Monotone (D.ironedQuantileScore ψ) :=
  (D.convexOn_ironedPrimitive ψ hsupport hψ).monotone_rightDerivExtend (by norm_num)
    (D.bddBelow_rightDeriv_ironedPrimitive ψ hsupport hψ)
    (D.bddAbove_rightDeriv_ironedPrimitive ψ hsupport hψ)

/-- The ironed score is globally monotone in value space. -/
theorem monotone_ironed (hsupport : D.IsSupportedOnInterval lower upper)
    (hψ : ContinuousOn ψ (Icc lower upper)) : Monotone (D.ironed ψ) :=
  (D.monotone_ironedQuantileScore ψ hsupport hψ).comp (monotone_cdf (D : Measure ℝ))

/-- The ironed score is measurable. -/
lemma measurable_ironed (hsupport : D.IsSupportedOnInterval lower upper)
    (hψ : ContinuousOn ψ (Icc lower upper)) : Measurable (D.ironed ψ) :=
  (D.monotone_ironed ψ hsupport hψ).measurable

/-- Every ironed score is bounded by its endpoint quantile scores. -/
lemma ironed_mem_Icc (hsupport : D.IsSupportedOnInterval lower upper)
    (hψ : ContinuousOn ψ (Icc lower upper)) (v : ℝ) :
    D.ironed ψ v ∈ Icc (D.ironedQuantileScore ψ 0) (D.ironedQuantileScore ψ 1) := by
  exact ⟨D.monotone_ironedQuantileScore ψ hsupport hψ (cdf_nonneg (D : Measure ℝ) v),
    D.monotone_ironedQuantileScore ψ hsupport hψ (cdf_le_one (D : Measure ℝ) v)⟩

/-- The cumulative quantile-score gap equals the primitive gap. -/
lemma integral_ironedQuantileScore_sub_quantileScore
    (hsupport : D.IsSupportedOnInterval lower upper)
    (hψ : ContinuousOn ψ (Icc lower upper)) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ∫ t in (0 : ℝ)..s, (D.ironedQuantileScore ψ t - D.quantileScore ψ t) =
      D.ironedPrimitive ψ s - D.scorePrimitive ψ s := by
  have hconv := D.convexOn_ironedPrimitive ψ hsupport hψ
  have hderiv : ∫ t in (0 : ℝ)..s, D.ironedQuantileScore ψ t =
      D.ironedPrimitive ψ s - D.ironedPrimitive ψ 0 := by
    rw [← hconv.integral_rightDeriv_eq_sub (by norm_num)
      (D.continuousOn_ironedPrimitive ψ hsupport hψ)
      (D.bddBelow_rightDeriv_ironedPrimitive ψ hsupport hψ)
      (D.bddAbove_rightDeriv_ironedPrimitive ψ hsupport hψ) hs.1 hs.2]
    refine intervalIntegral.integral_congr_ae ?_
    have hone : ∀ᵐ t ∂volume, t ≠ (1 : ℝ) := by
      rw [ae_iff]
      simp only [not_not]
      exact measure_singleton 1
    filter_upwards [hone] with t ht1 ht
    rw [uIoc_of_le hs.1] at ht
    exact rightDerivExtend_of_mem_Ioo (D.ironedPrimitive ψ)
      ⟨ht.1, lt_of_le_of_ne (le_trans ht.2 hs.2) ht1⟩
  have hscore : ∫ t in (0 : ℝ)..s, D.quantileScore ψ t = D.scorePrimitive ψ s := rfl
  have hsub : ∫ t in (0 : ℝ)..s,
      (D.ironedQuantileScore ψ t - D.quantileScore ψ t) =
      (∫ t in (0 : ℝ)..s, D.ironedQuantileScore ψ t) -
        ∫ t in (0 : ℝ)..s, D.quantileScore ψ t := by
    refine intervalIntegral.integral_sub
      (D.monotone_ironedQuantileScore ψ hsupport hψ).intervalIntegrable ?_
    exact (D.intervalIntegrable_quantileScore ψ hsupport hψ).mono_set (by
      rw [uIcc_of_le hs.1, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact Icc_subset_Icc_right hs.2)
  have hzero : D.scorePrimitive ψ 0 = 0 := by
    simp [scorePrimitive]
  rw [hsub, hderiv, hscore, D.ironedPrimitive_zero ψ hsupport hψ, hzero]
  ring

/-! ### Integrability -/

/-- A bounded monotone allocation times the score is integrable. -/
lemma integrable_mul (hsupport : D.IsSupportedOnInterval lower upper)
    (hψ : ContinuousOn ψ (Icc lower upper)) {x : ℝ → ℝ}
    (hx : ∀ v ∈ Icc lower upper, x v ∈ Icc (0 : ℝ) 1)
    (hmono : MonotoneOn x (Icc lower upper)) :
    Integrable (fun v => x v * ψ v) (D : Measure ℝ) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hψ
  have hC_nonneg : 0 ≤ max C 0 := le_max_right _ _
  have hxmeas : AEStronglyMeasurable x (D : Measure ℝ) :=
    (D.aemeasurable_of_monotoneOn hsupport hmono).aestronglyMeasurable
  have hψmeas : AEStronglyMeasurable ψ (D : Measure ℝ) :=
    D.aestronglyMeasurable_of_continuousOn hsupport hψ
  have hbound : ∀ᵐ v ∂(D : Measure ℝ), ‖x v * ψ v‖ ≤ max C 0 := by
    filter_upwards [hsupport] with v hv
    rw [Real.norm_eq_abs, abs_mul]
    have hxabs : |x v| ≤ 1 := abs_le.mpr ⟨by linarith [(hx v hv).1], (hx v hv).2⟩
    have hψabs : |ψ v| ≤ max C 0 := (hC v hv).trans (le_max_left _ _)
    calc
      |x v| * |ψ v| ≤ 1 * max C 0 :=
        mul_le_mul hxabs hψabs (abs_nonneg _) (by norm_num)
      _ = max C 0 := one_mul _
  exact Integrable.mono' (integrable_const (max C 0)) (hxmeas.mul hψmeas) hbound

/-- A bounded monotone allocation times the ironed score is integrable. -/
lemma integrable_mul_ironed (hsupport : D.IsSupportedOnInterval lower upper)
    (hψ : ContinuousOn ψ (Icc lower upper)) {x : ℝ → ℝ}
    (hx : ∀ v ∈ Icc lower upper, x v ∈ Icc (0 : ℝ) 1)
    (hmono : MonotoneOn x (Icc lower upper)) :
    Integrable (fun v => x v * D.ironed ψ v) (D : Measure ℝ) := by
  let C := max |D.ironedQuantileScore ψ 0| |D.ironedQuantileScore ψ 1|
  have hxmeas : AEStronglyMeasurable x (D : Measure ℝ) :=
    (D.aemeasurable_of_monotoneOn hsupport hmono).aestronglyMeasurable
  have himeas : AEStronglyMeasurable (D.ironed ψ) (D : Measure ℝ) :=
    (D.measurable_ironed ψ hsupport hψ).aestronglyMeasurable
  have hbound : ∀ᵐ v ∂(D : Measure ℝ), ‖x v * D.ironed ψ v‖ ≤ C := by
    filter_upwards [hsupport] with v hv
    rw [Real.norm_eq_abs, abs_mul]
    have hxabs : |x v| ≤ 1 := abs_le.mpr ⟨by linarith [(hx v hv).1], (hx v hv).2⟩
    have hiabs : |D.ironed ψ v| ≤ C := by
      obtain ⟨hlo, hhi⟩ := D.ironed_mem_Icc ψ hsupport hψ v
      rw [abs_le]
      exact ⟨(neg_le_neg (le_max_left _ _)).trans ((neg_abs_le _).trans hlo),
        hhi.trans ((le_abs_self _).trans (le_max_right _ _))⟩
    calc
      |x v| * |D.ironed ψ v| ≤ 1 * C :=
        mul_le_mul hxabs hiabs (abs_nonneg _) (by norm_num)
      _ = C := one_mul _
  exact Integrable.mono' (integrable_const C) (hxmeas.mul himeas) hbound

/-! ### Stieltjes representation of the ironing gap -/

/-- On an affine interval of the ironed primitive, the ironed quantile score is its slope. -/
private lemma ironedQuantileScore_eq_of_affineOn {p r m c : ℝ} (hpr : 0 ≤ p)
    (hr1 : r ≤ 1) (haffine : ∀ x ∈ Ioo p r, D.ironedPrimitive ψ x = m * x + c)
    {t : ℝ} (ht : t ∈ Ioo p r) : D.ironedQuantileScore ψ t = m := by
  have htoo : t ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_lt hpr ht.1, lt_of_lt_of_le ht.2 hr1⟩
  rw [ironedQuantileScore, rightDerivExtend_of_mem_Ioo _ htoo]
  have haff : HasDerivWithinAt (fun x => m * x + c) m (Ioi t) t := by
    simpa using ((hasDerivWithinAt_id t (Ioi t)).const_mul m).add_const c
  have heq : D.ironedPrimitive ψ =ᶠ[𝓝 t] fun x => m * x + c :=
    Filter.eventuallyEq_of_mem (Ioo_mem_nhds ht.1 ht.2) haffine
  exact (haff.congr_of_eventuallyEq (heq.filter_mono nhdsWithin_le_nhds)
    heq.eq_of_nhds).derivWithin (uniqueDiffWithinAt_Ioi t)

/-- Extend a quantile allocation by constants outside `(0, 1)`. -/
private noncomputable def clampedQuantileAllocation (x : ℝ → ℝ) (t : ℝ) : ℝ :=
  if t ≤ 0 then 0 else if 1 ≤ t then 1 else x (Measure.quantile (D : Measure ℝ) t)

/-- The constant extension of a bounded support-monotone allocation is globally monotone. -/
private lemma monotone_clampedQuantileAllocation
    (hsupport : D.IsSupportedOnInterval lower upper) {x : ℝ → ℝ}
    (hx : ∀ v ∈ Icc lower upper, x v ∈ Icc (0 : ℝ) 1)
    (hmono : MonotoneOn x (Icc lower upper)) : Monotone (D.clampedQuantileAllocation x) := by
  let X : ℝ → ℝ := fun t => x (Measure.quantile (D : Measure ℝ) t)
  have hX0 : ∀ t ∈ Ioo (0 : ℝ) 1, 0 ≤ X t := fun t ht =>
    (hx _ (D.quantile_mem_Icc hsupport ht)).1
  have hX1 : ∀ t ∈ Ioo (0 : ℝ) 1, X t ≤ 1 := fun t ht =>
    (hx _ (D.quantile_mem_Icc hsupport ht)).2
  have hXmono : MonotoneOn X (Ioo (0 : ℝ) 1) :=
    D.monotoneOn_comp_quantile hsupport hmono
  intro s t hst
  simp only [clampedQuantileAllocation]
  by_cases ht0 : t ≤ 0
  · rw [if_pos (hst.trans ht0), if_pos ht0]
  by_cases hs0 : s ≤ 0
  · rw [if_pos hs0, if_neg ht0]
    by_cases ht1 : 1 ≤ t
    · rw [if_pos ht1]
      norm_num
    · rw [if_neg ht1]
      exact hX0 t ⟨not_le.mp ht0, not_le.mp ht1⟩
  · rw [if_neg hs0]
    by_cases hs1 : 1 ≤ s
    · rw [if_pos hs1, if_neg ht0, if_pos (hs1.trans hst)]
    · rw [if_neg hs1]
      by_cases ht1 : 1 ≤ t
      · rw [if_neg ht0, if_pos ht1]
        exact hX1 s ⟨not_le.mp hs0, not_le.mp hs1⟩
      · rw [if_neg ht0, if_neg ht1]
        exact hXmono ⟨not_le.mp hs0, not_le.mp hs1⟩ ⟨not_le.mp ht0, not_le.mp ht1⟩ hst

/-- The quantile-space ironing gap is the primitive gap integrated against the allocation's
Stieltjes measure. -/
private theorem integral_gap_mul_eq_integral_stieltjes [NoAtoms (D : Measure ℝ)]
    (hsupport : D.IsSupportedOnInterval lower upper)
    (hψ : ContinuousOn ψ (Icc lower upper)) {x : ℝ → ℝ}
    (hx : ∀ v ∈ Icc lower upper, x v ∈ Icc (0 : ℝ) 1)
    (hmono : MonotoneOn x (Icc lower upper)) :
    ∫ t in Ioo (0 : ℝ) 1,
        (D.ironedQuantileScore ψ t - D.quantileScore ψ t) *
          x (Measure.quantile (D : Measure ℝ) t) =
      ∫ s in Ioc (0 : ℝ) 1, (D.scorePrimitive ψ s - D.ironedPrimitive ψ s)
        ∂(D.monotone_clampedQuantileAllocation hsupport hx hmono).stieltjesFunction.measure := by
  let X : ℝ → ℝ := fun t => x (Measure.quantile (D : Measure ℝ) t)
  let g : ℝ → ℝ := fun t => D.ironedQuantileScore ψ t - D.quantileScore ψ t
  let G : ℝ → ℝ := fun t => D.ironedPrimitive ψ t - D.scorePrimitive ψ t
  let Xe : ℝ → ℝ := D.clampedQuantileAllocation x
  have hXe_mono : Monotone Xe := D.monotone_clampedQuantileAllocation hsupport hx hmono
  have hXe_eq : ∀ t ∈ Ioo (0 : ℝ) 1, Xe t = X t := by
    intro t ht
    simp only [Xe, X, clampedQuantileAllocation, if_neg (not_le.mpr ht.1),
      if_neg (not_le.mpr ht.2)]
  have hg_ii : IntervalIntegrable g volume 0 1 :=
    (D.monotone_ironedQuantileScore ψ hsupport hψ).intervalIntegrable.sub
      (D.intervalIntegrable_quantileScore ψ hsupport hψ)
  have hcum : ∀ s ∈ Icc (0 : ℝ) 1, ∫ t in (0 : ℝ)..s, g t = G s :=
    fun s hs => D.integral_ironedQuantileScore_sub_quantileScore ψ hsupport hψ hs
  have hG1 : G 1 = 0 := by
    simp only [G, D.ironedPrimitive_one ψ hsupport hψ, sub_self]
  have hg01 : ∫ t in (0 : ℝ)..1, g t = 0 := by
    rw [hcum 1 (right_mem_Icc.mpr (by norm_num)), hG1]
  have htail : ∀ s ∈ Ioc (0 : ℝ) 1, ∫ t in s..1, g t = -G s := by
    intro s hs
    have hii0s : IntervalIntegrable g volume 0 s := hg_ii.mono_set (by
      rw [uIcc_of_le hs.1.le, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact Icc_subset_Icc_right hs.2)
    have hiis1 : IntervalIntegrable g volume s 1 := hg_ii.mono_set (by
      rw [uIcc_of_le hs.2, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact Icc_subset_Icc_left hs.1.le)
    have hsplit : (∫ t in (0 : ℝ)..s, g t) + ∫ t in s..(1 : ℝ), g t =
        ∫ t in (0 : ℝ)..1, g t :=
      intervalIntegral.integral_add_adjacent_intervals hii0s hiis1
    rw [hcum s ⟨hs.1.le, hs.2⟩, hg01] at hsplit
    linarith
  let Xsf := hXe_mono.stieltjesFunction
  let μX := hXe_mono.stieltjesFunction.measure
  have hX_eq_Xsf : (fun t => g t * X t) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      fun t => g t * Xsf t := by
    have hae : Xe =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] Xsf :=
      hXe_mono.stieltjesFunction_ae_eq.symm.restrict
    have hXeqXe : X =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] Xe :=
      (ae_restrict_iff' measurableSet_Ioo).mpr
        (ae_of_all _ fun t ht => (hXe_eq t ht).symm)
    filter_upwards [hXeqXe, hae] with t h1 h2
    rw [h1, h2]
  have hg_oc : IntegrableOn g (Ioc (0 : ℝ) 1) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp hg_ii
  have hXsf_bdd : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) 1)),
      ‖Xsf t‖ ≤ max |Xsf 0| |Xsf 1| := by
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun t ht => ?_)
    rw [Real.norm_eq_abs, abs_le]
    have hlo : Xsf 0 ≤ Xsf t := Xsf.mono ht.1.le
    have hhi : Xsf t ≤ Xsf 1 := Xsf.mono ht.2
    exact ⟨(neg_le_neg (le_max_left _ _)).trans ((neg_abs_le _).trans hlo),
      hhi.trans ((le_abs_self _).trans (le_max_right _ _))⟩
  have hg_Xsf_oc : IntegrableOn (fun t => g t * Xsf t) (Ioc (0 : ℝ) 1) volume := by
    rw [show (fun t => g t * Xsf t) = fun t => Xsf t * g t from
      funext fun t => mul_comm _ _]
    exact hg_oc.bdd_mul Xsf.mono.measurable.aestronglyMeasurable.restrict hXsf_bdd
  have hstep1 : ∫ t in Ioo (0 : ℝ) 1, g t * X t =
      ∫ t in Ioc (0 : ℝ) 1, g t * Xsf t := by
    rw [setIntegral_congr_set Ioo_ae_eq_Ioc]
    refine setIntegral_congr_ae measurableSet_Ioc ?_
    have h' : (fun t => g t * X t) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
        fun t => g t * Xsf t := by
      rwa [Measure.restrict_congr_set Ioo_ae_eq_Ioc] at hX_eq_Xsf
    exact (ae_restrict_iff' measurableSet_Ioc).mp h'
  have hstep2 : ∫ t in Ioc (0 : ℝ) 1, g t * Xsf t =
      ∫ t in (0 : ℝ)..1, g t * (Xsf t - Xsf 0) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    have hexpand : ∀ t, g t * (Xsf t - Xsf 0) = g t * Xsf t - Xsf 0 * g t :=
      fun t => by ring
    simp_rw [hexpand]
    rw [integral_sub hg_Xsf_oc (hg_oc.const_mul (Xsf 0))]
    have hconst : ∫ t in Ioc (0 : ℝ) 1, Xsf 0 * g t =
        Xsf 0 * ∫ t in (0 : ℝ)..1, g t := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_const_mul]
    rw [hconst, hg01, mul_zero, sub_zero]
  have hstep3 : ∫ t in (0 : ℝ)..1, g t * (Xsf t - Xsf 0) =
      ∫ s in Ioc (0 : ℝ) 1, (∫ t in s..1, g t) ∂μX :=
    integral_triangle_swap_stieltjes hXe_mono (by norm_num) hg_ii
  rw [hstep1, hstep2, hstep3]
  refine setIntegral_congr_fun measurableSet_Ioc (fun s hs => ?_)
  rw [htail s hs]
  simp only [G]
  ring

/-! ### Integral comparison -/

/-- Ironing weakly raises the score integral of every bounded monotone allocation. -/
theorem integral_mul_le_integral_mul_ironed [NoAtoms (D : Measure ℝ)]
    (hsupport : D.IsSupportedOnInterval lower upper)
    (hψ : ContinuousOn ψ (Icc lower upper)) {x : ℝ → ℝ}
    (hx : ∀ v ∈ Icc lower upper, x v ∈ Icc (0 : ℝ) 1)
    (hmono : MonotoneOn x (Icc lower upper)) :
    (∫ v, x v * ψ v ∂(D : Measure ℝ)) ≤
      ∫ v, x v * D.ironed ψ v ∂(D : Measure ℝ) := by
  let X : ℝ → ℝ := fun t => x (Measure.quantile (D : Measure ℝ) t)
  have hlhs_int := D.integrable_mul ψ hsupport hψ hx hmono
  have hrhs_int := D.integrable_mul_ironed ψ hsupport hψ hx hmono
  have hlhs : (∫ v, x v * ψ v ∂(D : Measure ℝ)) =
      ∫ t in Ioo (0 : ℝ) 1, X t * D.quantileScore ψ t := by
    simpa only [X, quantileScore] using
      D.integral_eq_integral_comp_quantile (fun v => x v * ψ v) hlhs_int.1
  have hrhs : (∫ v, x v * D.ironed ψ v ∂(D : Measure ℝ)) =
      ∫ t in Ioo (0 : ℝ) 1, X t * D.ironedQuantileScore ψ t := by
    rw [D.integral_eq_integral_comp_quantile
      (fun v => x v * D.ironed ψ v) hrhs_int.1]
    refine setIntegral_congr_fun measurableSet_Ioo (fun t ht => ?_)
    simp only [X, ironed]
    rw [D.cdf_quantile ht]
  rw [hlhs, hrhs]
  have hint_lhs : IntegrableOn (fun t => X t * D.quantileScore ψ t)
      (Ioo (0 : ℝ) 1) volume := by
    simpa only [X, quantileScore] using D.integrableOn_comp_quantile hlhs_int
  have hint_rhs : IntegrableOn (fun t => X t * D.ironedQuantileScore ψ t)
      (Ioo (0 : ℝ) 1) volume := by
    have h := D.integrableOn_comp_quantile hrhs_int
    refine h.congr ((ae_restrict_iff' measurableSet_Ioo).mpr (ae_of_all _ fun t ht => ?_))
    simp only [X, comp_apply, ironed]
    rw [D.cdf_quantile ht]
  have hsplit :
      ∫ t in Ioo (0 : ℝ) 1,
          (D.ironedQuantileScore ψ t - D.quantileScore ψ t) * X t =
        (∫ t in Ioo (0 : ℝ) 1, X t * D.ironedQuantileScore ψ t) -
          ∫ t in Ioo (0 : ℝ) 1, X t * D.quantileScore ψ t := by
    rw [← integral_sub hint_rhs hint_lhs]
    exact setIntegral_congr_fun measurableSet_Ioo (fun t _ => by ring)
  have hgap_nonneg : 0 ≤ ∫ t in Ioo (0 : ℝ) 1,
      (D.ironedQuantileScore ψ t - D.quantileScore ψ t) * X t := by
    rw [D.integral_gap_mul_eq_integral_stieltjes ψ hsupport hψ hx hmono]
    exact setIntegral_nonneg measurableSet_Ioc fun s hs =>
      sub_nonneg.mpr (D.ironedPrimitive_le_scorePrimitive ψ hsupport hψ
        ⟨hs.1.le, hs.2⟩)
  linarith [hsplit, hgap_nonneg]

/-- Ironing preserves the score integral when the allocation is flat on ironed-score levels. -/
theorem integral_mul_eq_integral_mul_ironed [NoAtoms (D : Measure ℝ)]
    (hsupport : D.IsSupportedOnInterval lower upper)
    (hψ : ContinuousOn ψ (Icc lower upper)) {x : ℝ → ℝ}
    (hx : ∀ v ∈ Icc lower upper, x v ∈ Icc (0 : ℝ) 1)
    (hmono : MonotoneOn x (Icc lower upper))
    (hflat : ∀ v ∈ Icc lower upper, ∀ w ∈ Icc lower upper,
      D.ironed ψ v = D.ironed ψ w → x v = x w) :
    (∫ v, x v * ψ v ∂(D : Measure ℝ)) =
      ∫ v, x v * D.ironed ψ v ∂(D : Measure ℝ) := by
  let X : ℝ → ℝ := fun t => x (Measure.quantile (D : Measure ℝ) t)
  let hXe_mono : Monotone (D.clampedQuantileAllocation x) :=
    D.monotone_clampedQuantileAllocation hsupport hx hmono
  let μX := hXe_mono.stieltjesFunction.measure
  have hlhs_int := D.integrable_mul ψ hsupport hψ hx hmono
  have hrhs_int := D.integrable_mul_ironed ψ hsupport hψ hx hmono
  have hlhs : (∫ v, x v * ψ v ∂(D : Measure ℝ)) =
      ∫ t in Ioo (0 : ℝ) 1, X t * D.quantileScore ψ t := by
    simpa only [X, quantileScore] using
      D.integral_eq_integral_comp_quantile (fun v => x v * ψ v) hlhs_int.1
  have hrhs : (∫ v, x v * D.ironed ψ v ∂(D : Measure ℝ)) =
      ∫ t in Ioo (0 : ℝ) 1, X t * D.ironedQuantileScore ψ t := by
    rw [D.integral_eq_integral_comp_quantile
      (fun v => x v * D.ironed ψ v) hrhs_int.1]
    refine setIntegral_congr_fun measurableSet_Ioo (fun t ht => ?_)
    simp only [X, ironed]
    rw [D.cdf_quantile ht]
  have hint_lhs : IntegrableOn (fun t => X t * D.quantileScore ψ t)
      (Ioo (0 : ℝ) 1) volume := by
    simpa only [X, quantileScore] using D.integrableOn_comp_quantile hlhs_int
  have hint_rhs : IntegrableOn (fun t => X t * D.ironedQuantileScore ψ t)
      (Ioo (0 : ℝ) 1) volume := by
    have h := D.integrableOn_comp_quantile hrhs_int
    refine h.congr ((ae_restrict_iff' measurableSet_Ioo).mpr (ae_of_all _ fun t ht => ?_))
    simp only [X, comp_apply, ironed]
    rw [D.cdf_quantile ht]
  have hsplit :
      ∫ t in Ioo (0 : ℝ) 1,
          (D.ironedQuantileScore ψ t - D.quantileScore ψ t) * X t =
        (∫ t in Ioo (0 : ℝ) 1, X t * D.ironedQuantileScore ψ t) -
          ∫ t in Ioo (0 : ℝ) 1, X t * D.quantileScore ψ t := by
    rw [← integral_sub hint_rhs hint_lhs]
    exact setIntegral_congr_fun measurableSet_Ioo (fun t _ => by ring)
  have hcore : ∫ t in Ioo (0 : ℝ) 1,
      (D.ironedQuantileScore ψ t - D.quantileScore ψ t) * X t =
      ∫ s in Ioc (0 : ℝ) 1, (D.scorePrimitive ψ s - D.ironedPrimitive ψ s) ∂μX := by
    exact D.integral_gap_mul_eq_integral_stieltjes ψ hsupport hψ hx hmono
  have hnull : μX {s | s ∈ Ioc (0 : ℝ) 1 ∧
      D.ironedPrimitive ψ s < D.scorePrimitive ψ s} = 0 := by
    refine measure_null_of_locally_null _ (fun s hs => ?_)
    obtain ⟨hs_oc, hlt⟩ := hs
    have hs_oo : s ∈ Ioo (0 : ℝ) 1 := by
      refine ⟨hs_oc.1, lt_of_le_of_ne hs_oc.2 (fun h1 => ?_)⟩
      rw [h1, D.ironedPrimitive_one ψ hsupport hψ] at hlt
      exact lt_irrefl _ hlt
    obtain ⟨p, r, m, c, _, _, hps, hsr, haffine⟩ :=
      convexEnvelope_affineOn_of_lt (by norm_num : (0 : ℝ) ≤ 1)
        (D.continuousOn_scorePrimitive ψ hsupport hψ) hs_oo hlt
    have haffine' : ∀ t ∈ Ioo p r, D.ironedPrimitive ψ t = m * t + c :=
      fun t ht => haffine t ⟨ht.1.le, ht.2.le⟩
    let p' := max p 0
    let r' := min r 1
    have hp'lt : p' < s := max_lt hps hs_oo.1
    have hsr' : s < r' := lt_min hsr hs_oo.2
    have hsub : Ioo p' r' ⊆ Ioo p r := fun t ht =>
      ⟨lt_of_le_of_lt (le_max_left _ _) ht.1,
        lt_of_lt_of_le ht.2 (min_le_left _ _)⟩
    have hsub01 : Ioo p' r' ⊆ Ioo (0 : ℝ) 1 := fun t ht =>
      ⟨lt_of_le_of_lt (le_max_right _ _) ht.1,
        lt_of_lt_of_le ht.2 (min_le_right _ _)⟩
    have haffine'' : ∀ t ∈ Ioo p' r', D.ironedPrimitive ψ t = m * t + c :=
      fun t ht => haffine' t (hsub ht)
    have hXe_const : ∀ t ∈ Ioo p' r', D.clampedQuantileAllocation x t = X s := by
      intro t ht
      have ht01 : t ∈ Ioo (0 : ℝ) 1 := hsub01 ht
      have hscore_t : D.ironedQuantileScore ψ t = m :=
        D.ironedQuantileScore_eq_of_affineOn ψ (le_max_right _ _) (min_le_right _ _)
          haffine'' ht
      have hscore_s : D.ironedQuantileScore ψ s = m :=
        D.ironedQuantileScore_eq_of_affineOn ψ (le_max_right _ _) (min_le_right _ _)
          haffine'' ⟨hp'lt, hsr'⟩
      have hi : D.ironed ψ (Measure.quantile (D : Measure ℝ) t) =
          D.ironed ψ (Measure.quantile (D : Measure ℝ) s) := by
        rw [ironed, ironed, D.cdf_quantile ht01, D.cdf_quantile hs_oo,
          hscore_t, hscore_s]
      simp only [clampedQuantileAllocation, if_neg (not_le.mpr ht01.1),
        if_neg (not_le.mpr ht01.2), X]
      exact hflat _ (D.quantile_mem_Icc hsupport ht01) _
        (D.quantile_mem_Icc hsupport hs_oo) hi
    have hμ_zero : μX (Ioo p' r') = 0 :=
      hXe_mono.stieltjesFunction_measure_Ioo_eq_zero (lt_trans hp'lt hsr') hXe_const
    refine ⟨Ioo p' r', ?_, hμ_zero⟩
    exact mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds hp'lt hsr')
  have hgap_zero : ∫ t in Ioo (0 : ℝ) 1,
      (D.ironedQuantileScore ψ t - D.quantileScore ψ t) * X t = 0 := by
    rw [hcore]
    refine setIntegral_eq_zero_of_ae_eq_zero ?_
    rw [ae_iff]
    refine measure_mono_null (fun s hs => ?_) hnull
    simp only [mem_setOf_eq, Classical.not_imp] at hs
    obtain ⟨hs_oc, hne⟩ := hs
    refine ⟨hs_oc, ?_⟩
    have hle := D.ironedPrimitive_le_scorePrimitive ψ hsupport hψ
      ⟨hs_oc.1.le, hs_oc.2⟩
    by_contra hge
    push_neg at hge
    exact hne (by linarith)
  rw [hlhs, hrhs]
  linarith [hsplit, hgap_zero]

/-! ### Regular scores -/

/-- If the score is monotone on the support, ironing does nothing at interior quantile levels. -/
theorem ironedQuantileScore_eq_quantileScore_of_monotoneOn
    [NoAtoms (D : Measure ℝ)] (hsupport : D.IsSupportedOnInterval lower upper)
    (hvol : volume.restrict (Icc lower upper) ≪ (D : Measure ℝ))
    (hψ : ContinuousOn ψ (Icc lower upper))
    (hmono : MonotoneOn ψ (Icc lower upper)) {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    D.ironedQuantileScore ψ q = D.quantileScore ψ q := by
  have hmono_q : MonotoneOn (D.quantileScore ψ) (Ioo (0 : ℝ) 1) :=
    D.monotoneOn_comp_quantile hsupport hmono
  have hEqOn : ∀ t ∈ Ioo (0 : ℝ) 1,
      D.ironedPrimitive ψ t = D.scorePrimitive ψ t := by
    intro t ht
    have hminor : IsAffineMinorant 0 1 (D.scorePrimitive ψ) (D.quantileScore ψ t)
        (D.scorePrimitive ψ t - D.quantileScore ψ t * t) := by
      intro r hr
      have hII_r : IntervalIntegrable (D.quantileScore ψ) volume 0 r :=
        (D.intervalIntegrable_quantileScore ψ hsupport hψ).mono_set (by
          rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), uIcc_of_le hr.1]
          exact Icc_subset_Icc_right hr.2)
      have hII_t : IntervalIntegrable (D.quantileScore ψ) volume 0 t :=
        (D.intervalIntegrable_quantileScore ψ hsupport hψ).mono_set (by
          rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), uIcc_of_le ht.1.le]
          exact Icc_subset_Icc_right ht.2.le)
      have hdiff : D.scorePrimitive ψ r - D.scorePrimitive ψ t =
          ∫ u in t..r, D.quantileScore ψ u :=
        intervalIntegral.integral_interval_sub_left hII_r hII_t
      have hkey : D.quantileScore ψ t * (r - t) ≤
          ∫ u in t..r, D.quantileScore ψ u := by
        rcases le_total t r with htr | hrt
        · have hII_tr : IntervalIntegrable (D.quantileScore ψ) volume t r :=
            (D.intervalIntegrable_quantileScore ψ hsupport hψ).mono_set (by
              rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), uIcc_of_le htr]
              exact Icc_subset_Icc ht.1.le hr.2)
          have hbound : ∀ u ∈ Ioo t r,
              D.quantileScore ψ t ≤ D.quantileScore ψ u := fun u hu =>
            hmono_q ht ⟨lt_trans ht.1 hu.1, lt_of_lt_of_le hu.2 hr.2⟩ hu.1.le
          have hconst : D.quantileScore ψ t * (r - t) =
              ∫ _u in t..r, D.quantileScore ψ t := by
            rw [intervalIntegral.integral_const, smul_eq_mul]
            ring
          have hle : (∫ _u in t..r, D.quantileScore ψ t) ≤
              ∫ u in t..r, D.quantileScore ψ u :=
            intervalIntegral.integral_mono_on_of_le_Ioo htr intervalIntegrable_const
              hII_tr hbound
          rwa [hconst]
        · have hII_rt : IntervalIntegrable (D.quantileScore ψ) volume r t :=
            (D.intervalIntegrable_quantileScore ψ hsupport hψ).mono_set (by
              rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), uIcc_of_le hrt]
              exact Icc_subset_Icc hr.1 ht.2.le)
          have hbound : ∀ u ∈ Ioo r t,
              D.quantileScore ψ u ≤ D.quantileScore ψ t := fun u hu =>
            hmono_q ⟨lt_of_le_of_lt hr.1 hu.1, lt_trans hu.2 ht.2⟩ ht hu.2.le
          have hconst : D.quantileScore ψ t * (t - r) =
              ∫ _u in r..t, D.quantileScore ψ t := by
            rw [intervalIntegral.integral_const, smul_eq_mul]
            ring
          have hle : (∫ u in r..t, D.quantileScore ψ u) ≤
              ∫ _u in r..t, D.quantileScore ψ t :=
            intervalIntegral.integral_mono_on_of_le_Ioo hrt hII_rt
              intervalIntegrable_const hbound
          have hsymm : (∫ u in t..r, D.quantileScore ψ u) =
              -(∫ u in r..t, D.quantileScore ψ u) := intervalIntegral.integral_symm r t
          rw [hsymm]
          rw [← hconst] at hle
          nlinarith
      nlinarith [hkey, hdiff]
    exact convexEnvelope_eq_of_affineMinorant_contact (by norm_num)
      (D.continuousOn_scorePrimitive ψ hsupport hψ) ⟨ht.1.le, ht.2.le⟩ hminor (by ring)
  have hev : D.ironedPrimitive ψ =ᶠ[𝓝[Ioi q] q] D.scorePrimitive ψ :=
    Filter.eventuallyEq_of_mem
      (mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds hq.1 hq.2)) hEqOn
  have htransfer : D.ironedQuantileScore ψ q =
      derivWithin (D.scorePrimitive ψ) (Ioi q) q := by
    rw [ironedQuantileScore, rightDerivExtend_of_mem_Ioo _ hq]
    exact hev.derivWithin_eq (hEqOn q hq)
  have hq_mem : Measure.quantile (D : Measure ℝ) q ∈ Ioo lower upper :=
    D.quantile_mem_Ioo hsupport hq
  have hcont_score : ContinuousAt (D.quantileScore ψ) q := by
    have hcontψ : ContinuousAt ψ (Measure.quantile (D : Measure ℝ) q) :=
      hψ.continuousAt
        (mem_of_superset (Ioo_mem_nhds hq_mem.1 hq_mem.2) Ioo_subset_Icc_self)
    exact hcontψ.comp (D.continuousAt_quantile hsupport hvol hq)
  have hII_q : IntervalIntegrable (D.quantileScore ψ) volume 0 q :=
    (D.intervalIntegrable_quantileScore ψ hsupport hψ).mono_set (by
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), uIcc_of_le hq.1.le]
      exact Icc_subset_Icc_right hq.2.le)
  have hmeas : StronglyMeasurableAtFilter (D.quantileScore ψ) (𝓝 q) := by
    refine ⟨Ioo (0 : ℝ) 1, Ioo_mem_nhds hq.1 hq.2, ?_⟩
    have hint : IntegrableOn (D.quantileScore ψ) (Ioc (0 : ℝ) 1) volume :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
        (D.intervalIntegrable_quantileScore ψ hsupport hψ)
    exact hint.1.mono_measure (Measure.restrict_mono Ioo_subset_Ioc_self le_rfl)
  have hderiv : HasDerivAt (D.scorePrimitive ψ) (D.quantileScore ψ q) q :=
    intervalIntegral.integral_hasDerivAt_right hII_q hmeas hcont_score
  have hright : derivWithin (D.scorePrimitive ψ) (Ioi q) q = D.quantileScore ψ q :=
    hderiv.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi q)
  rw [htransfer, hright]

/-- If the score is monotone on the support interval, ironing does nothing on its interior. -/
theorem ironed_eq_of_monotoneOn [NoAtoms (D : Measure ℝ)]
    (hsupport : D.IsSupportedOnInterval lower upper)
    (hvol : volume.restrict (Icc lower upper) ≪ (D : Measure ℝ))
    (hψ : ContinuousOn ψ (Icc lower upper))
    (hmono : MonotoneOn ψ (Icc lower upper)) {v : ℝ} (hv : v ∈ Ioo lower upper) :
    D.ironed ψ v = ψ v := by
  have ht : cdf (D : Measure ℝ) v ∈ Ioo (0 : ℝ) 1 := D.cdf_mem_Ioo hsupport hvol hv
  rw [ironed, D.ironedQuantileScore_eq_quantileScore_of_monotoneOn ψ
    hsupport hvol hψ hmono ht, quantileScore, D.quantile_cdf hsupport hvol hv]

/-! ### Single-parameter corollaries -/

/-- An envelope-IC problem's expected score is bounded by its expected ironed score. -/
theorem integral_q_mul_le_integral_q_mul_ironed {Action : Type*}
    (D : ValueDistribution) (P : SingleParameterProblem Action) [HasEnvelopeIC P]
    [NoAtoms (D : Measure ℝ)] (ψ : ℝ → ℝ)
    (hsupport : D.IsSupportedOnInterval P.lowestType P.highestType)
    (hψ : ContinuousOn ψ P.typeInterval) :
    (∫ v, P.q v * ψ v ∂(D : Measure ℝ)) ≤
      ∫ v, P.q v * D.ironed ψ v ∂(D : Measure ℝ) :=
  D.integral_mul_le_integral_mul_ironed ψ hsupport hψ
    (fun v _ => P.q_range v) P.q_monotoneOn

/-- The score and ironed-score integrals agree when the allocation is flat on ironed levels. -/
theorem integral_q_mul_eq_integral_q_mul_ironed {Action : Type*}
    (D : ValueDistribution) (P : SingleParameterProblem Action) [HasEnvelopeIC P]
    [NoAtoms (D : Measure ℝ)] (ψ : ℝ → ℝ)
    (hsupport : D.IsSupportedOnInterval P.lowestType P.highestType)
    (hψ : ContinuousOn ψ P.typeInterval)
    (hflat : ∀ v ∈ P.typeInterval, ∀ w ∈ P.typeInterval,
      D.ironed ψ v = D.ironed ψ w → P.q v = P.q w) :
    (∫ v, P.q v * ψ v ∂(D : Measure ℝ)) =
      ∫ v, P.q v * D.ironed ψ v ∂(D : Measure ℝ) :=
  D.integral_mul_eq_integral_mul_ironed ψ hsupport hψ
    (fun v _ => P.q_range v) P.q_monotoneOn hflat

/-- Individual rationality bounds expected payment by expected ironed virtual value. -/
theorem expectedPayment_le_integral_q_mul_ironed_virtualValue {Action : Type*}
    (D : ValueDistribution) (P : SingleParameterProblem Action) [HasEnvelopeIC P]
    (density : ℝ → ℝ) (horder : P.lowestType ≤ P.highestType)
    (hsupport : D.IsSupportedOnInterval P.lowestType P.highestType)
    (hD : (D : Measure ℝ) ≪ volume)
    (hdensity : density =ᵐ[volume.restrict P.typeInterval] D.realDensity)
    (hcont : ContinuousOn density P.typeInterval)
    (hpos : ∀ v ∈ P.typeInterval, 0 < density v)
    (hIR : P.IsIndividuallyRational) :
    D.expectedPayment P ≤
      ∫ v, P.q v * D.ironed (D.virtualValue density) v ∂(D : Measure ℝ) := by
  letI : NoAtoms (D : Measure ℝ) := noAtoms_of_absolutelyContinuous_volume hD
  have hpos_ae : ∀ᵐ v ∂(volume.restrict P.typeInterval), 0 < density v :=
    ae_restrict_of_forall_mem measurableSet_Icc hpos
  calc
    D.expectedPayment P ≤
        ∫ v, P.q v * D.virtualValue density v ∂(D : Measure ℝ) :=
      D.expectedPayment_le_integral_q_mul_virtualValue P density horder hsupport hD
        hdensity hpos_ae hIR
    _ ≤ ∫ v, P.q v * D.ironed (D.virtualValue density) v ∂(D : Measure ℝ) :=
      D.integral_q_mul_le_integral_q_mul_ironed P (D.virtualValue density) hsupport
        (D.continuousOn_virtualValue hcont hpos)

/-- For a regular distribution, ironing leaves the virtual value unchanged on the interior. -/
theorem ironed_virtualValue_eq_of_isRegular (D : ValueDistribution) (density : ℝ → ℝ)
    {lower upper : ℝ} (hsupport : D.IsSupportedOnInterval lower upper)
    (hD : (D : Measure ℝ) ≪ volume)
    (hdensity : density =ᵐ[volume.restrict (Icc lower upper)] D.realDensity)
    (hcont : ContinuousOn density (Icc lower upper))
    (hpos : ∀ v ∈ Icc lower upper, 0 < density v)
    (hreg : D.IsRegular density lower upper) {v : ℝ} (hv : v ∈ Ioo lower upper) :
    D.ironed (D.virtualValue density) v = D.virtualValue density v := by
  letI : NoAtoms (D : Measure ℝ) := noAtoms_of_absolutelyContinuous_volume hD
  have hpos_ae : ∀ᵐ w ∂(volume.restrict (Icc lower upper)), 0 < density w :=
    ae_restrict_of_forall_mem measurableSet_Icc hpos
  have hvol : volume.restrict (Icc lower upper) ≪ (D : Measure ℝ) :=
    D.absolutelyContinuous_volume_restrict_of_ae_pos hD hdensity hpos_ae
  exact D.ironed_eq_of_monotoneOn (D.virtualValue density) hsupport hvol
    (D.continuousOn_virtualValue hcont hpos) hreg hv

end ValueDistribution

end
