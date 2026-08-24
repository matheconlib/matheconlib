/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Auctionlib.ForMathlib.CDF
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Quantile function of a probability measure on the real line

The generalized inverse of the CDF, its pushforward identity, and inverse and continuity facts on a
compact support interval.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set Topology

noncomputable section

namespace Real

/-- Lebesgue measure restricted to `(0, 1)` is a probability measure. -/
instance isProbabilityMeasure_volume_restrict_Ioo_zero_one :
    IsProbabilityMeasure ((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ, Real.volume_Ioo]
  simp

end Real

namespace MeasureTheory.Measure

variable (μ : Measure ℝ)

/-- The generalized inverse of the CDF. Outside `(0, 1)`, its value is unspecified. -/
def quantile (t : ℝ) : ℝ :=
  sInf {x : ℝ | t ≤ cdf μ x}

variable {μ}

namespace Quantile

/-- For `t < 1`, the superlevel set of the CDF at height `t` is nonempty. -/
lemma set_nonempty {t : ℝ} (ht : t < 1) : ({x : ℝ | t ≤ cdf μ x}).Nonempty := by
  have h := tendsto_cdf_atTop μ
  have hε : 0 < 1 - t := sub_pos.mpr ht
  rw [Metric.tendsto_atTop] at h
  obtain ⟨N, hN⟩ := h (1 - t) hε
  refine ⟨N, ?_⟩
  have h1 := hN N le_rfl
  rw [Real.dist_eq, abs_sub_lt_iff] at h1
  simp only [mem_setOf_eq]
  linarith

/-- For `0 < t`, the superlevel set of the CDF at height `t` is bounded below. -/
lemma set_bddBelow {t : ℝ} (ht : 0 < t) : BddBelow {x : ℝ | t ≤ cdf μ x} := by
  have h := tendsto_cdf_atBot μ
  rw [Metric.tendsto_nhds] at h
  have hevent := h t ht
  rw [Filter.eventually_atBot] at hevent
  obtain ⟨N, hN⟩ := hevent
  refine ⟨N, ?_⟩
  intro x hx
  by_contra hnot
  push Not at hnot
  have hd := hN x hnot.le
  rw [Real.dist_eq, sub_zero, abs_lt] at hd
  simp only [mem_setOf_eq] at hx
  linarith

end Quantile

/-- Galois identity between the quantile and the CDF on the interior probability range. -/
lemma quantile_le_iff {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) {x : ℝ} :
    quantile μ t ≤ x ↔ t ≤ cdf μ x := by
  obtain ⟨ht_pos, ht_lt⟩ := ht
  refine ⟨fun h => ?_, fun h => csInf_le (Quantile.set_bddBelow ht_pos) h⟩
  set q := quantile μ t with hq
  have hset_nonempty := Quantile.set_nonempty (μ := μ) ht_lt
  have hset_bddBelow := Quantile.set_bddBelow (μ := μ) ht_pos
  have hq_mem : t ≤ cdf μ q := by
    have hright := (cdf μ).right_continuous q
    rw [Metric.continuousWithinAt_iff] at hright
    by_contra hnot
    push Not at hnot
    have hε : 0 < t - cdf μ q := sub_pos.mpr hnot
    obtain ⟨δ, hδ_pos, hδ⟩ := hright (t - cdf μ q) hε
    have hexists : ∃ y, y ∈ {z : ℝ | t ≤ cdf μ z} ∧ y < q + δ := by
      by_contra hne
      push Not at hne
      have hlower : q + δ ≤ q := by
        apply le_csInf hset_nonempty
        intro y hy
        exact hne y hy
      linarith
    obtain ⟨y, hy, hy_lt⟩ := hexists
    have hqy : q ≤ y := csInf_le hset_bddBelow hy
    have hdist : dist y q < δ := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hqy)]
      linarith
    have hclose := hδ hqy hdist
    rw [Real.dist_eq, abs_lt] at hclose
    have hy' : t ≤ cdf μ y := hy
    linarith [hclose.2]
  exact hq_mem.trans (monotone_cdf μ h)

/-- The quantile lies in its defining CDF superlevel set. -/
lemma le_cdf_quantile {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    t ≤ cdf μ (quantile μ t) :=
  (quantile_le_iff ht).mp le_rfl

/-- The quantile function is monotone on `(0, 1)`. -/
lemma monotoneOn_quantile : MonotoneOn (quantile μ) (Ioo (0 : ℝ) 1) := by
  intro s hs t ht hst
  rw [quantile_le_iff hs]
  exact hst.trans (le_cdf_quantile ht)

/-- The quantile is almost everywhere measurable on `(0, 1)`. -/
lemma aemeasurable_quantile_restrict_Ioo :
    AEMeasurable (quantile μ) (volume.restrict (Ioo (0 : ℝ) 1)) :=
  aemeasurable_restrict_of_monotoneOn measurableSet_Ioo monotoneOn_quantile

/-- For an atomless probability measure, the CDF attains every interior level at its quantile. -/
lemma cdf_quantile [IsProbabilityMeasure μ] [NoAtoms μ] {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) : cdf μ (quantile μ t) = t := by
  set q := quantile μ t
  refine le_antisymm ?_ (le_cdf_quantile ht)
  have hlt : ∀ x < q, cdf μ x < t := fun x hx =>
    lt_of_not_ge fun hle => hx.not_ge ((quantile_le_iff ht).mpr hle)
  have htend : Tendsto (cdf μ) (𝓝[<] q) (𝓝 (cdf μ q)) :=
    continuous_cdf.continuousAt.continuousWithinAt.tendsto
  haveI : (𝓝[<] q).NeBot := nhdsWithin_Iio_neBot le_rfl
  refine le_of_tendsto htend ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (hlt x hx).le

/-! ### Pushforward of uniform measure under the quantile -/

/-- Volume of the portion of `(0, 1)` below a point in `[0, 1]`. -/
private lemma volume_Ioo_inter_Iic {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    volume (Ioo (0 : ℝ) 1 ∩ Iic a) = ENNReal.ofReal a := by
  rcases eq_or_lt_of_le ha1 with rfl | ha1
  · have heq : Ioo (0 : ℝ) 1 ∩ Iic 1 = Ioo (0 : ℝ) 1 := by
      ext x
      simp only [mem_inter_iff, mem_Ioo, mem_Iic]
      exact and_iff_left_of_imp fun hx => hx.2.le
    rw [heq, Real.volume_Ioo]
    norm_num
  · have heq : Ioo (0 : ℝ) 1 ∩ Iic a = Ioc 0 a := by
      ext x
      simp only [mem_inter_iff, mem_Ioo, mem_Iic, mem_Ioc]
      constructor
      · exact fun hx => ⟨hx.1.1, hx.2⟩
      · exact fun hx => ⟨⟨hx.1, hx.2.trans_lt ha1⟩, hx.2⟩
    rw [heq, Real.volume_Ioc]
    ring_nf

/-- The pushforward of uniform measure under the quantile, evaluated on a lower half-line. -/
private lemma map_quantile_apply_Iic [IsProbabilityMeasure μ] (x : ℝ) :
    (Measure.map (quantile μ) (volume.restrict (Ioo (0 : ℝ) 1))) (Iic x) = μ (Iic x) := by
  rw [Measure.map_apply_of_aemeasurable aemeasurable_quantile_restrict_Ioo measurableSet_Iic]
  rw [Measure.restrict_apply' measurableSet_Ioo]
  set a := cdf μ x with ha
  have ha0 : 0 ≤ a := cdf_nonneg μ x
  have ha1 : a ≤ 1 := cdf_le_one μ x
  have heq : quantile μ ⁻¹' Iic x ∩ Ioo (0 : ℝ) 1 = Ioo (0 : ℝ) 1 ∩ Iic a := by
    ext t
    simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ioo]
    constructor
    · exact fun ht => ⟨ht.2, (quantile_le_iff ht.2).mp ht.1⟩
    · exact fun ht => ⟨(quantile_le_iff ht.1).mpr ht.2, ht.1⟩
  rw [heq, volume_Ioo_inter_Iic ha0 ha1, ← ofReal_cdf μ x, ha]

/-- The pushforward of Lebesgue measure on `(0, 1)` under the quantile is the original probability
measure. -/
theorem map_quantile_volume_Ioo [IsProbabilityMeasure μ] :
    Measure.map (quantile μ) (volume.restrict (Ioo (0 : ℝ) 1)) = μ := by
  haveI : IsProbabilityMeasure
      (Measure.map (quantile μ) (volume.restrict (Ioo (0 : ℝ) 1))) :=
    Measure.isProbabilityMeasure_map aemeasurable_quantile_restrict_Ioo
  refine Measure.ext_of_Iic _ _ fun x => ?_
  exact map_quantile_apply_Iic x

/-- Change of variables from a probability measure to its quantile representation. -/
theorem integral_eq_integral_quantile [IsProbabilityMeasure μ]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (φ : ℝ → E)
    (hφ : AEStronglyMeasurable φ μ) :
    ∫ x, φ x ∂μ = ∫ t in Ioo (0 : ℝ) 1, φ (quantile μ t) := by
  conv_lhs => rw [← map_quantile_volume_Ioo (μ := μ)]
  rw [MeasureTheory.integral_map aemeasurable_quantile_restrict_Ioo]
  rw [map_quantile_volume_Ioo (μ := μ)]
  exact hφ

/-! ### Compact-support inverse and continuity facts -/

/-- Every interior quantile belongs to any closed interval supporting the probability measure. -/
lemma quantile_mem_Icc [IsProbabilityMeasure μ] {a b : ℝ}
    (hsupp : ∀ᵐ y ∂μ, y ∈ Icc a b) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    quantile μ t ∈ Icc a b := by
  constructor
  · by_contra hlt
    push Not at hlt
    have hle := le_cdf_quantile (μ := μ) ht
    rw [cdf_eq_zero_of_lt hsupp hlt] at hle
    exact (not_le_of_gt ht.1) hle
  · rw [quantile_le_iff ht, cdf_eq_one_of_le hsupp le_rfl]
    exact ht.2.le

/-- Every interior quantile belongs to the interior of an atomless measure's support interval. -/
lemma quantile_mem_Ioo [IsProbabilityMeasure μ] [NoAtoms μ] {a b : ℝ}
    (hsupp : ∀ᵐ y ∂μ, y ∈ Icc a b) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    quantile μ t ∈ Ioo a b := by
  have hcdf : cdf μ (quantile μ t) = t := cdf_quantile ht
  have hmem : quantile μ t ∈ Icc a b := quantile_mem_Icc hsupp ht
  refine ⟨lt_of_le_of_ne hmem.1 ?_, lt_of_le_of_ne hmem.2 ?_⟩
  · intro h
    rw [← h, cdf_left_eq_zero hsupp] at hcdf
    exact (ne_of_lt ht.1) hcdf
  · intro h
    rw [h, cdf_eq_one_of_le hsupp le_rfl] at hcdf
    exact (ne_of_lt ht.2) hcdf.symm

/-- On the interior of a support interval where the CDF is strictly increasing, quantile is a left
inverse of the CDF. -/
lemma quantile_cdf [IsProbabilityMeasure μ] [NoAtoms μ] {a b : ℝ}
    (hsupp : ∀ᵐ y ∂μ, y ∈ Icc a b) (hac : volume.restrict (Icc a b) ≪ μ)
    {x : ℝ} (hx : x ∈ Ioo a b) : quantile μ (cdf μ x) = x := by
  have ht : cdf μ x ∈ Ioo (0 : ℝ) 1 := cdf_mem_Ioo hsupp hac hx
  refine le_antisymm ((quantile_le_iff ht).mpr le_rfl) ?_
  by_contra hlt
  push Not at hlt
  have hq_mem : quantile μ (cdf μ x) ∈ Icc a b := quantile_mem_Icc hsupp ht
  have hstrict : cdf μ (quantile μ (cdf μ x)) < cdf μ x :=
    strictMonoOn_cdf hac hq_mem ⟨hx.1.le, hx.2.le⟩ hlt
  have hge : cdf μ x ≤ cdf μ (quantile μ (cdf μ x)) := le_cdf_quantile ht
  linarith

/-- The quantile is continuous at every interior probability level when the measure has an
atomless, strictly increasing CDF on its compact support. -/
lemma continuousAt_quantile [IsProbabilityMeasure μ] [NoAtoms μ] {a b : ℝ}
    (hsupp : ∀ᵐ y ∂μ, y ∈ Icc a b) (hac : volume.restrict (Icc a b) ≪ μ)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : ContinuousAt (quantile μ) t := by
  have hq_mem : quantile μ t ∈ Ioo a b := quantile_mem_Ioo hsupp ht
  have himage : quantile μ '' Ioo (0 : ℝ) 1 ∈ 𝓝 (quantile μ t) := by
    refine mem_of_superset (Ioo_mem_nhds hq_mem.1 hq_mem.2) ?_
    intro x hx
    exact ⟨cdf μ x, cdf_mem_Ioo hsupp hac hx, quantile_cdf hsupp hac hx⟩
  exact continuousAt_of_monotoneOn_of_image_mem_nhds monotoneOn_quantile
    (Ioo_mem_nhds ht.1 ht.2) himage

end MeasureTheory.Measure

end
