/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Probability.CDF
public import Mathlib.Topology.Order.LeftRightLim

/-!
# Auxiliary facts about cumulative distribution functions

Continuity and support lemmas for Stieltjes functions and probability CDFs.
-/

@[expose] public section

open Filter MeasureTheory Set Topology

namespace StieltjesFunction

/-- A Stieltjes function has no jump at a point where its associated measure has no atom. -/
lemma leftLim_eq_of_measure_singleton_eq_zero (f : StieltjesFunction ℝ) {x : ℝ}
    (hx : f.measure {x} = 0) : Function.leftLim f x = f x := by
  rw [f.measure_singleton, ENNReal.ofReal_eq_zero] at hx
  exact le_antisymm (f.mono.leftLim_le le_rfl) (sub_nonpos.mp hx)

/-- A Stieltjes function is continuous at every point where its associated measure has no atom. -/
lemma continuousAt_of_measure_singleton_eq_zero (f : StieltjesFunction ℝ) {x : ℝ}
    (hx : f.measure {x} = 0) : ContinuousAt f x := by
  rw [f.mono.continuousAt_iff_leftLim_eq_rightLim, f.rightLim_eq]
  exact f.leftLim_eq_of_measure_singleton_eq_zero hx

/-- A Stieltjes function whose associated measure is atomless is continuous. -/
lemma continuous_of_noAtoms (f : StieltjesFunction ℝ) [NoAtoms f.measure] : Continuous f := by
  rw [continuous_iff_continuousAt]
  exact fun x =>
    f.continuousAt_of_measure_singleton_eq_zero
      (MeasureTheory.measure_singleton x)

end StieltjesFunction

namespace ProbabilityTheory

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

/-- The CDF of an atomless probability measure is continuous. -/
lemma continuous_cdf [NoAtoms μ] : Continuous (cdf μ) := by
  letI : NoAtoms (cdf μ).measure := by
    rw [measure_cdf μ]
    infer_instance
  exact (cdf μ).continuous_of_noAtoms

/-- A CDF vanishes strictly below a closed interval supporting the measure. -/
lemma cdf_eq_zero_of_lt {a b x : ℝ} (hsupp : ∀ᵐ y ∂μ, y ∈ Icc a b) (hx : x < a) :
    cdf μ x = 0 := by
  have hsupp_zero : μ {y | ¬y ∈ Icc a b} = 0 := ae_iff.mp hsupp
  have hIic : μ (Iic x) = 0 := by
    refine measure_mono_null ?_ hsupp_zero
    intro y hy hy_mem
    exact (not_lt_of_ge hy_mem.1) (hy.trans_lt hx)
  rw [cdf_eq_real, Measure.real, hIic, ENNReal.toReal_zero]

/-- A CDF is one at and above the right endpoint of a closed interval supporting the measure. -/
lemma cdf_eq_one_of_le {a b x : ℝ} (hsupp : ∀ᵐ y ∂μ, y ∈ Icc a b) (hx : b ≤ x) :
    cdf μ x = 1 := by
  have hIic : ∀ᵐ y ∂μ, y ∈ Iic x := hsupp.mono fun _ hy => hy.2.trans hx
  have hmeasure : μ (Iic x) = 1 := (mem_ae_iff_prob_eq_one measurableSet_Iic).mp hIic
  rw [cdf_eq_real, Measure.real, hmeasure, ENNReal.toReal_one]

/-- For an atomless measure supported on `[a, b]`, its CDF vanishes at `a`. -/
lemma cdf_left_eq_zero [NoAtoms μ] {a b : ℝ} (hsupp : ∀ᵐ y ∂μ, y ∈ Icc a b) :
    cdf μ a = 0 := by
  have hlim : Tendsto (cdf μ) (𝓝[<] a) (𝓝 (cdf μ a)) :=
    continuous_cdf.continuousAt.continuousWithinAt.tendsto
  have hzero : Tendsto (cdf μ) (𝓝[<] a) (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (cdf_eq_zero_of_lt hsupp hx).symm
  haveI : (𝓝[<] a).NeBot := nhdsWithin_Iio_neBot le_rfl
  exact tendsto_nhds_unique hlim hzero

/-- The CDF is strictly increasing between two points in an interval on which Lebesgue measure is
absolutely continuous with respect to the probability measure. -/
lemma cdf_lt_cdf_of_absolutelyContinuous {a b x y : ℝ}
    (hac : volume.restrict (Icc a b) ≪ μ) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b)
    (hxy : x < y) : cdf μ x < cdf μ y := by
  have hinter : Ioc x y ∩ Icc a b = Ioc x y := by
    ext z
    constructor
    · exact fun hz => hz.1
    · intro hz
      exact ⟨hz, ⟨hx.1.trans hz.1.le, hz.2.trans hy.2⟩⟩
  have hvolume : 0 < (volume.restrict (Icc a b)) (Ioc x y) := by
    rw [Measure.restrict_apply measurableSet_Ioc, hinter, Real.volume_Ioc]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hxy)
  have hmeasure : 0 < μ (Ioc x y) := hac.pos_mono hvolume
  rw [← measure_cdf μ, (cdf μ).measure_Ioc] at hmeasure
  exact sub_pos.mp (ENNReal.ofReal_pos.mp hmeasure)

/-- The CDF is strictly monotone on an interval where Lebesgue measure is absolutely continuous
with respect to the probability measure. -/
lemma strictMonoOn_cdf {a b : ℝ} (hac : volume.restrict (Icc a b) ≪ μ) :
    StrictMonoOn (cdf μ) (Icc a b) := fun _ hx _ hy hxy =>
  cdf_lt_cdf_of_absolutelyContinuous hac hx hy hxy

/-- The CDF is positive at every interior point of an interval on which Lebesgue measure is
absolutely continuous with respect to the probability measure. -/
lemma cdf_pos_of_mem_Ioo {a b x : ℝ} (hac : volume.restrict (Icc a b) ≪ μ)
    (hx : x ∈ Ioo a b) : 0 < cdf μ x :=
  lt_of_le_of_lt (cdf_nonneg μ a)
    (cdf_lt_cdf_of_absolutelyContinuous (a := a) (b := b) (x := a) (y := x) hac
      ⟨le_rfl, hx.1.le.trans hx.2.le⟩ ⟨hx.1.le, hx.2.le⟩ hx.1)

/-- On the interior of an atomless measure's support interval, its CDF takes values in `(0, 1)`. -/
lemma cdf_mem_Ioo [NoAtoms μ] {a b x : ℝ} (hsupp : ∀ᵐ y ∂μ, y ∈ Icc a b)
    (hac : volume.restrict (Icc a b) ≪ μ) (hx : x ∈ Ioo a b) : cdf μ x ∈ Ioo 0 1 := by
  refine ⟨cdf_pos_of_mem_Ioo hac hx, ?_⟩
  have hlt : cdf μ x < cdf μ b :=
    cdf_lt_cdf_of_absolutelyContinuous (a := a) (b := b) (x := x) (y := b) hac
      ⟨hx.1.le, hx.2.le⟩ ⟨hx.1.le.trans hx.2.le, le_rfl⟩ hx.2
  rwa [cdf_eq_one_of_le hsupp le_rfl] at hlt

end ProbabilityTheory

end
