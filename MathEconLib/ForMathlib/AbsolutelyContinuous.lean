/-
Copyright (c) 2026 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
module

public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Mathlib.Probability.CDF
public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# Auxiliary lemmas for absolute continuity and Radon-Nikodym derivatives

Lemmas that should eventually be upstreamed to Mathlib.

## Main results

* `AbsolutelyContinuousOnInterval.pow`: if `f` is AC on `[a, s]`, then `f ^ n` is too.
* `ae_restrict_rnDeriv_eq_zero`: if `μ ≪ ν` and `μ(S) = 0`, the Radon-Nikodym derivative
  vanishes a.e. on `S`.
* `absolutelyContinuousOnInterval_cdf`: the CDF of a probability measure `μ ≪ volume`
  is AC on any interval where `cdf μ a = 0`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory MeasureTheory.Measure

/-- If `f` is absolutely continuous on `[a, s]`, then so is `f ^ n`. -/
theorem AbsolutelyContinuousOnInterval.pow {f : ℝ → ℝ} {a s : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a s) (n : ℕ) :
    AbsolutelyContinuousOnInterval (fun x => f x ^ n) a s := by
  induction n with
  | zero =>
    simp only [pow_zero]
    exact (LipschitzWith.const 1).lipschitzOnWith.absolutelyContinuousOnInterval
  | succ k ih =>
    simp_rw [pow_succ]; exact ih.mul hf

/-- If `μ ≪ ν` and `μ(S) = 0` for a measurable set `S`, then the Radon–Nikodym derivative
`rnDeriv μ ν` vanishes a.e. on `S`. -/
theorem ae_restrict_rnDeriv_eq_zero {α : Type*} {m : MeasurableSpace α}
    {μ ν : Measure α} [SigmaFinite ν] [μ.HaveLebesgueDecomposition ν] (habs : μ ≪ ν) {S : Set α}
    (hS : MeasurableSet S) (hmass : μ S = 0) :
    ∀ᵐ x ∂ν, x ∈ S → (μ.rnDeriv ν x).toReal = 0 := by
  have h := (lintegral_eq_zero_iff (measurable_rnDeriv _ _)).mp <|
    show ∫⁻ x in S, μ.rnDeriv ν x ∂ν = 0 by rwa [setLIntegral_rnDeriv habs]
  rw [Filter.EventuallyEq, ae_restrict_iff' hS] at h
  filter_upwards [h] with x hx h_mem
  have h0 := hx h_mem; simp only [Pi.zero_apply] at h0; simp [h0]

/-- The CDF of a measure absolutely continuous w.r.t. Lebesgue measure is absolutely continuous
on any interval `[a, s]` where `cdf μ a = 0`. -/
theorem absolutelyContinuousOnInterval_cdf {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (habs : μ ≪ volume) {a s : ℝ} (ha : cdf μ a = 0) :
    AbsolutelyContinuousOnInterval (cdf μ) a s := by
  set F := cdf μ
  set g : ℝ → ℝ := fun t => (μ.rnDeriv volume t).toReal
  have hg_int : IntervalIntegrable g volume a s :=
    intervalIntegrable_iff.mpr integrable_toReal_rnDeriv.integrableOn
  have h_eq : (fun x => F x) = fun x => ∫ t in a..x, g t := by
    have hFm : F.measure = μ := measure_cdf μ
    ext x
    by_cases hax : a ≤ x
    · have h1 : ∫ t in Set.Ioc a x, g t ∂volume = F x := by
        trans μ.real (Set.Ioc a x)
        · exact setIntegral_toReal_rnDeriv habs _
        · show (μ (Set.Ioc a x)).toReal = F x
          rw [← hFm, F.measure_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr (F.mono hax)), ha,
            sub_zero]
      rw [intervalIntegral.integral_of_le hax, h1]
    · push_neg at hax
      have hFx : F x = 0 := by
        have h1 : F x ≤ F a := F.mono hax.le
        linarith [cdf_nonneg μ x]
      have h1 : ∫ t in Set.Ioc x a, g t ∂volume = 0 := by
        trans μ.real (Set.Ioc x a)
        · exact setIntegral_toReal_rnDeriv habs _
        · show (μ (Set.Ioc x a)).toReal = 0
          rw [← hFm, F.measure_Ioc, ha, hFx, sub_zero,
              ENNReal.ofReal_zero, ENNReal.toReal_zero]
      rw [hFx, intervalIntegral.integral_symm, intervalIntegral.integral_of_le hax.le,
          h1, neg_zero]
  show AbsolutelyContinuousOnInterval (fun x => F x) a s
  rw [h_eq]
  exact hg_int.absolutelyContinuousOnInterval_intervalIntegral Set.left_mem_uIcc
