/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.MeasureTheory.Measure.Stieltjes
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Triangle Fubini swaps

This file proves Fubini-type swaps over the triangle `T = {(s, θ) : a ≤ s ≤ θ ≤ b}`, first for two
real functions `g, f : ℝ → ℝ` integrated against Lebesgue measure, then for a Lebesgue weight
against a Stieltjes measure. Writing each side as a two-dimensional integral over `[a,b] × [a,b]`
of the integrand restricted to the triangle and applying `MeasureTheory.integral_integral_swap`,
the Lebesgue × Lebesgue form is

`(∫ θ in a..b, (∫ s in a..θ, g s) * f θ) = ∫ s in a..b, g s * (∫ θ in s..b, f θ)`,

so the cumulative integral of `g` weighted by `f` equals `g` weighted by the tail integral of `f`.

## Main statements

* `MeasureTheory.integral_triangle_swap` — the Lebesgue × Lebesgue swap.
* `MeasureTheory.integral_triangle_swap_stieltjes` — the Lebesgue × Stieltjes swap: For monotone
  `u` with Stieltjes measure `μ_u`, the cumulative Stieltjes increment
  `u_sf t − u_sf a = μ_u((a,t])` weighted by `g` equals the tail integral of `g` against `μ_u`.

## Notes

The only regularity needed is interval-integrability of `g` and `f` on `[a, b]`. Over the finite
measure `volume.restrict (Ioc a b)` the product `g s · f θ` is integrable (`Integrable.mul_prod`),
so the indicator restriction to the triangle stays integrable and the integrable form of Fubini
`MeasureTheory.integral_integral_swap` applies. Neither boundedness of `g` nor nonnegativity of `f`
is required.

## Tags

fubini, tonelli, triangle, stieltjes measure, integration by parts
-/

@[expose] public section

open MeasureTheory Set

noncomputable section

namespace MeasureTheory

/-- **Triangle Fubini swap.** For `g` and `f` interval-integrable on `[a, b]`, swapping the order
of integration over the triangle `{(s, θ) : a ≤ s ≤ θ ≤ b}` gives

`(∫ θ in a..b, (∫ s in a..θ, g s) * f θ) = ∫ s in a..b, g s * (∫ θ in s..b, f θ)`.

The left side integrates `g` cumulatively (up to `θ`) weighted by `f θ`; the right integrates `g`
pointwise weighted by the tail mass of `f` above `s`. -/
theorem integral_triangle_swap {a b : ℝ} (hab : a ≤ b) {g f : ℝ → ℝ}
    (hg : IntervalIntegrable g volume a b) (hf : IntervalIntegrable f volume a b) :
    (∫ θ in a..b, (∫ s in a..θ, g s) * f θ)
      = ∫ s in a..b, g s * (∫ θ in s..b, f θ) := by
  -- The triangle `T = {(s, θ) : a ≤ s ≤ θ ≤ b}`, with `s = p.1`, `θ = p.2`.
  set T : Set (ℝ × ℝ) := {p | a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b} with hT_def
  have hT_meas : MeasurableSet T :=
    (measurableSet_le measurable_const measurable_fst).inter
      ((measurableSet_le measurable_fst measurable_snd).inter
        (measurableSet_le measurable_snd measurable_const))
  -- Work with `volume` restricted to `Ioc a b` on both factors (a finite measure).
  set μ : Measure ℝ := volume.restrict (Ioc a b) with hμ_def
  haveI : IsFiniteMeasure μ := by
    rw [hμ_def]
    infer_instance
  -- `g` and `f` are integrable over `Ioc a b`.
  have hg_int : Integrable g μ := hg.1
  have hf_int : Integrable f μ := hf.1
  -- The integrand `H s θ = 𝟙[T](s, θ) · g s · f θ`.
  set H : ℝ → ℝ → ℝ := fun s θ => T.indicator (fun p : ℝ × ℝ => g p.1 * f p.2) (s, θ) with hH_def
  have h_uncurry_H : Function.uncurry H = T.indicator (fun p : ℝ × ℝ => g p.1 * f p.2) := by
    funext p; cases p with | mk s θ => simp [hH_def, Function.uncurry]
  -- `H` is integrable over `μ ×ₘ μ`: the product `g s · f θ` is integrable and the indicator
  -- restriction only shrinks the support.
  have h_prod_int : Integrable (fun p : ℝ × ℝ => g p.1 * f p.2) (μ.prod μ) :=
    hg_int.mul_prod hf_int
  have h_H_int : Integrable (Function.uncurry H) (μ.prod μ) := by
    rw [h_uncurry_H]; exact h_prod_int.indicator hT_meas
  -- Fubini swap.
  have h_swap := MeasureTheory.integral_integral_swap (f := H) h_H_int
  -- Inner integral with `s` outer, `θ` inner: gives `g s * ∫ θ in s..b, f θ` over `Ioc a b`.
  have h_inner_s : ∀ s ∈ Ioc a b, (∫ θ, H s θ ∂μ) = g s * (∫ θ in s..b, f θ) := by
    intro s hs
    have hsb : s ≤ b := le_trans hs.2 le_rfl
    -- The section `θ ↦ H s θ` equals the indicator of `Icc s b` of `θ ↦ g s * f θ`.
    have h_sect : (fun θ => H s θ) = (Icc s b).indicator (fun θ => g s * f θ) := by
      funext θ
      simp only [hH_def, Set.indicator, hT_def, mem_setOf_eq, mem_Icc]
      by_cases h_in : a ≤ s ∧ s ≤ θ ∧ θ ≤ b
      · simp [h_in]
      · have : ¬ (s ≤ θ ∧ θ ≤ b) := fun h => h_in ⟨hs.1.le, h.1, h.2⟩
        simp [this]
    rw [h_sect, hμ_def, setIntegral_indicator measurableSet_Icc]
    rw [show Ioc a b ∩ Icc s b = Icc s b by
      ext θ; simp only [mem_inter_iff, mem_Ioc, mem_Icc]
      exact ⟨fun h => h.2, fun h => ⟨⟨lt_of_lt_of_le hs.1 h.1, le_trans h.2 le_rfl⟩, h⟩⟩]
    rw [integral_const_mul, setIntegral_congr_set Ioc_ae_eq_Icc.symm,
      intervalIntegral.integral_of_le hsb]
  -- Inner integral with `θ` outer, `s` inner: gives `(∫ s in a..θ, g s) * f θ` over `Ioc a b`.
  have h_inner_θ : ∀ θ ∈ Ioc a b, (∫ s, H s θ ∂μ) = (∫ s in a..θ, g s) * f θ := by
    intro θ hθ
    have haθ : a ≤ θ := hθ.1.le
    -- The section `s ↦ H s θ` equals the indicator of `Icc a θ` of `s ↦ g s * f θ`.
    have h_sect : (fun s => H s θ) = (Icc a θ).indicator (fun s => g s * f θ) := by
      funext s
      simp only [hH_def, Set.indicator, hT_def, mem_setOf_eq, mem_Icc]
      by_cases h_in : a ≤ s ∧ s ≤ θ ∧ θ ≤ b
      · simp [h_in]
      · have h1 : ¬ (a ≤ s ∧ s ≤ θ) := fun h => h_in ⟨h.1, h.2, hθ.2⟩
        simp [h_in, h1]
    rw [h_sect, hμ_def, setIntegral_indicator measurableSet_Icc]
    rw [show Ioc a b ∩ Icc a θ = Ioc a θ by
      ext s; simp only [mem_inter_iff, mem_Ioc, mem_Icc]
      exact ⟨fun h => ⟨h.1.1, h.2.2⟩, fun h => ⟨⟨h.1, le_trans h.2 hθ.2⟩, ⟨h.1.le, h.2⟩⟩⟩]
    rw [integral_mul_const, intervalIntegral.integral_of_le haθ]
  -- Assemble: rewrite both iterated integrals via the section computations.
  have h_lhs_eq : (∫ θ, (∫ s, H s θ ∂μ) ∂μ) = ∫ θ in a..b, (∫ s in a..θ, g s) * f θ := by
    rw [intervalIntegral.integral_of_le hab, hμ_def]
    exact setIntegral_congr_fun measurableSet_Ioc h_inner_θ
  have h_rhs_eq : (∫ s, (∫ θ, H s θ ∂μ) ∂μ) = ∫ s in a..b, g s * (∫ θ in s..b, f θ) := by
    rw [intervalIntegral.integral_of_le hab, hμ_def]
    exact setIntegral_congr_fun measurableSet_Ioc h_inner_s
  rw [← h_lhs_eq, ← h_rhs_eq, h_swap]

/-- **Lebesgue × Stieltjes triangle swap.** For `u` monotone (right-continuous regularization
`u_sf = hu.stieltjesFunction`, Stieltjes measure `μ_u`) and `g` interval-integrable on `[a, b]`:

`∫ t in a..b, g t · (u_sf t − u_sf a) = ∫ s in Ioc a b, (∫ t in s..b, g t) ∂μ_u`.

The left side weights the cumulative Stieltjes increment `u_sf t − u_sf a = μ_u((a, t])` by `g`;
the right side integrates the tail integral of `g` against `μ_u`. Both are the integral of
`g t · 𝟙[a < s ≤ t ≤ b]` over the product `(volume × μ_u)`-triangle, in the two iteration orders. -/
theorem integral_triangle_swap_stieltjes {a b : ℝ} {u g : ℝ → ℝ}
    (hu : Monotone u) (hab : a < b) (hg : IntervalIntegrable g volume a b) :
    ∫ t in a..b, g t * (hu.stieltjesFunction t - hu.stieltjesFunction a)
      = ∫ s in Ioc a b, (∫ t in s..b, g t) ∂(hu.stieltjesFunction.measure) := by
  set u_sf := hu.stieltjesFunction with hu_sf
  set μ := hu.stieltjesFunction.measure with hμ
  have hμ_fin : μ (Ioc a b) ≠ ⊤ := by
    change u_sf.measure (Ioc a b) ≠ ⊤
    simp [StieltjesFunction.measure_Ioc, ENNReal.ofReal_ne_top]
  haveI : IsFiniteMeasure (μ.restrict (Ioc a b)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr hμ_fin⟩
  set f : ℝ → ℝ → ℝ := fun t s => (Ioc a t).indicator (fun _ => g t) s with hf_def
  have h_inner_t : ∀ t ∈ Ioc a b, ∫ s in Ioc a b, f t s ∂μ = g t * (u_sf t - u_sf a) := by
    intro t ht
    have hsubset : Ioc a t ∩ Ioc a b = Ioc a t := by
      rw [inter_eq_left]; exact Ioc_subset_Ioc_right ht.2
    rw [hf_def]
    simp only [integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
      hsubset, setIntegral_const, smul_eq_mul]
    rw [measureReal_def,
      show μ (Ioc a t) = ENNReal.ofReal (u_sf t - u_sf a) from u_sf.measure_Ioc a t,
      ENNReal.toReal_ofReal (sub_nonneg.mpr (u_sf.mono ht.1.le))]
    ring
  have h_inner_s : ∀ s ∈ Ioc a b, ∫ t in Ioc a b, f t s = ∫ t in s..b, g t := by
    intro s hs
    rw [hf_def]
    have heq : (Ioc a b).indicator (fun t => (Ioc a t).indicator (fun _ => g t) s)
        = (Ioc a b).indicator ((Ici s).indicator g) := by
      ext t
      by_cases htab : t ∈ Ioc a b
      · simp only [indicator_of_mem htab]
        by_cases hst : s ≤ t
        · rw [indicator_of_mem (show s ∈ Ioc a t from ⟨hs.1, hst⟩),
            indicator_of_mem (show t ∈ Ici s from hst)]
        · rw [indicator_of_notMem (show s ∉ Ioc a t from fun h => hst h.2),
            indicator_of_notMem (show t ∉ Ici s from hst)]
      · rw [indicator_of_notMem htab, indicator_of_notMem htab]
    rw [← integral_indicator measurableSet_Ioc, heq, integral_indicator measurableSet_Ioc]
    rw [integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
    have hinter : Ici s ∩ Ioc a b = Icc s b := by
      ext t; simp only [mem_inter_iff, mem_Ioc, mem_Ici, mem_Icc]
      exact ⟨fun ⟨hsx, _, hb⟩ => ⟨hsx, hb⟩,
        fun ⟨hsx, hb⟩ => ⟨hsx, lt_of_lt_of_le hs.1 hsx, hb⟩⟩
    rw [hinter, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs.2]
  have hg_oc : IntegrableOn g (Ioc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).mp hg
  have hgfst : Integrable (fun p : ℝ × ℝ => g p.1)
      ((volume.restrict (Ioc a b)).prod (μ.restrict (Ioc a b))) :=
    hg_oc.comp_fst (μ.restrict (Ioc a b))
  have hTmeas : MeasurableSet {p : ℝ × ℝ | a < p.2 ∧ p.2 ≤ p.1} :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst)
  have h_int : Integrable (Function.uncurry f)
      ((volume.restrict (Ioc a b)).prod (μ.restrict (Ioc a b))) := by
    refine (hgfst.indicator hTmeas).congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry, hf_def, Set.indicator_apply, mem_setOf_eq, mem_Ioc]
  have hswap := MeasureTheory.integral_integral_swap (μ := volume.restrict (Ioc a b))
    (ν := μ.restrict (Ioc a b)) h_int
  rw [intervalIntegral.integral_of_le hab.le]
  refine (setIntegral_congr_fun measurableSet_Ioc h_inner_t).symm.trans ?_
  refine hswap.trans (setIntegral_congr_fun measurableSet_Ioc h_inner_s)

end MeasureTheory

end
