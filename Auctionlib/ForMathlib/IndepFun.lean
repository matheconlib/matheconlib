/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Notation

/-!
# Fubini via independence

A helper for swapping an integrand against an independent "copy" of one of its arguments: If
`X ⫫ Y` are independent random variables and `h(X ω, Y ω)` is integrable, then
`∫ ω, h (X ω) (Y ω) ∂ℙ = ∫ ω, ∫ ω', h (X ω) (Y ω') ∂ℙ ∂ℙ`.

Proof combines:

* `indepFun_iff_map_prod_eq_prod_map_map`: The joint law equals the product of marginal laws for
  independent random variables;
* `MeasureTheory.integral_prod`: Fubini on product measures;
* `integral_map`: Change of variables under the pushforward.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- The iterated integral obtained by replacing the second argument with an independent copy is
integrable whenever the original independent pairing is integrable. -/
lemma MeasureTheory.integrable_integral_indep_swap
    {α γ : Type*} [MeasurableSpace α] [MeasurableSpace γ]
    {X : Ω → α} {Y : Ω → γ} (hXY : IndepFun X Y ℙ)
    (hX : Measurable X) (hY : Measurable Y)
    (h : α → γ → ℝ) (hh : Measurable h.uncurry)
    (hint : Integrable (fun ω => h (X ω) (Y ω)) ℙ) :
    Integrable (fun ω => ∫ ω', h (X ω) (Y ω') ∂ℙ) ℙ := by
  have hmap : Measure.map (fun ω => (X ω, Y ω)) ℙ =
      (Measure.map X ℙ).prod (Measure.map Y ℙ) :=
    (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).1 hXY
  have hint_prod : Integrable h.uncurry
      ((Measure.map X ℙ).prod (Measure.map Y ℙ)) := by
    rw [← hmap]
    exact (integrable_map_measure hh.aestronglyMeasurable
      (hX.prodMk hY).aemeasurable).2 hint
  have houter_map : Integrable
      (fun x => ∫ y, h x y ∂(Measure.map Y ℙ)) (Measure.map X ℙ) :=
    hint_prod.integral_prod_left
  have houter : Integrable
      (fun ω => ∫ y, h (X ω) y ∂(Measure.map Y ℙ)) ℙ :=
    (integrable_map_measure houter_map.aestronglyMeasurable hX.aemeasurable).1 houter_map
  refine houter.congr (Filter.Eventually.of_forall fun ω => ?_)
  exact integral_map hY.aemeasurable
    (hh.of_uncurry_left.aestronglyMeasurable (μ := Measure.map Y ℙ))

/-- **Fubini via independence.** For independent random variables `X ⫫ Y`, the integral of
`h(X ω, Y ω)` equals the iterated integral where the `Y` argument ranges over an independent
copy. -/
lemma MeasureTheory.integral_indep_swap
    {α γ : Type*} [MeasurableSpace α] [MeasurableSpace γ]
    {X : Ω → α} {Y : Ω → γ} (hXY : IndepFun X Y ℙ)
    (hX : Measurable X) (hY : Measurable Y)
    (h : α → γ → ℝ) (hh : Measurable h.uncurry)
    (hint : Integrable (fun ω => h (X ω) (Y ω)) ℙ) :
    ∫ ω, h (X ω) (Y ω) ∂ℙ = ∫ ω, ∫ ω', h (X ω) (Y ω') ∂ℙ ∂ℙ := by
  have hmap : Measure.map (fun ω => (X ω, Y ω)) ℙ =
      (Measure.map X ℙ).prod (Measure.map Y ℙ) :=
    (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).1 hXY
  have hint_prod : Integrable h.uncurry
      ((Measure.map X ℙ).prod (Measure.map Y ℙ)) := by
    rw [← hmap]
    exact (integrable_map_measure hh.aestronglyMeasurable
      (hX.prodMk hY).aemeasurable).2 hint
  calc ∫ ω, h (X ω) (Y ω) ∂ℙ
      = ∫ z, h.uncurry z ∂(Measure.map (fun ω => (X ω, Y ω)) ℙ) := by
        rw [integral_map (hX.prodMk hY).aemeasurable hh.aestronglyMeasurable]; rfl
    _ = ∫ z, h.uncurry z ∂((Measure.map X ℙ).prod (Measure.map Y ℙ)) := by rw [hmap]
    _ = ∫ x, ∫ y, h x y ∂(Measure.map Y ℙ) ∂(Measure.map X ℙ) :=
        MeasureTheory.integral_prod _ hint_prod
    _ = ∫ ω, ∫ y, h (X ω) y ∂(Measure.map Y ℙ) ∂ℙ := by
        rw [integral_map hX.aemeasurable]
        exact (MeasureTheory.Integrable.integral_prod_left hint_prod).aestronglyMeasurable
    _ = ∫ ω, ∫ ω', h (X ω) (Y ω') ∂ℙ ∂ℙ := by
        congr 1 with ω
        rw [integral_map hY.aemeasurable (hh.of_uncurry_left).aestronglyMeasurable]

end
