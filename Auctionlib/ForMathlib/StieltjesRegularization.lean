/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Stieltjes

/-!
# Stieltjes regularization of monotone functions

Auxiliary facts about the right-continuous Stieltjes regularization of a monotone real function.
-/

@[expose] public section

open MeasureTheory Set Filter Function
open scoped Topology Real

namespace Monotone

/-- A monotone function constant on an open interval assigns that interval zero Stieltjes mass. -/
lemma stieltjesFunction_measure_Ioo_eq_zero {f : ℝ → ℝ} (hf : Monotone f) {p r k : ℝ}
    (hpr : p < r) (hconst : ∀ x ∈ Ioo p r, f x = k) :
    hf.stieltjesFunction.measure (Ioo p r) = 0 := by
  set sf := hf.stieltjesFunction with hsf
  have hsf_eq : ∀ y ∈ Ico p r, sf y = k := by
    intro y hy
    rw [hsf, Monotone.stieltjesFunction_eq]
    refine rightLim_eq_of_tendsto (nhdsWithin_Ioi_neBot le_rfl).ne ?_
    have hev : ∀ᶠ z in nhdsWithin y (Ioi y), f z = k := by
      filter_upwards [Ioo_mem_nhdsGT hy.2] with z hz
      exact hconst z ⟨lt_of_le_of_lt hy.1 hz.1, hz.2⟩
    exact (tendsto_congr' hev).mpr tendsto_const_nhds
  have hsfp : sf p = k := hsf_eq p ⟨le_rfl, hpr⟩
  have hleftLim : leftLim (⇑sf) r = k := by
    refine leftLim_eq_of_tendsto (nhdsWithin_Iio_neBot le_rfl).ne ?_
    have hev : ∀ᶠ z in nhdsWithin r (Iio r), sf z = k := by
      filter_upwards [Ioo_mem_nhdsLT hpr] with z hz
      exact hsf_eq z ⟨hz.1.le, hz.2⟩
    exact (tendsto_congr' hev).mpr tendsto_const_nhds
  change sf.measure (Ioo p r) = 0
  rw [StieltjesFunction.measure_Ioo, hleftLim, hsfp, sub_self, ENNReal.ofReal_zero]

/-- A monotone function agrees Lebesgue-a.e. with its right-continuous regularization. -/
lemma stieltjesFunction_ae_eq {f : ℝ → ℝ} (hf : Monotone f) :
    ⇑hf.stieltjesFunction =ᵐ[volume] f := by
  have hD : volume {x | ¬ContinuousAt f x} = 0 :=
    hf.countable_not_continuousAt.measure_zero volume
  filter_upwards [compl_mem_ae_iff.mpr hD] with x hx
  have hcont : ContinuousAt f x := not_not.mp hx
  rw [Monotone.stieltjesFunction_eq]
  exact hcont.continuousWithinAt.rightLim_eq

end Monotone
