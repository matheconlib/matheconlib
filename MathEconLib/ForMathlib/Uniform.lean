/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Data.Fintype.Pi
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Uniform finite expectations

Integrating a real-valued function under the uniform PMF on a nonempty finite discrete space
agrees with Mathlib's finite average. Uniform laws transport along equivalences, and a uniform
law on a finite product is the product of its uniform coordinate laws. Applications supply their
own carriers, statistics, and outcome rules.
-/

@[expose] public section

open scoped BigOperators
open MeasureTheory

namespace PMF

/-- Uniform mass on a nonempty finite type, using Mathlib's finite PMF constructor.
Mathlib's `Measure.uniformOfFinset` supplies the corresponding measure. -/
noncomputable def uniformFintype (α : Type*) [Fintype α] [Nonempty α] : PMF α :=
  ofFintype (fun _ ↦ (Fintype.card α : ℝ≥0∞)⁻¹) (by simp)

@[simp] theorem uniformFintype_apply {α : Type*} [Fintype α] [Nonempty α] (a : α) :
    uniformFintype α a = (Fintype.card α : ℝ≥0∞)⁻¹ := rfl

/-- The finite uniform PMF agrees with Mathlib's uniform measure on the full finite set. -/
theorem toMeasure_uniformFintype {α : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] :
    (uniformFintype α).toMeasure = Measure.uniformOfFinset (Finset.univ : Finset α) := by
  classical
  apply Measure.ext_of_singleton
  intro a
  simp [PMF.toMeasure_apply_singleton]

/-- A bijective change of representation preserves the uniform law on a finite space. -/
theorem map_uniformOfFintype {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (e : α ≃ β) :
    (uniformFintype α).map e = uniformFintype β := by
  classical
  ext b
  rw [map_apply, ← e.symm.tsum_eq]
  simp [Fintype.card_congr e]

/-- Uniform sampling of a finite family of finite coordinates has their product law,
including the empty product. -/
theorem toMeasure_uniformOfFintype_pi {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)] [∀ i, MeasurableSpace (α i)]
    [∀ i, MeasurableSingletonClass (α i)] :
    (uniformFintype (∀ i, α i)).toMeasure =
      Measure.pi (fun i ↦ (uniformFintype (α i)).toMeasure) := by
  classical
  refine Measure.ext_of_singleton fun f ↦ ?_
  rw [toMeasure_apply_singleton _ _ (measurableSet_singleton f), Measure.pi_singleton]
  simp only [toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    uniformFintype_apply, Fintype.card_pi, Nat.cast_prod]
  exact ENNReal.prod_inv_distrib fun _ _ _ _ _ ↦ Or.inr (by simp)

/-- A uniform finite expectation is the ordinary average over the outcome space. -/
theorem integral_uniformOfFintype {α : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (f : α → ℝ) :
    (∫ a, f a ∂(uniformFintype α).toMeasure) = 𝔼 a, f a := by
  rw [integral_eq_sum, Fintype.expect_eq_sum_div_card]
  simp only [uniformFintype_apply, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, smul_eq_mul, div_eq_inv_mul, Finset.mul_sum]

end PMF
