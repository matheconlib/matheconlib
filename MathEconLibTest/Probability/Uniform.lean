/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
import MathEconLib

/-!
Public API pins and examples linking uniform PMF integrals, finite distributions, and finite
averages.
-/

namespace MathEconLibTest.Probability.Uniform

open MathEconLib.Probability MeasureTheory
open scoped BigOperators

section APIPins

noncomputable example : ∀ (α : Type*) [Fintype α] [Nonempty α], PMF α :=
  @PMF.uniformFintype

example : ∀ {α : Type*} [Fintype α] [Nonempty α] (a : α),
    PMF.uniformFintype α a = (Fintype.card α : ENNReal)⁻¹ :=
  @PMF.uniformFintype_apply

example : ∀ {α : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α]
    [MeasurableSingletonClass α],
    (PMF.uniformFintype α).toMeasure = Measure.uniformOfFinset (Finset.univ : Finset α) :=
  @PMF.toMeasure_uniformFintype

example : ∀ {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β] (e : α ≃ β),
    (PMF.uniformFintype α).map e = PMF.uniformFintype β :=
  @PMF.map_uniformOfFintype

example : ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)] (f : ∀ i, α i),
    PMF.uniformFintype (∀ i, α i) f = ∏ i, PMF.uniformFintype (α i) (f i) :=
  @PMF.uniformFintype_pi_apply

example : ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)] [∀ i, MeasurableSpace (α i)]
    [∀ i, MeasurableSingletonClass (α i)],
    (PMF.uniformFintype (∀ i, α i)).toMeasure =
      Measure.pi (fun i ↦ (PMF.uniformFintype (α i)).toMeasure) :=
  @PMF.toMeasure_uniformOfFintype_pi

example : ∀ {α : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (f : α → ℝ),
    (∫ a, f a ∂(PMF.uniformFintype α).toMeasure) = 𝔼 a, f a :=
  @PMF.integral_uniformOfFintype

example : ∀ {α : Type*} [Fintype α] [Nonempty α],
    (FinDist.uniform (α := α)).toPMF = PMF.uniformFintype α :=
  @FinDist.toPMF_uniform

example : ∀ {α : Type*} [Fintype α] [Nonempty α] (f : α → ℝ),
    (FinDist.uniform (α := α)).expect f = 𝔼 a, f a :=
  @FinDist.expect_uniform

end APIPins

example {α : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (f : α → ℝ) :
    (∫ a, f a ∂(PMF.uniformFintype α).toMeasure) =
      (FinDist.uniform (α := α)).expect f := by
  rw [PMF.integral_uniformOfFintype, FinDist.expect_uniform]

example {α : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α] :
    (FinDist.uniform (α := α)).toMeasure = (PMF.uniformFintype α).toMeasure := by
  simp [FinDist.toMeasure]

-- A payoff statistic on three outcomes uses the same finite-average identity as matching.
example : (FinDist.uniform (α := Fin 3)).expect (fun i ↦ (i.val + 1 : ℝ)) = 2 := by
  rw [FinDist.expect_uniform, Fintype.expect_eq_sum_div_card]
  norm_num [Fin.sum_univ_succ]

-- A nonmatching application: relabeling three possible outcomes preserves their uniform law.
example : (PMF.uniformFintype (Fin 3)).map (Equiv.swap 0 1) =
    PMF.uniformFintype (Fin 3) := PMF.map_uniformOfFintype (Equiv.swap 0 1)

section BinarySignals

local instance : MeasurableSpace Bool := ⊤

-- Three binary signals and the empty family use the same product-law lemma as rankings.
example : (PMF.uniformFintype (Fin 3 → Bool)).toMeasure =
    Measure.pi (fun _ : Fin 3 ↦ (PMF.uniformFintype Bool).toMeasure) :=
  PMF.toMeasure_uniformOfFintype_pi

example : (PMF.uniformFintype (Fin 0 → Bool)).toMeasure =
    Measure.pi (fun _ : Fin 0 ↦ (PMF.uniformFintype Bool).toMeasure) :=
  PMF.toMeasure_uniformOfFintype_pi

end BinarySignals

#print axioms PMF.integral_uniformOfFintype
#print axioms PMF.map_uniformOfFintype
#print axioms PMF.toMeasure_uniformOfFintype_pi
#print axioms MathEconLib.Probability.FinDist.expect_uniform
#print axioms MathEconLib.Probability.FinDist.toPMF_uniform

end MathEconLibTest.Probability.Uniform
