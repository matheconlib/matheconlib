/-
Copyright (c) 2026 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
Some general results on measurability, integrals etc.
-/

open MeasureTheory

@[expose] public section

@[fun_prop]
lemma Continuous.integrable {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] {μ : Measure α} [IsFiniteMeasureOnCompacts μ] [CompactSpace α]
    {E : Type*} [NormedAddCommGroup E] {f : α → E} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport <| .of_compactSpace _

@[simps!]
def MeasurableEquiv.piSplitAt {ι : Type*} [DecidableEq ι] (i : ι) (α : ι → Type*)
    [∀ i, MeasurableSpace (α i)] :
    ((i : ι) → α i) ≃ᵐ α i × ((j : {j : ι // j ≠ i}) → α j) where
  toEquiv := .piSplitAt i α
  measurable_toFun := by
    dsimp [Equiv.piSplitAt]
    fun_prop
  measurable_invFun := measurable_pi_iff.2 fun i ↦ by
    dsimp [Equiv.piSplitAt]
    split_ifs with h
    · subst h
      fun_prop
    · fun_prop

lemma MeasurableEquiv.piSplitAt_eq_piCongrLeft_trans_piOptionEquivProd
    {ι : Type*} [DecidableEq ι] (i : ι) (α : ι → Type*)
    [∀ i, MeasurableSpace (α i)] :
    piSplitAt i α =
    ((piCongrLeft _ (Equiv.optionSubtypeNe i)).symm.trans <|
      (piOptionEquivProd _).trans prodComm) := by
  ext <;> rfl

@[simp]
lemma MeasurableEquiv.map_trans {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {μ : Measure α} (e : α ≃ᵐ β) (e' : β ≃ᵐ γ) :
    μ.map (e.trans e') = (μ.map e).map e' :=
  (μ.map_map e'.measurable e.measurable).symm

@[simp]
lemma MeasurableEquiv.prodComm_symm {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] :
    (MeasurableEquiv.prodComm (α := α) (β := β)).symm = MeasurableEquiv.prodComm :=
  rfl

@[simp]
lemma MeasurableEquiv.prodComm_prod {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν] :
    (μ.prod ν).map MeasurableEquiv.prodComm = (ν.prod μ) :=
  Measure.prod_swap

lemma MeasureTheory.Measure.pi_map_piSplitAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, MeasurableSpace (α i)] (i : ι)
    (μ : (i : ι) → Measure (α i)) [∀ i, SigmaFinite (μ i)] :
    ((μ i).prod (Measure.pi fun i ↦ μ i.1)).map
      (MeasurableEquiv.piSplitAt i α).symm = Measure.pi μ := by
  rw [MeasurableEquiv.piSplitAt_eq_piCongrLeft_trans_piOptionEquivProd]
  erw [MeasurableEquiv.trans_symm, MeasurableEquiv.symm_symm, MeasurableEquiv.trans_symm,
    MeasurableEquiv.map_trans, MeasurableEquiv.map_trans, MeasurableEquiv.prodComm_symm,
    MeasurableEquiv.prodComm_prod (μ := μ i) (ν := Measure.pi fun j : {j // j ≠ i} ↦ μ j)]
  refine .trans (congr_arg _ ?_) <| Measure.pi_map_piCongrLeft _ _
  exact Measure.pi_map_piOptionEquivProd fun b ↦ μ ((Equiv.optionSubtypeNe i) b)

end
