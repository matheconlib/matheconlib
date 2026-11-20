/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.Welfare.Pareto
public import Mathlib.Data.Set.Image

/-!
# Transport of Pareto efficiency

Reindexing the agents preserves both efficiency criteria when every agent is represented.
To compare two descriptions of the outcomes, pull preferences back along the outcome map
and take the preimage of the feasible set. Every feasible outcome must have a representative.
-/

@[expose] public section

namespace MathEconLib.Welfare

open Preferences

variable {I J X Y : Type*} (R : I → Preference X) {F : Set X} {x : X}

/-- Reindexing preserves Pareto efficiency when every agent occurs in the new index. -/
theorem isParetoEfficient_reindex_iff {r : J → I} (hr : Function.Surjective r) :
    IsParetoEfficient (R ∘ r) F x ↔ IsParetoEfficient R F x := by
  rw [isParetoEfficient_iff, isParetoEfficient_iff]
  exact and_congr_right' <| forall₂_congr fun y _ ↦ not_congr <|
    and_congr (hr.forall (p := fun i ↦ (R i).le x y)).symm
      (hr.exists (p := fun i ↦ (R i).lt x y)).symm

/-- Reindexing preserves weak Pareto efficiency when every agent occurs in the new index. -/
theorem isWeaklyParetoEfficient_reindex_iff {r : J → I} (hr : Function.Surjective r) :
    IsWeaklyParetoEfficient (R ∘ r) F x ↔ IsWeaklyParetoEfficient R F x :=
  and_congr_right' <| forall₂_congr fun y _ ↦
    not_congr (hr.forall (p := fun i ↦ (R i).lt x y)).symm

private theorem forall_mem_preimage_iff {f : Y → X} (hF : F ⊆ Set.range f) (p : X → Prop) :
    (∀ y ∈ f ⁻¹' F, p (f y)) ↔ ∀ x ∈ F, p x := by
  calc
    _ ↔ ∀ x ∈ f '' (f ⁻¹' F), p x := Set.forall_mem_image.symm
    _ ↔ _ := by rw [Set.image_preimage_eq_of_subset hF]

/-- An outcome map preserves and reflects Pareto efficiency if it covers the feasible set. -/
theorem isParetoEfficient_comap_iff (f : Y → X) (hF : F ⊆ Set.range f) {y : Y} :
    IsParetoEfficient (fun i ↦ (R i).comap f) (f ⁻¹' F) y ↔ IsParetoEfficient R F (f y) := by
  rw [isParetoEfficient_iff, isParetoEfficient_iff]
  exact and_congr_right' <| forall_mem_preimage_iff hF fun x ↦ ¬ ParetoImprovement R (f y) x

/-- An outcome map preserves and reflects weak Pareto efficiency if it covers the feasible set. -/
theorem isWeaklyParetoEfficient_comap_iff (f : Y → X) (hF : F ⊆ Set.range f) {y : Y} :
    IsWeaklyParetoEfficient (fun i ↦ (R i).comap f) (f ⁻¹' F) y ↔
      IsWeaklyParetoEfficient R F (f y) :=
  and_congr_right' <| forall_mem_preimage_iff hF fun x ↦ ¬ UnanimousStrictImprovement R (f y) x

variable (F)

/-- A feasible outcome can equivalently be tested for Pareto efficiency on the subtype `F`. -/
theorem isParetoEfficient_subtype_iff (x : F) :
    IsParetoEfficient (fun i ↦ (R i).comap Subtype.val) Set.univ x ↔ IsParetoEfficient R F ↑x := by
  simpa only [Subtype.coe_preimage_self] using
    isParetoEfficient_comap_iff R Subtype.val (fun z hz ↦ ⟨⟨z, hz⟩, rfl⟩) (y := x)

/-- Weak Pareto efficiency on the feasible subtype agrees with weak Pareto efficiency in `F`. -/
theorem isWeaklyParetoEfficient_subtype_iff (x : F) :
    IsWeaklyParetoEfficient (fun i ↦ (R i).comap Subtype.val) Set.univ x ↔
      IsWeaklyParetoEfficient R F ↑x := by
  simpa only [Subtype.coe_preimage_self] using
    isWeaklyParetoEfficient_comap_iff R Subtype.val (fun z hz ↦ ⟨⟨z, hz⟩, rfl⟩) (y := x)

end MathEconLib.Welfare
