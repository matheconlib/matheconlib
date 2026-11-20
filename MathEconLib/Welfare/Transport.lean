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
For a feasible action set `C` and an outcome map `f`, compare outcomes on the attainable set
`f '' C`. If feasibility is given on outcomes instead, use its preimage and check that each
feasible outcome is attainable.
-/

@[expose] public section

namespace MathEconLib.Welfare

open Preferences

variable {I J X Y : Type*} {R : I → Preference X} {F S : Set X} {x : X}

/-- Pareto efficiency persists on a smaller feasible set containing the candidate. -/
theorem IsParetoEfficient.mono (hx : IsParetoEfficient R F x) (hSF : S ⊆ F) (hxs : x ∈ S) :
    IsParetoEfficient R S x := by
  let := (unanimousPreference R).toPreorder
  exact Maximal.mono hx hSF hxs

/-- Weak Pareto efficiency persists on a smaller feasible set containing the candidate. -/
theorem IsWeaklyParetoEfficient.mono (hx : IsWeaklyParetoEfficient R F x) (hSF : S ⊆ F)
    (hxs : x ∈ S) : IsWeaklyParetoEfficient R S x :=
  ⟨hxs, fun y hy ↦ hx.2 y (hSF hy)⟩

variable (R)

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

/-- An efficient action is feasible and yields an efficient outcome among those attainable from
`C`. Feasibility of the action matters when several actions give the same outcome. -/
theorem isParetoEfficient_comap_image_iff (f : Y → X) (C : Set Y) (a : Y) :
    IsParetoEfficient (fun i ↦ (R i).comap f) C a ↔
      a ∈ C ∧ IsParetoEfficient R (f '' C) (f a) := by
  let := (unanimousPreference R).toPreorder
  let := (unanimousPreference (fun i ↦ (R i).comap f)).toPreorder
  refine (and_iff_right_of_imp (fun h ↦ h.1)).symm.trans (and_congr_right fun ha ↦ ?_)
  exact (maximal_mem_image_monotone_iff (f := f) ha (fun {_ _} _ _ ↦ Iff.rfl)).symm

/-- A weakly efficient action is feasible and yields a weakly efficient attainable outcome. -/
theorem isWeaklyParetoEfficient_comap_image_iff (f : Y → X) (C : Set Y) (a : Y) :
    IsWeaklyParetoEfficient (fun i ↦ (R i).comap f) C a ↔
      a ∈ C ∧ IsWeaklyParetoEfficient R (f '' C) (f a) := by
  rw [isWeaklyParetoEfficient_iff, isWeaklyParetoEfficient_iff, Set.forall_mem_image]
  exact ⟨fun h ↦ ⟨h.1, Set.mem_image_of_mem f h.1, h.2⟩, fun h ↦ ⟨h.1, h.2.2⟩⟩

/-- An outcome map preserves and reflects Pareto efficiency if it covers the feasible set. -/
theorem isParetoEfficient_comap_iff (f : Y → X) (hF : F ⊆ Set.range f) {y : Y} :
    IsParetoEfficient (fun i ↦ (R i).comap f) (f ⁻¹' F) y ↔ IsParetoEfficient R F (f y) := by
  rw [isParetoEfficient_comap_image_iff, Set.image_preimage_eq_of_subset hF]
  exact and_iff_right_of_imp fun h ↦ h.1

/-- An outcome map preserves and reflects weak Pareto efficiency if it covers the feasible set. -/
theorem isWeaklyParetoEfficient_comap_iff (f : Y → X) (hF : F ⊆ Set.range f) {y : Y} :
    IsWeaklyParetoEfficient (fun i ↦ (R i).comap f) (f ⁻¹' F) y ↔
      IsWeaklyParetoEfficient R F (f y) := by
  rw [isWeaklyParetoEfficient_comap_image_iff, Set.image_preimage_eq_of_subset hF]
  exact and_iff_right_of_imp fun h ↦ h.1

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
