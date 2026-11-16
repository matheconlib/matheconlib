/-
Copyright (c) 2026 Ben Eltschig, Jujian Zhang, Ruiz Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig, Jujian Zhang, Ruiz Chen
-/
module

public import Mathlib.Order.Setoid.Partition

/-!
# Parts of a partition and refinement

Mathlib's `Setoid.Partitions α` is the type of partitions of `α` into nonempty sets. It is
ordered by refinement, so `P ≤ Q` means that `P` refines `Q`, and it is a complete lattice.
This file makes the parts of a partition available through `SetLike`, so that `s ∈ P` says that
`s` is a part of `P`, and names the part containing a given point.

## Main definitions

* `Setoid.Partitions.part`: the part of a partition that contains a given point.

## Main statements

* `Setoid.Partitions.le_iff_forall_exists_subset`: `P` refines `Q` exactly when every part of
  `P` lies in some part of `Q`.
* `Setoid.Partitions.part_orderIso`: in the partition into the classes of an equivalence
  relation, the part of a point is its class.
* `Setoid.Partitions.part_mono`: refining a partition shrinks the part of every point.
* `Setoid.Partitions.part_eq_biUnion_of_le`: a part of a coarser partition is the union of the
  parts of a finer partition that it contains.

## Provenance

Adapted from the `AgreeToDisagree` Lean development
(<https://github.com/AxiomMath/AgreeToDisagree>), Copyright (c) 2026 Axiom Math, released under
the MIT License; its notice is reproduced in `docs/licenses/AgreeToDisagree-MIT.txt`.
-/

@[expose] public section

namespace Setoid.Partitions

variable {α : Type*}

/-- The parts of a partition, so that `s ∈ P` means that `s` is a part of `P`. -/
instance : SetLike (Partitions α) (Set α) where
  coe := Partitions.toSet
  coe_injective := Subtype.val_injective

variable {P Q : Partitions α} {s : Set α} {a b : α}

@[simp]
lemma mem_toSet : s ∈ P.toSet ↔ s ∈ P := Iff.rfl

/-- `P` refines `Q` exactly when every part of `P` lies in some part of `Q`. -/
lemma le_iff_forall_exists_subset : P ≤ Q ↔ ∀ s ∈ P, ∃ t ∈ Q, s ⊆ t := by
  refine ⟨fun h s hs ↦ ?_, fun h a b hab s hs has ↦ ?_⟩
  · obtain ⟨a, ha⟩ := nonempty_of_mem_partition P.isPartition hs
    refine ⟨{b | mkClasses _ Q.isPartition.2 b a}, ?_, fun b hb ↦ h fun s' hs' hbs' ↦ ?_⟩
    · have := mem_classes (mkClasses _ Q.isPartition.2) a
      rwa [classes_mkClasses _ Q.isPartition] at this
    · rwa [← P.isPartition.pairwiseDisjoint.elim hs hs' <| Set.not_disjoint_iff.2 ⟨b, hb, hbs'⟩]
  · obtain ⟨t, ⟨ht, hat⟩, -⟩ := P.isPartition.2 a
    obtain ⟨s', hs', hts'⟩ := h t ht
    rw [Q.isPartition.pairwiseDisjoint.elim hs hs' <| Set.not_disjoint_iff.2 ⟨a, has, hts' hat⟩]
    exact hts' <| hab t ht hat

/-- The part of the partition `P` that contains `a`. -/
protected def part (P : Partitions α) (a : α) : Set α :=
  {b | mkClasses P.toSet P.isPartition.2 b a}

lemma mem_part_self (P : Partitions α) (a : α) : a ∈ P.part a :=
  (mkClasses P.toSet P.isPartition.2).refl a

lemma part_mem (P : Partitions α) (a : α) : P.part a ∈ P := by
  rw [← mem_toSet, ← classes_mkClasses P.toSet P.isPartition]
  exact (mkClasses P.toSet P.isPartition.2).mem_classes a

/-- The part of a point is the unique part that contains it. -/
lemma part_eq_of_mem (hs : s ∈ P) (ha : a ∈ s) : P.part a = s :=
  (eq_eqv_class_of_mem P.isPartition.2 hs ha).symm

lemma part_eq_iff_mem (hs : s ∈ P) : P.part a = s ↔ a ∈ s :=
  ⟨fun h ↦ h ▸ P.mem_part_self a, part_eq_of_mem hs⟩

lemma mem_part_iff_part_eq_part : a ∈ P.part b ↔ P.part a = P.part b :=
  (part_eq_iff_mem (P.part_mem b)).symm

/-- In the partition into the classes of an equivalence relation, the part of a point is its
equivalence class. -/
lemma part_orderIso (r : Setoid α) (a : α) : (Partition.orderIso α r).part a = {b | r b a} :=
  part_eq_of_mem (r.mem_classes a) (r.refl a)

/-- Refining a partition shrinks the part of every point. -/
lemma part_mono (h : P ≤ Q) (a : α) : P.part a ⊆ Q.part a :=
  fun _ hb ↦ h hb

/-- A part of a coarser partition is the union of the parts of a finer partition that it
contains. -/
lemma part_eq_biUnion_of_le (h : P ≤ Q) (a : α) :
    Q.part a = ⋃ s ∈ {s ∈ P | s ⊆ Q.part a}, s := by
  ext b
  refine ⟨fun hb ↦ ?_, fun hb ↦ ?_⟩
  · exact Set.mem_biUnion
      ⟨P.part_mem b, (part_mono h b).trans_eq (mem_part_iff_part_eq_part.1 hb)⟩
      (P.mem_part_self b)
  · obtain ⟨s, hs, hbs⟩ := Set.mem_iUnion₂.1 hb
    exact hs.2 hbs

end Setoid.Partitions
