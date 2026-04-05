import Mathlib

namespace AgreeToDisagree

open Set

variable {α Ω : Type*}

/-- We write `Partition α` for the type of partitions of a set `α`, implemented as a subtype
of `Set (Set α)`. Mathlib already equips this subtype with the order given by refinement (such that
`P ≤ Q` iff `P` refines `Q`) and proves that it is a complete lattice, i.e. that arbitrary infima
and suprema of partitions exist. -/
abbrev Partition (α : Type*) := Subtype (Setoid.IsPartition (α := α))

/-- When we write `s ∈ P` for a partition `P : Partition α`, we mean that `s` is a `Set α` that is
an element of the `Set (Set α)` underlying `P`. -/
@[reducible]
instance Partition.instSetLike : SetLike (Partition α) (Set α) where
  coe := Subtype.val
  coe_injective' := Subtype.val_injective

/-- As expected, a partition `P` refines a partition `Q` iff every set in `P` is contained in
a set in `Q`. -/
lemma Partition.le_iff {P Q : Partition α} : P ≤ Q ↔ ∀ s ∈ P, ∃ t ∈ Q, s ⊆ t := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · intro s hs
    have ⟨a, ha⟩ := Setoid.nonempty_of_mem_partition P.2 hs
    refine ⟨{b | Setoid.mkClasses _ Q.2.2 b a}, ?_, ?_⟩
    · have := Setoid.mem_classes (Setoid.mkClasses _ Q.2.2) a
      rwa [Setoid.classes_mkClasses Q.1 Q.2] at this
    · refine fun b hb ↦ h fun s' hs' hbs' ↦ ?_
      rwa [← P.2.pairwiseDisjoint.elim hs hs' <| not_disjoint_iff.2 ⟨b, hb, hbs'⟩]
  · intro a b hab s hs has
    have ⟨t, ⟨ht, hat⟩, _⟩ := P.2.2 a
    have ⟨s', hs'⟩ := h t ht
    rw [Q.2.pairwiseDisjoint.elim hs hs'.1 <| not_disjoint_iff.2 ⟨a, has, hs'.2 hat⟩]
    exact hs'.2 <| hab t ht hat

/-- We call a partition of a measurable space measurable if it consists of measurable sets. -/
protected def Partition.Measurable [MeasurableSpace Ω] (P : Partition Ω) :=
  ∀ s ∈ P, MeasurableSet s

/-- If a countable partition is measurable, every partition it refines is measurable too.
Note that the countability assumption is necessary because e.g. the partition into singletons is
usually measurable but refines all other partitions, even nonmeasurable ones. -/
lemma Partition.Measurable.mono [MeasurableSpace Ω] {P Q : Partition Ω}
    (hP : P.Measurable) (hP' : P.val.Countable) (hQ : P ≤ Q) : Q.Measurable := by
  intro s hs
  rw [← inter_univ s, ← P.2.sUnion_eq_univ, sUnion_eq_iUnion, inter_iUnion]
  have := hP'.to_subtype
  refine MeasurableSet.iUnion fun t ↦ ?_
  have ⟨s', hs'⟩ := le_iff.1 hQ _ t.2
  obtain h | h := Q.2.pairwiseDisjoint.eq_or_disjoint hs hs'.1
  · rw [h, inter_eq_right.2 hs'.2]
    exact hP _ t.2
  · suffices s ∩ t ⊆ ∅ by simp_all
    exact (inter_subset_inter_right s hs'.2).trans <| Set.disjoint_iff.1 h

/-- The supremum of two measurable partitions is measurable if at least one of the two partitions
is countable. -/
lemma Partition.Measurable.sup [MeasurableSpace Ω] {P Q : Partition Ω}
    (hP : P.Measurable) (hQ : Q.Measurable) (h : P.val.Countable ∨ Q.val.Countable) :
    (P ⊔ Q).Measurable := by
  obtain h | h := h
  · exact hP.mono h le_sup_left
  · exact hQ.mono h le_sup_right

open MeasureTheory

open scoped ProbabilityTheory

-- todo
lemma agreeToDisagree [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (P₁ P₂ : Partition Ω) (hP₁ : P₁.Measurable) (hP₂ : P₂.Measurable) (h : (P₁ ⊔ P₂).Measurable)
    (h : ∀ s ∈ P₁ ⊔ P₂, ℙ s > 0) :
    (sorry : Prop) := by sorry

end AgreeToDisagree
