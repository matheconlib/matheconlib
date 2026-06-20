import Mathlib.Data.Setoid.Partition
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

open Set

variable {α Ω : Type*}

namespace Setoid

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

/-- `P.class a` is the element of a partition `P : Partition α` that contains `a : α`. -/
protected def Partition.class (P : Partition α) (a : α) : Set α :=
  {b | Setoid.mkClasses P.1 P.2.2 b a}

lemma Partition.mem_class (P : Partition α) (a : α) : a ∈ P.class a :=
  (Setoid.mkClasses P.1 P.2.2).2.refl _

lemma Partition.class_mem (P : Partition α) (a : α) : P.class a ∈ P :=
  (Setoid.classes_mkClasses P.1 P.2 ▸ (Setoid.mkClasses P.1 P.2.2).mem_classes a:)

lemma Partition.Measurable.measurableSet_class [MeasurableSpace Ω] {P : Partition Ω}
    (hP : P.Measurable) (ω : Ω) : MeasurableSet (P.class ω) :=
  hP _ (P.class_mem ω)

lemma Partition.class_mono {P Q : Partition α} (h : P ≤ Q) (a : α) :
    P.class a ⊆ Q.class a :=
  fun x ↦ @h x a

lemma Partition.class_eq_class_of_mem {P : Partition α} {a a' : α} (h : a' ∈ P.class a) :
    P.class a' = P.class a :=
  (Setoid.eq_eqv_class_of_mem P.2.2 (P.class_mem a) h).symm

lemma Partition.class_eq_of_mem {P : Partition α} {s : Set α} {a : α}
    (hs : s ∈ P) (ha : a ∈ s) : P.class a = s :=
  (Setoid.eq_eqv_class_of_mem P.2.2 hs ha).symm

lemma Partition.class_eq_biUnion_of_le {P Q : Partition α} (h : P ≤ Q) (a : α) :
    Q.class a = ⋃ s ∈ {s ∈ P | s ⊆ Q.class a}, s := by
  ext b
  refine ⟨fun hb ↦ ?_, fun hb ↦ ?_⟩
  · exact mem_biUnion ⟨P.class_mem b, (P.class_mono h b).trans_eq (Q.class_eq_class_of_mem hb)⟩
      (P.mem_class b)
  · obtain ⟨s, hs, hs'⟩ := mem_iUnion₂.mp hb
    exact hs.2 hs'

open MeasureTheory

variable [MeasurableSpace Ω] {μ μ₁ μ₂ : Measure Ω} [IsProbabilityMeasure μ]
  [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]

noncomputable abbrev Partition.probabilityAt (P : Partition Ω)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E : Set Ω) (ω : Ω) : ENNReal :=
  μ (E ∩ P.class ω) / μ (P.class ω)

/-- A partition with all parts of positive measure is countable. -/
lemma Partition.countable_of_measure_pos {μ : Measure Ω} [IsProbabilityMeasure μ]
    {P : Partition Ω} (hP : P.Measurable) (hP' : ∀ s ∈ P, μ s > 0) :
    P.val.Countable := by
  rw [← Set.countable_coe_iff, ← Set.countable_univ_iff]
  convert μ.countable_meas_pos_of_disjoint_iUnion (fun s : P.1 ↦ hP s.1 s.2) ?_ using 1
  · ext ⟨s, hs⟩; simp [hP' s hs]
  · simpa [Pairwise] using P.2.pairwiseDisjoint

end Setoid
