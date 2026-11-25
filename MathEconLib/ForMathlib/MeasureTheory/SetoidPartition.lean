/-
Copyright (c) 2026 Ben Eltschig, Jujian Zhang, Ruiz Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig, Jujian Zhang, Ruiz Chen
-/
module

public import MathEconLib.ForMathlib.Order.SetoidPartition
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-!
# Measurable partitions

A partition of a measurable space is measurable when each of its parts is a measurable set.
Measurability passes to coarser partitions only from countable ones: the partition into
singletons is often measurable but refines every partition, including nonmeasurable ones.
Under an s-finite measure, a measurable partition whose parts all have positive measure is
countable, and every measurable set then has the sum of its measures on the parts as its measure.

## Main definitions

* `Setoid.Partitions.Measurable`: every part of the partition is a measurable set.

## Main statements

* `Setoid.Partitions.Measurable.mono`: a partition coarser than a countable measurable
  partition is measurable.
* `Setoid.Partitions.countable_of_measure_pos`: a measurable partition with parts of positive
  measure is countable.
* `Setoid.Partitions.measure_eq_tsum_inter`: the measure of a measurable set is the sum of its
  measures on the parts of a countable measurable partition.

## References

Ruize Chen, Ben Eltschig, Scott Duke Kominers, Ken Ono, and Jujian Zhang (2026),
*We Can't Agree to Disagree, Formally: Aumann's Theorem and Assumption Accounting in Lean*,
Lemma 4.1 (positive cells are countable).
[DOI: 10.2139/ssrn.6837298](https://doi.org/10.2139/ssrn.6837298).

## Provenance

Adapted from the `AgreeToDisagree` Lean development
(<https://github.com/AxiomMath/AgreeToDisagree>), Copyright (c) 2026 Axiom Math, released under
the MIT License; its notice is reproduced in `docs/licenses/AgreeToDisagree-MIT.txt`.
-/

@[expose] public section

open MeasureTheory Set

namespace Setoid.Partitions

variable {α : Type*} [MeasurableSpace α] {P Q : Partitions α}

/-- A partition of a measurable space is measurable if all of its parts are measurable sets. -/
protected def Measurable (P : Partitions α) : Prop :=
  ∀ s ∈ P, MeasurableSet s

/-- In a measurable partition, the part of every point is a measurable set. -/
lemma Measurable.measurableSet_partOf (hP : P.Measurable) (a : α) : MeasurableSet (P.partOf a) :=
  hP _ (P.partOf_mem a)

/-- A partition coarser than a countable measurable partition is measurable. Countability is
needed: the partition into singletons refines every partition. -/
lemma Measurable.mono (hP : P.Measurable) (hc : (P : Set (Set α)).Countable) (h : P ≤ Q) :
    Q.Measurable := by
  intro s hs
  rw [← inter_univ s, ← P.isPartition.sUnion_eq_univ, sUnion_eq_iUnion, inter_iUnion]
  have := hc.to_subtype
  refine MeasurableSet.iUnion fun t ↦ ?_
  obtain ⟨s', hs', hts'⟩ := le_iff_forall_exists_subset.1 h _ t.2
  obtain rfl | hdisj := Q.isPartition.pairwiseDisjoint.eq_or_disjoint hs hs'
  · rw [inter_eq_right.2 hts']
    exact hP _ t.2
  · rw [((show Disjoint s s' from hdisj).mono_right hts').inter_eq]
    exact .empty

/-- The supremum of two measurable partitions is measurable if one of them is countable. -/
lemma Measurable.sup (hP : P.Measurable) (hQ : Q.Measurable)
    (h : (P : Set (Set α)).Countable ∨ (Q : Set (Set α)).Countable) : (P ⊔ Q).Measurable :=
  h.elim (hP.mono · le_sup_left) (hQ.mono · le_sup_right)

/-- Under an s-finite measure, a measurable partition whose parts all have positive measure is
countable. -/
lemma countable_of_measure_pos {μ : Measure α} [SFinite μ] (hP : P.Measurable)
    (hpos : ∀ s ∈ P, 0 < μ s) : (P : Set (Set α)).Countable := by
  rw [← countable_coe_iff, ← countable_univ_iff]
  convert μ.countable_meas_pos_of_disjoint_iUnion (fun s : P ↦ hP s s.2)
    (fun s t hst ↦ P.isPartition.pairwiseDisjoint s.2 t.2 (Subtype.coe_ne_coe.2 hst)) using 1
  ext s
  simp [hpos s s.2]

/-- The measure of a measurable set is the sum of its measures on the parts of a countable
measurable partition. -/
lemma measure_eq_tsum_inter (μ : Measure α) (hP : P.Measurable)
    (hc : (P : Set (Set α)).Countable) {A : Set α} (hA : MeasurableSet A) :
    μ A = ∑' s : P, μ (A ∩ s) := by
  have := hc.to_subtype
  conv_lhs => rw [← inter_univ A, ← P.isPartition.sUnion_eq_univ, sUnion_eq_iUnion, inter_iUnion]
  exact measure_iUnion
    (fun s t hst ↦ (P.isPartition.pairwiseDisjoint s.2 t.2 (Subtype.coe_ne_coe.2 hst)).mono
      inter_subset_right inter_subset_right)
    fun s ↦ hA.inter (hP s s.2)

end Setoid.Partitions
