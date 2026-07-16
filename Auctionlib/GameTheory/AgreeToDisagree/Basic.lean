import Auctionlib.ForMathlib.Partition
import Mathlib.Order.CompletePartialOrder

/-! # Auman's agreement theorem
This file contains a formalisation of Auman's agreement theorem: if the posteriors
of all players at some point are common knowledge, then they must be equal, i.e. it
is impossible to agree to disagree.

See also https://github.com/AxiomMath/AgreeToDisagree.
-/

open Set Setoid

variable {α Ω : Type*}

open MeasureTheory

variable [MeasurableSpace Ω] {μ μ₁ μ₂ : Measure Ω} [IsProbabilityMeasure μ]
  [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]

/-- Let `P` be a partition of `Ω` into measurable non-null sets, `Q` a coarser partition and
`E` a set such that `P.probabilityAt E ω' = p` for all `ω' ∈ Q.class ω`.
Then `Q.probabilityAt E ω = p`. -/
lemma Setoid.Partition.probabilityAt_eq_of_le {P Q : Partition Ω} (hP : P.Measurable)
    (hP' : ∀ s ∈ P, μ s > 0) (hQ : P ≤ Q) {E : Set Ω} (hE : MeasurableSet E) (ω : Ω) {p : ENNReal}
    (h : ∀ ω' ∈ Q.class ω, P.probabilityAt μ E ω' = p) :
    Q.probabilityAt μ E ω = p := by
  have hP'' := P.countable_of_measure_pos hP hP'
  rw [eq_comm, ENNReal.eq_div_iff (pos_mono (P.class_mono hQ ω) (hP' _ (P.class_mem ω))).ne'
      (measure_ne_top _ _),
    P.class_eq_biUnion_of_le hQ ω, Set.inter_iUnion₂,
    measure_biUnion (hP''.mono fun s hs ↦ hs.1) ?_ (fun s hs ↦ hP s hs.1), ← ENNReal.tsum_mul_right,
    measure_biUnion (hP''.mono fun s hs ↦ hs.1) ?_ (fun s hs ↦ hE.inter (hP s hs.1))]
  · congr; ext s
    have ⟨ω', hω'⟩ := Setoid.nonempty_of_mem_partition P.2 s.2.1
    rw [← P.class_eq_of_mem s.2.1 hω',
      ← ENNReal.eq_div_iff (hP' _ (P.class_mem ω')).ne' (measure_ne_top _ _), eq_comm]
    exact h _ (s.2.2 hω')
  · exact (Set.Pairwise.mono inter_subset_left P.2.pairwiseDisjoint).mono'
      (fun s t h ↦ h.mono inf_le_right inf_le_right)
  · exact Set.Pairwise.mono inter_subset_left P.2.pairwiseDisjoint

namespace AgreeToDisagree

/-- Let `Ω` be a probability measure space, `P₁` and `P₂` two measurable partitions representing
the information partitions of two agents, `E` a measurable set and `ω` an event. Then if it is
common knowledge at `ω` that `E` appears to have probability `p₁` to the first agent and probability
`p₂` to the second agent, `p₁ = p₂` - that is, the two agents agree on the probability of `E`. -/
lemma agreeToDisagree {P₁ P₂ : Partition Ω} (hP₁ : P₁.Measurable) (hP₂ : P₂.Measurable)
    (hP₁' : ∀ s ∈ P₁, μ₁ s > 0) (hP₂' : ∀ s ∈ P₂, μ₂ s > 0)
    {E : Set Ω} (hE : MeasurableSet E) (ω : Ω) {p₁ p₂ : ENNReal}
    (h : (P₁ ⊔ P₂).class ω ⊆ {ω' | P₁.probabilityAt μ₁ E ω' = p₁ ∧ P₂.probabilityAt μ₂ E ω' = p₂})
    (h' : (P₁ ⊔ P₂).probabilityAt μ₁ E ω = (P₁ ⊔ P₂).probabilityAt μ₂ E ω) :
    p₁ = p₂ := by
  rw [← P₁.probabilityAt_eq_of_le hP₁ hP₁' le_sup_left hE ω (h.trans inter_subset_left),
    ← P₂.probabilityAt_eq_of_le hP₂ hP₂' le_sup_right hE ω (h.trans inter_subset_right)]
  exact h'

/-- Let `Ω` be a probability measure space, `P` a family of measurable partitions representing
the information partitions of agents indexed by a type `ι`, `E` a measurable set and `ω` an event.
Then if it is common knowledge at `ω` that `E` appears to have probability `p i` to each agent `i`,
`p i = p j` for all `i`, `j` - that is, all agents agree on the probability of `E`. -/
lemma agreeToDisagree' {ι : Type*} {μ : ι → Measure Ω} [∀ i, IsProbabilityMeasure (μ i)]
    {P : ι → Partition Ω} (hP : ∀ i, (P i).Measurable) (hP' : ∀ i, ∀ s ∈ P i, μ i s > 0)
    {E : Set Ω} (hE : MeasurableSet E) (ω : Ω) {p : ι → ENNReal}
    (h : (⨆ i, P i).class ω ⊆ {ω' | ∀ i, (P i).probabilityAt (μ i) E ω' = p i})
    (h' : ∀ i j, (⨆ i, P i).probabilityAt (μ i) E ω = (⨆ i, P i).probabilityAt (μ j) E ω) :
    ∀ i j, p i = p j := by
  intro i j
  rw [← (P i).probabilityAt_eq_of_le (hP i) (hP' i) (le_iSup _ i) hE ω (fun ω' hω'↦ h hω' i),
    ← (P j).probabilityAt_eq_of_le (hP j) (hP' j) (le_iSup _ j) hE ω (fun ω' hω'↦ h hω' j)]
  exact h' i j

end AgreeToDisagree
