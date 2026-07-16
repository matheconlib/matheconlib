import Mathlib
import Auctionlib.ForMathlib.Partition

/-! # Neeman's agreement theorem for `p`-beliefs
This file contains a machine-written formalisation of Neeman's agreement theorem for
`p`-beliefs, based on our earlier agreement theorem formalisations.

## Main definitions / results
* `Partition.belief P μ p E`: the event "players with information partition `P` and
  prior `μ` `p`-believe `E`, i.e. assign at least probability `p` to `E`".
* `Partition.IsEvidentBelief P μ p E`: an event is an evident `p`-belief with respect to `P` if
  whenever it occurs, players with information partition `P` `p`-believe it.
* `IsCommonBeliefAt P μ p C ω`: an event `C` is common `p`-belief at `ω` with respect to a family of
  information partitions `P i` if there exists an event `E` containing `ω` such that `E` is
  a `p`-evident belief to all `P i` and whenever `E` occurs, every player with information partition
  `P i` `p`-believes `C`.
* `agreeToDisagree_beliefs`: whenever the posteriors of all players are common `p`-belief, any two
  posteriors can differ by at most `1 - p`.
-/

open Set Setoid MeasureTheory

open scoped ProbabilityTheory

variable {α Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

namespace Setoid

abbrev Partition.belief (P : Partition Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ENNReal) (E : Set Ω) : Set Ω :=
  {ω | p ≤ P.probabilityAt μ E ω}

abbrev Partition.IsEvidentBelief (P : Partition Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ENNReal) (E : Set Ω) : Prop :=
  E ⊆ P.belief μ p E

abbrev _root_.IsCommonBeliefAt {ι : Type*} (P : ι → Partition Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (p : ENNReal) (C : Set Ω) (ω : Ω) : Prop :=
  ∃ E : Set Ω, ω ∈ E ∧ (∀ i, (P i).IsEvidentBelief μ p E) ∧ ∀ i, E ⊆ (P i).belief μ p C

/-! ## Helper lemmas -/

/-- `probabilityAt` is constant on each cell of the partition. -/
lemma Partition.probabilityAt_eq_of_mem_class {P : Partition Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (E : Set Ω) {ω ω' : Ω} (h : ω' ∈ P.class ω) :
    P.probabilityAt μ E ω' = P.probabilityAt μ E ω := by
  rw [Partition.probabilityAt, Partition.class_eq_class_of_mem h]

/-- `belief` is monotone in the event argument. -/
lemma Partition.belief_mono {P : Partition Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p : ENNReal} {A B : Set Ω} (hAB : A ⊆ B) :
    P.belief μ p A ⊆ P.belief μ p B := fun _ hω ↦
  hω.trans <| ENNReal.div_le_div_right (measure_mono (inter_subset_inter_left _ hAB)) _

/-- If `ω` `p`-believes `E`, the entire cell of `ω` does too. -/
lemma Partition.class_subset_belief_of_mem {P : Partition Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {p : ENNReal} {E : Set Ω} {ω : Ω} (h : ω ∈ P.belief μ p E) :
    P.class ω ⊆ P.belief μ p E := fun ω' hω' ↦ by
  show p ≤ μ (E ∩ P.class ω') / μ (P.class ω')
  rw [Partition.class_eq_class_of_mem hω']
  exact h

omit [MeasurableSpace Ω] in
/-- For a cell `s ∈ P` and a union-of-cells set `Q`, either `s ⊆ Q` or `s` is disjoint from `Q`. -/
lemma Partition.cell_inter_unionCells {P : Partition Ω} {s Q : Set Ω}
    (hs : s ∈ P) (hQ_unionCells : ∀ ω ∈ Q, P.class ω ⊆ Q) :
    s ∩ Q = s ∨ s ∩ Q = ∅ := by
  by_cases h : (s ∩ Q).Nonempty
  · obtain ⟨ω₀, hω₀s, hω₀Q⟩ := h
    exact .inl <| inter_eq_left.mpr <|
      Partition.class_eq_of_mem hs hω₀s ▸ hQ_unionCells ω₀ hω₀Q
  · exact .inr <| not_nonempty_iff_eq_empty.mp h

/-- The conditional probability is bounded by `1`. -/
lemma Partition.probabilityAt_le_one' {P : Partition Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hP' : ∀ s ∈ P, μ s > 0) (E : Set Ω) (ω : Ω) :
    P.probabilityAt μ E ω ≤ 1 := by
  rw [Partition.probabilityAt, ENNReal.div_le_iff (hP' _ (P.class_mem ω)).ne' (measure_ne_top μ _)]
  simpa using measure_mono inter_subset_right

/-- If `ω ∈ P.belief μ p A`, the posterior on the belief set at `ω` equals `1`. -/
lemma Partition.probabilityAt_belief_eq_one_of_mem {P : Partition Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hP' : ∀ s ∈ P, μ s > 0)
    {p : ENNReal} {A : Set Ω} {ω : Ω} (hω : ω ∈ P.belief μ p A) :
    P.probabilityAt μ (P.belief μ p A) ω = 1 := by
  have hunion : ∀ ω' ∈ P.belief μ p A, P.class ω' ⊆ P.belief μ p A :=
    fun _ ↦ Partition.class_subset_belief_of_mem
  have heq : P.class ω ∩ P.belief μ p A = P.class ω := by
    rcases Partition.cell_inter_unionCells (P.class_mem ω) hunion with h | h
    · exact h
    · exact absurd (show ω ∈ (∅ : Set Ω) from h ▸ ⟨P.mem_class ω, hω⟩) id
  show μ (P.belief μ p A ∩ P.class ω) / μ (P.class ω) = 1
  rw [inter_comm, heq]
  exact ENNReal.div_self (hP' _ (P.class_mem ω)).ne' (measure_ne_top μ _)

/-- If `ω ∉ P.belief μ p A`, the posterior on the belief set at `ω` equals `0`. -/
lemma Partition.probabilityAt_belief_eq_zero_of_not_mem {P : Partition Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {p : ENNReal} {A : Set Ω} {ω : Ω}
    (hω : ω ∉ P.belief μ p A) :
    P.probabilityAt μ (P.belief μ p A) ω = 0 := by
  have hunion : ∀ ω' ∈ P.belief μ p A, P.class ω' ⊆ P.belief μ p A :=
    fun _ ↦ Partition.class_subset_belief_of_mem
  have heq : P.class ω ∩ P.belief μ p A = ∅ := by
    rcases Partition.cell_inter_unionCells (P.class_mem ω) hunion with h | h
    · exact absurd ((show P.class ω ⊆ P.belief μ p A from h ▸ inter_subset_right) (P.mem_class ω))
        hω
    · exact h
  show μ (P.belief μ p A ∩ P.class ω) / μ (P.class ω) = 0
  rw [inter_comm, heq]
  simp

/-- For a measurable partition with cells of positive measure and `0 < p`, `belief` is
idempotent. -/
lemma Partition.belief_idem_of_pos {P : Partition Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hP' : ∀ s ∈ P, μ s > 0)
    {p : ENNReal} (hp : 0 < p) (A : Set Ω) :
    P.belief μ p (P.belief μ p A) = P.belief μ p A := by
  ext ω
  refine ⟨fun hω ↦ ?_, fun hω ↦ ?_⟩
  · by_contra hnot
    have hle : p ≤ P.probabilityAt μ (P.belief μ p A) ω := hω
    rw [Partition.probabilityAt_belief_eq_zero_of_not_mem hnot, nonpos_iff_eq_zero] at hle
    exact hp.ne' hle
  · show p ≤ P.probabilityAt μ (P.belief μ p A) ω
    rw [Partition.probabilityAt_belief_eq_one_of_mem hP' hω]
    exact hω.trans (Partition.probabilityAt_le_one' hP' A ω)

/-- If `p ≤ P.probabilityAt μ C ω'` with `0 < p`, the cell of `ω'` meets `C`. -/
lemma Partition.class_inter_nonempty_of_pos_probabilityAt {P : Partition Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {p : ENNReal} (hp : 0 < p) {C : Set Ω}
    {ω' : Ω} (h : p ≤ P.probabilityAt μ C ω') :
    (P.class ω' ∩ C).Nonempty := by
  have h1 : 0 < P.probabilityAt μ C ω' := hp.trans_le h
  have h2 : μ (C ∩ P.class ω') ≠ 0 := fun hz ↦ by
    simp [Partition.probabilityAt, hz] at h1
  rw [inter_comm]
  exact nonempty_of_measure_ne_zero h2

/-- If `C ⊆ {ω | P.probabilityAt μ E ω = r}` and the cell of `ω'` meets `C`, the
posterior at `ω'` equals `r`. -/
lemma Partition.probabilityAt_E_eq_of_class_meets {P : Partition Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {E C : Set Ω} {r : ENNReal}
    (hCD : C ⊆ {ω | P.probabilityAt μ E ω = r}) {ω' : Ω}
    (hne : (P.class ω' ∩ C).Nonempty) :
    P.probabilityAt μ E ω' = r := by
  obtain ⟨ω₀, hω₀class, hω₀C⟩ := hne
  rw [← Partition.probabilityAt_eq_of_mem_class μ E hω₀class]
  exact hCD hω₀C

omit [MeasurableSpace Ω] in
/-- Decomposition `Q = ⋃ (s : P.val), s.val ∩ Q`. -/
lemma Partition.eq_iUnion_inter (P : Partition Ω) (Q : Set Ω) :
    Q = ⋃ s : P.val, s.val ∩ Q := by
  ext x
  refine ⟨fun hx ↦ ?_, fun hx ↦ (mem_iUnion.mp hx).choose_spec.2⟩
  obtain ⟨s, hs, hxs⟩ : x ∈ ⋃₀ P.val := P.2.sUnion_eq_univ ▸ trivial
  exact mem_iUnion.mpr ⟨⟨s, hs⟩, hxs, hx⟩

omit [MeasurableSpace Ω] in
/-- The family `s ↦ s.val ∩ Q` over `P.val` is pairwise disjoint. -/
lemma Partition.pairwise_disjoint_inter (P : Partition Ω) (Q : Set Ω) :
    Pairwise (Function.onFun Disjoint (fun s : P.val ↦ s.val ∩ Q)) := fun s₁ s₂ hne ↦
  ((P.2.pairwiseDisjoint s₁.2 s₂.2 fun h ↦ hne (Subtype.ext h)).inter_left Q).inter_right Q

/-- For a measurable partition `P`, every set `s.val ∩ Q` is measurable when `Q` is. -/
lemma Partition.measurableSet_cell_inter {P : Partition Ω} (hP : P.Measurable)
    {Q : Set Ω} (hQ : MeasurableSet Q) (s : P.val) :
    MeasurableSet (s.val ∩ Q) :=
  (hP s.val s.2).inter hQ

lemma Partition.measurableSet_belief {P : Partition Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hP : P.Measurable) (hP' : ∀ s ∈ P, μ s > 0)
    (p : ENNReal) (A : Set Ω) :
    MeasurableSet (P.belief μ p A) := by
  have hSat : ∀ ω ∈ P.belief μ p A, P.class ω ⊆ P.belief μ p A :=
    fun _ ↦ P.class_subset_belief_of_mem
  rw [Partition.eq_iUnion_inter P (P.belief μ p A)]
  haveI : Countable P.val := (Partition.countable_of_measure_pos hP hP').to_subtype
  refine MeasurableSet.iUnion fun s ↦ ?_
  rcases Partition.cell_inter_unionCells s.2 hSat with heq | heq
  · rw [heq]
    exact hP s.1 s.2
  · rw [heq]
    exact .empty

/-- A nonempty union-of-cells set has positive measure when cells do. -/
lemma Partition.measure_pos_of_unionCells_mem {P : Partition Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hP' : ∀ s ∈ P, μ s > 0)
    {Q : Set Ω} (hQ_unionCells : ∀ ω ∈ Q, P.class ω ⊆ Q)
    {ω : Ω} (hω : ω ∈ Q) :
    0 < μ Q :=
  (hP' (P.class ω) (P.class_mem ω)).trans_le (measure_mono (hQ_unionCells ω hω))

/-- Cellwise identity: on each cell `s ⊆ Q` of constant posterior `r`,
`μ(E ∩ s ∩ Q) = r * μ(s ∩ Q)`. -/
lemma Partition.cellwise_measure_eq_of_posterior_const {P : Partition Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hP' : ∀ s ∈ P, μ s > 0)
    {E Q s : Set Ω} (hs : s ∈ P)
    (hQ_unionCells : ∀ ω ∈ Q, P.class ω ⊆ Q)
    {r : ENNReal} (hposterior : ∀ ω ∈ Q, P.probabilityAt μ E ω = r) :
    μ (E ∩ s ∩ Q) = r * μ (s ∩ Q) := by
  rcases Partition.cell_inter_unionCells hs hQ_unionCells with hsQ | hsQ
  · have hs_sub_Q : s ⊆ Q := hsQ ▸ inter_subset_right
    obtain ⟨ω₀, hω₀⟩ : s.Nonempty := Setoid.nonempty_of_mem_partition P.2 hs
    have hpost := hposterior ω₀ (hs_sub_Q hω₀)
    simp only [Partition.probabilityAt, Partition.class_eq_of_mem hs hω₀] at hpost
    rw [show E ∩ s ∩ Q = E ∩ s by rw [inter_assoc, inter_eq_left.mpr hs_sub_Q], hsQ,
      ← hpost, ENNReal.div_mul_cancel (hP' s hs).ne' (measure_ne_top μ s)]
  · rw [hsQ, inter_assoc, hsQ, inter_empty, measure_empty, mul_zero]

lemma Partition.measure_E_inter_eq_mul_of_posteriors_const {P : Partition Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hP : P.Measurable) (hP' : ∀ s ∈ P, μ s > 0)
    {E Q : Set Ω} (hE : MeasurableSet E) (hQ : MeasurableSet Q)
    (hQ_unionCells : ∀ ω ∈ Q, P.class ω ⊆ Q)
    {r : ENNReal} (hposterior : ∀ ω ∈ Q, P.probabilityAt μ E ω = r) :
    μ (E ∩ Q) = r * μ Q := by
  haveI : Countable P.val := (Partition.countable_of_measure_pos hP hP').to_subtype
  have hQ_eq : Q = ⋃ s : P.val, s.val ∩ Q := Partition.eq_iUnion_inter P Q
  have hdisj := Partition.pairwise_disjoint_inter P Q
  have hmeas : ∀ s : P.val, MeasurableSet (s.val ∩ Q) :=
    fun s ↦ Partition.measurableSet_cell_inter hP hQ s
  have hdisj_E : Pairwise (Function.onFun Disjoint (fun s : P.val ↦ E ∩ (s.val ∩ Q))) :=
    fun _ _ hij ↦ (hdisj hij).mono inter_subset_right inter_subset_right
  rw [show E ∩ Q = ⋃ s : P.val, E ∩ (s.val ∩ Q) by
      conv_lhs => rw [hQ_eq]
      exact inter_iUnion _ _,
    measure_iUnion hdisj_E (fun s ↦ hE.inter (hmeas s))]
  conv_rhs => rw [hQ_eq, measure_iUnion hdisj hmeas]
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun s ↦ ?_
  have := Partition.cellwise_measure_eq_of_posterior_const hP' s.2 hQ_unionCells hposterior
    (E := E)
  rwa [inter_assoc] at this

end Setoid

namespace AgreeToDisagree

/-- Cellwise inequality for J-posterior bounds. -/
lemma cellwise_pmul_inter_le {P : Partition Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hP' : ∀ s ∈ P, μ s > 0)
    {J Q : Set Ω} (hQ_unionCells : ∀ ω ∈ Q, P.class ω ⊆ Q)
    {p : ENNReal} (hposterior : ∀ ω ∈ Q, p ≤ P.probabilityAt μ J ω)
    (s : P.val) :
    p * μ (s.val ∩ Q) ≤ μ (J ∩ (s.val ∩ Q)) := by
  obtain heq | heq := Partition.cell_inter_unionCells s.2 hQ_unionCells
  · rw [heq]
    obtain ⟨ω, hω⟩ := Setoid.nonempty_of_mem_partition P.2 s.2
    have hωQ : ω ∈ Q := (heq.symm ▸ hω : ω ∈ s.val ∩ Q).2
    have hpost := hposterior ω hωQ
    change p ≤ μ (J ∩ P.class ω) / μ (P.class ω) at hpost
    rw [Partition.class_eq_of_mem s.2 hω] at hpost
    rwa [ENNReal.le_div_iff_mul_le (.inl (hP' s.val s.2).ne')
      (.inl (measure_ne_top μ s.val))] at hpost
  · simp [heq]

lemma _root_.Setoid.Partition.measure_J_inter_ge_of_posteriors_ge {P : Partition Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hP : P.Measurable) (hP' : ∀ s ∈ P, μ s > 0)
    {J Q : Set Ω} (hJ : MeasurableSet J) (hQ : MeasurableSet Q)
    (hQ_unionCells : ∀ ω ∈ Q, P.class ω ⊆ Q)
    {p : ENNReal} (hposterior : ∀ ω ∈ Q, p ≤ P.probabilityAt μ J ω) :
    p * μ Q ≤ μ (J ∩ Q) := by
  haveI : Countable P.val := (Partition.countable_of_measure_pos hP hP').to_subtype
  have hQ_eq : Q = ⋃ s : P.val, s.val ∩ Q := Partition.eq_iUnion_inter P Q
  have hm : ∀ s : P.val, MeasurableSet (s.val ∩ Q) :=
    fun s ↦ Partition.measurableSet_cell_inter hP hQ s
  have hd := Partition.pairwise_disjoint_inter P Q
  have hdJ : Pairwise (Function.onFun Disjoint (fun s : P.val ↦ J ∩ (s.val ∩ Q))) :=
    fun _ _ hij ↦ (hd hij).mono inter_subset_right inter_subset_right
  have hμQ : μ Q = ∑' s : P.val, μ (s.val ∩ Q) := by
    conv_lhs => rw [hQ_eq]
    exact measure_iUnion hd hm
  have hμJQ : μ (J ∩ Q) = ∑' s : P.val, μ (J ∩ (s.val ∩ Q)) := by
    conv_lhs => rw [show J ∩ Q = ⋃ s : P.val, J ∩ (s.val ∩ Q) by
      conv_lhs => rw [hQ_eq]
      exact inter_iUnion _ _]
    exact measure_iUnion hdJ (fun s ↦ hJ.inter (hm s))
  rw [hμQ, hμJQ, ← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum (cellwise_pmul_inter_le hP' hQ_unionCells hposterior)

/-- ENNReal: for `a ≠ 0` and `a ≠ ⊤`, `(a / b) * (c / a) = c / b`. -/
lemma ennreal_div_mul_div_cancel (a b c : ENNReal) (h0 : a ≠ 0) (ht : a ≠ ⊤) :
    a / b * (c / a) = c / b := by
  rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul,
    show b⁻¹ * a * (a⁻¹ * c) = b⁻¹ * (a * a⁻¹) * c by ring,
    ENNReal.mul_inv_cancel h0 ht, mul_one]

/-- Lower bound: `cond(E|A) ≥ p · cond(E|A∩B)` when `p · μ A ≤ μ(B ∩ A)`. -/
lemma cond_E_A_lower_bound {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p : ENNReal} {E A B : Set Ω}
    (hA_pos : 0 < μ A) (hAB_pos : 0 < μ (A ∩ B))
    (hp_BA : p * μ A ≤ μ (B ∩ A)) :
    p * (μ (E ∩ A ∩ B) / μ (A ∩ B)) ≤ μ (E ∩ A) / μ A := by
  have hA_ne_top : μ A ≠ ⊤ := measure_ne_top μ A
  have hAB_ne_top : μ (A ∩ B) ≠ ⊤ := measure_ne_top μ _
  have hp_AB : p * μ A ≤ μ (A ∩ B) := inter_comm A B ▸ hp_BA
  have hp_div : p ≤ μ (A ∩ B) / μ A :=
    (ENNReal.le_div_iff_mul_le (.inl hA_pos.ne') (.inl hA_ne_top)).mpr hp_AB
  have h_mono : μ (E ∩ A ∩ B) ≤ μ (E ∩ A) := measure_mono inter_subset_left
  calc p * (μ (E ∩ A ∩ B) / μ (A ∩ B))
      ≤ (μ (A ∩ B) / μ A) * (μ (E ∩ A ∩ B) / μ (A ∩ B)) := by gcongr
    _ = μ (E ∩ A ∩ B) / μ A :=
        ennreal_div_mul_div_cancel _ _ _ hAB_pos.ne' hAB_ne_top
    _ ≤ μ (E ∩ A) / μ A := by gcongr

omit [IsProbabilityMeasure μ] in
/-- `μ (Eᶜ ∩ A) = μ A - μ (E ∩ A)` when `E` is measurable and `μ A < ⊤`. -/
lemma measure_compl_inter_eq_sub {E A : Set Ω} (hE : MeasurableSet E)
    (hA_lt : μ A < ⊤) : μ (Eᶜ ∩ A) = μ A - μ (E ∩ A) := by
  have h1 : μ (A ∩ E) + μ (A \ E) = μ A := measure_inter_add_diff A hE
  rw [show A ∩ E = E ∩ A from inter_comm _ _,
    show A \ E = Eᶜ ∩ A by rw [diff_eq, inter_comm]] at h1
  exact ENNReal.eq_sub_of_add_eq
    (ne_top_of_le_ne_top hA_lt.ne (measure_mono inter_subset_right)) ((add_comm _ _).trans h1)

/-- ENNReal: `(a - b) / a = 1 - b / a` when `a ≠ 0`, `a ≠ ⊤`. -/
lemma ennreal_sub_div_eq {a b : ENNReal} (ha_ne_zero : a ≠ 0) (ha_ne_top : a ≠ ⊤) :
    (a - b) / a = 1 - b / a := by
  rw [show (a - b) / a = a / a - b / a from ENNReal.sub_div (by simp_all),
    ENNReal.div_self ha_ne_zero ha_ne_top]

/-- Algebraic helper: from `p * (1 - q) ≤ 1 - r` and bounds in `[0, 1]`, derive
`r ≤ p * q + (1 - p)`. -/
lemma ennreal_upper_bound_from_complement
    {p q r : ENNReal} (hp : p ≤ 1) (hq : q ≤ 1) (hr : r ≤ 1)
    (h : p * (1 - q) ≤ 1 - r) : r ≤ p * q + (1 - p) := by
  have hp_ne_top : p ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hp
  have hq_ne_top : q ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hq
  have hr_ne_top : r ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hr
  have hpq_ne_top : p * q ≠ ⊤ := ENNReal.mul_ne_top hp_ne_top hq_ne_top
  have h_1mp_ne_top : (1 : ENNReal) - p ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have h_1mr_ne_top : (1 : ENNReal) - r ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have h_sum_ne_top : p * q + (1 - p) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hpq_ne_top, h_1mp_ne_top⟩
  have h_real := ENNReal.toReal_mono h_1mr_ne_top h
  rw [ENNReal.toReal_mul, ENNReal.toReal_sub_of_le hq ENNReal.one_ne_top,
      ENNReal.toReal_sub_of_le hr ENNReal.one_ne_top, ENNReal.toReal_one] at h_real
  rw [← ENNReal.ofReal_toReal hr_ne_top, ← ENNReal.ofReal_toReal h_sum_ne_top]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [ENNReal.toReal_add hpq_ne_top h_1mp_ne_top, ENNReal.toReal_mul,
      ENNReal.toReal_sub_of_le hp ENNReal.one_ne_top, ENNReal.toReal_one]
  nlinarith [h_real]

/-- Upper bound: `cond(E|A) ≤ p · cond(E|A∩B) + (1 - p)`. -/
lemma cond_E_A_upper_bound {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p : ENNReal} {E A B : Set Ω} (hE : MeasurableSet E)
    (hA_pos : 0 < μ A) (hAB_pos : 0 < μ (A ∩ B))
    (hp_BA : p * μ A ≤ μ (B ∩ A)) (hp_le_one : p ≤ 1) :
    μ (E ∩ A) / μ A ≤ p * (μ (E ∩ A ∩ B) / μ (A ∩ B)) + (1 - p) := by
  have h_lower : p * (μ (Eᶜ ∩ A ∩ B) / μ (A ∩ B)) ≤ μ (Eᶜ ∩ A) / μ A :=
    cond_E_A_lower_bound (E := Eᶜ) hA_pos hAB_pos hp_BA
  have hA_ne_top : μ A ≠ ⊤ := measure_ne_top μ A
  have hAB_ne_top : μ (A ∩ B) ≠ ⊤ := measure_ne_top μ _
  have hcompl_AB : μ (Eᶜ ∩ A ∩ B) = μ (A ∩ B) - μ (E ∩ A ∩ B) := by
    rw [inter_assoc, show E ∩ A ∩ B = E ∩ (A ∩ B) from inter_assoc _ _ _]
    exact measure_compl_inter_eq_sub hE (measure_lt_top μ _)
  set r : ENNReal := μ (E ∩ A) / μ A with hr_def
  set q : ENNReal := μ (E ∩ A ∩ B) / μ (A ∩ B) with hq_def
  have hr_le : r ≤ 1 := by
    rw [hr_def, ENNReal.div_le_iff hA_pos.ne' hA_ne_top, one_mul]
    exact measure_mono inter_subset_right
  have hq_le : q ≤ 1 := by
    rw [hq_def, ENNReal.div_le_iff hAB_pos.ne' hAB_ne_top, one_mul, inter_assoc]
    exact measure_mono inter_subset_right
  rw [show μ (Eᶜ ∩ A) / μ A = 1 - r by
      rw [measure_compl_inter_eq_sub hE (measure_lt_top μ _), hr_def]
      exact ennreal_sub_div_eq hA_pos.ne' hA_ne_top,
    show μ (Eᶜ ∩ A ∩ B) / μ (A ∩ B) = 1 - q by
      rw [hcompl_AB, hq_def]
      exact ennreal_sub_div_eq hAB_pos.ne' hAB_ne_top] at h_lower
  exact ennreal_upper_bound_from_complement hp_le_one hq_le hr_le h_lower

/-- Combine the bounds `p*q ≤ r{i,j} ≤ p*q + (1-p)` (in ENNReal) into
`|rᵢ.toReal - rⱼ.toReal| ≤ 1 - p.toReal` (in ℝ). -/
lemma final_real_bound {p q ri rj : ENNReal} (hp_le : p ≤ 1) (hq_le : q ≤ 1)
    (hri_le : ri ≤ 1) (hrj_le : rj ≤ 1)
    (hri_lo : p * q ≤ ri) (hri_hi : ri ≤ p * q + (1 - p))
    (hrj_lo : p * q ≤ rj) (hrj_hi : rj ≤ p * q + (1 - p)) :
    |ri.toReal - rj.toReal| ≤ 1 - p.toReal := by
  have hp_ne : p ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hp_le
  have hq_ne : q ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hq_le
  have hri_ne : ri ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hri_le
  have hrj_ne : rj ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hrj_le
  have hpq_ne : p * q ≠ ⊤ := ENNReal.mul_ne_top hp_ne hq_ne
  have h1p_ne : (1 - p) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have hpq_toReal : (p * q).toReal = p.toReal * q.toReal := ENNReal.toReal_mul
  have h1p_toReal : (1 - p).toReal = 1 - p.toReal := by
    rw [ENNReal.toReal_sub_of_le hp_le ENNReal.one_ne_top, ENNReal.toReal_one]
  have hri_lo_r : p.toReal * q.toReal ≤ ri.toReal :=
    hpq_toReal ▸ (ENNReal.toReal_le_toReal hpq_ne hri_ne).mpr hri_lo
  have hrj_lo_r : p.toReal * q.toReal ≤ rj.toReal :=
    hpq_toReal ▸ (ENNReal.toReal_le_toReal hpq_ne hrj_ne).mpr hrj_lo
  have toReal_hi : ∀ {x : ENNReal}, x ≠ ⊤ → x ≤ p * q + (1 - p) →
      x.toReal ≤ p.toReal * q.toReal + (1 - p.toReal) := fun {x} hx_ne hx ↦ by
    have h := (ENNReal.toReal_le_toReal hx_ne (ENNReal.add_ne_top.mpr ⟨hpq_ne, h1p_ne⟩)).mpr hx
    rwa [ENNReal.toReal_add hpq_ne h1p_ne, hpq_toReal, h1p_toReal] at h
  have hri_hi_r := toReal_hi hri_ne hri_hi
  have hrj_hi_r := toReal_hi hrj_ne hrj_hi
  rw [abs_sub_le_iff]
  refine ⟨?_, ?_⟩ <;> linarith

/-! ## Main theorem -/

lemma agreeToDisagree_beliefs {ι : Type*} {P : ι → Partition Ω}
    (hP : ∀ i, (P i).Measurable) (hP' : ∀ i, ∀ s ∈ P i, μ s > 0)
    {E : Set Ω} (hE : MeasurableSet E) (ω : Ω) {p : ENNReal} (hp : 0 < p) {r : ι → ENNReal}
    (h : IsCommonBeliefAt P μ p {ω | ∀ i, (P i).probabilityAt μ E ω = r i} ω) :
    ∀ i j, |(r i).toReal - (r j).toReal| ≤ 1 - p.toReal := by
  intro i j
  set C : Set Ω := {ω | ∀ i, (P i).probabilityAt μ E ω = r i}
  obtain ⟨E0, hωE0, hEvi, hSubBC⟩ := h
  set Fi : Set Ω := (P i).belief μ p E0
  set Fj : Set Ω := (P j).belief μ p E0
  have hωFi : ω ∈ Fi := hEvi i hωE0
  have hωFj : ω ∈ Fj := hEvi j hωE0
  -- Belief idempotence yields F_k ⊆ (P k).belief μ p C
  have hbelC : ∀ k, (P k).belief μ p E0 ⊆ (P k).belief μ p C := fun k ↦ by
    have h1 : (P k).belief μ p E0 ⊆ (P k).belief μ p ((P k).belief μ p C) :=
      Partition.belief_mono (hSubBC k)
    rwa [Partition.belief_idem_of_pos (hP' k) hp] at h1
  -- Posteriors of E are constant (= r k) on F_k
  have hposterior : ∀ k, ∀ ω' ∈ (P k).belief μ p E0, (P k).probabilityAt μ E ω' = r k := by
    intro k ω' hω'
    have hCD : C ⊆ {ω | (P k).probabilityAt μ E ω = r k} := fun _ hω ↦ hω k
    exact Partition.probabilityAt_E_eq_of_class_meets hCD
      (Partition.class_inter_nonempty_of_pos_probabilityAt hp (hbelC k hω'))
  -- F_k is measurable and a union of cells
  have hFmeas : ∀ k, MeasurableSet ((P k).belief μ p E0) := fun k ↦
    Partition.measurableSet_belief (hP k) (hP' k) p E0
  have hFunion : ∀ k, ∀ ω ∈ (P k).belief μ p E0, (P k).class ω ⊆ (P k).belief μ p E0 :=
    fun _ _ ↦ Partition.class_subset_belief_of_mem
  have hFi_pos : 0 < μ Fi :=
    Partition.measure_pos_of_unionCells_mem (hP' i) (hFunion i) hωFi
  have hFj_pos : 0 < μ Fj :=
    Partition.measure_pos_of_unionCells_mem (hP' j) (hFunion j) hωFj
  -- μ(E ∩ F_k) = r k * μ F_k
  have hEF : ∀ k, μ (E ∩ (P k).belief μ p E0) = r k * μ ((P k).belief μ p E0) := fun k ↦
    Partition.measure_E_inter_eq_mul_of_posteriors_const (hP k) (hP' k) hE (hFmeas k)
      (hFunion k) (hposterior k)
  -- Cross-belief bounds via belief monotonicity
  have hFjFi : p * μ Fi ≤ μ (Fj ∩ Fi) :=
    Partition.measure_J_inter_ge_of_posteriors_ge (hP i) (hP' i) (hFmeas j) (hFmeas i)
      (hFunion i) fun _ hω' ↦ Partition.belief_mono (hEvi j) hω'
  have hFiFj : p * μ Fj ≤ μ (Fi ∩ Fj) :=
    Partition.measure_J_inter_ge_of_posteriors_ge (hP j) (hP' j) (hFmeas i) (hFmeas j)
      (hFunion j) fun _ hω' ↦ Partition.belief_mono (hEvi i) hω'
  have hFiFj_pos : 0 < μ (Fi ∩ Fj) := by
    rw [inter_comm]
    exact (ENNReal.mul_pos hp.ne' hFi_pos.ne').trans_le hFjFi
  have hFjFi_pos : 0 < μ (Fj ∩ Fi) := inter_comm Fj Fi ▸ hFiFj_pos
  have hri_eq : r i = μ (E ∩ Fi) / μ Fi := by
    rw [hEF i, ENNReal.mul_div_cancel_right hFi_pos.ne' (measure_ne_top μ _)]
  have hrj_eq : r j = μ (E ∩ Fj) / μ Fj := by
    rw [hEF j, ENNReal.mul_div_cancel_right hFj_pos.ne' (measure_ne_top μ _)]
  have hp_le : p ≤ 1 := hωFi.trans (Partition.probabilityAt_le_one' (hP' i) E0 ω)
  set q : ENNReal := μ (E ∩ Fi ∩ Fj) / μ (Fi ∩ Fj) with hq_def
  have hri_le : r i ≤ 1 := hri_eq ▸ ENNReal.div_le_of_le_mul (by
    rw [one_mul]
    exact measure_mono inter_subset_right)
  have hrj_le : r j ≤ 1 := hrj_eq ▸ ENNReal.div_le_of_le_mul (by
    rw [one_mul]
    exact measure_mono inter_subset_right)
  have hq_le : q ≤ 1 := ENNReal.div_le_of_le_mul (by
    rw [one_mul]
    exact measure_mono (inter_subset_inter_left _ inter_subset_right))
  have hq_swap : q = μ (E ∩ Fj ∩ Fi) / μ (Fj ∩ Fi) := by
    rw [hq_def, show E ∩ Fi ∩ Fj = E ∩ Fj ∩ Fi by
      ext x
      simp only [mem_inter_iff]
      tauto, inter_comm Fi Fj]
  have hri_lo : p * q ≤ r i := by
    rw [hri_eq, hq_def]
    exact cond_E_A_lower_bound hFi_pos hFiFj_pos hFjFi
  have hri_hi : r i ≤ p * q + (1 - p) := by
    rw [hri_eq, hq_def]
    exact cond_E_A_upper_bound hE hFi_pos hFiFj_pos hFjFi hp_le
  have hrj_lo : p * q ≤ r j := by
    rw [hrj_eq, hq_swap]
    exact cond_E_A_lower_bound hFj_pos hFjFi_pos hFiFj
  have hrj_hi : r j ≤ p * q + (1 - p) := by
    rw [hrj_eq, hq_swap]
    exact cond_E_A_upper_bound hE hFj_pos hFjFi_pos hFiFj hp_le
  exact final_real_bound hp_le hq_le hri_le hrj_le hri_lo hri_hi hrj_lo hrj_hi

end AgreeToDisagree
