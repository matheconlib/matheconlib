import Auctionlib.ForMathlib.AEEqSet
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Order.BourbakiWitt
import Mathlib.Order.CompletePartialOrder

/-
# Problem Description

Fix a probability space `(Ω, 𝓤, μ)`: `𝓤` is a σ-algebra on `Ω` and `μ` is a
probability measure (so `μ Ω = 1`, in particular `μ` is finite). Elements of `𝓤`
are called *events*. For events `A, D` the *symmetric difference* is
`A ∆ D = (A ∪ D) \ (A ∩ D)`.

* **Null event.** `A` is `μ`-null if `μ A = 0`.

* **Complete sub-σ-algebra.** A sub-σ-algebra `𝓕 ⊆ 𝓤` is *complete* if it contains
  every `μ`-null event: `μ A = 0 → A ∈ 𝓕`.

* **Generalised events.** Two events are equivalent when their symmetric difference
  is null (equivalently they are a.e. equal). A *generalised event* is an
  equivalence class of ambient-`𝓤`-measurable sets. The set of all generalised
  events relative to the ambient algebra `𝓤` is `𝐁(𝓤)`; the class of `A` is `⟦A⟧`.

* **Boolean operations.** `⟦A⟧ ⊕ ⟦D⟧ = ⟦A ∆ D⟧`, `⟦A⟧ ⊓ ⟦D⟧ = ⟦A ∩ D⟧`, with
  derived join `⟦A⟧ ⊔ ⟦D⟧ = ⟦A ∪ D⟧` and difference `⟦A⟧ - ⟦D⟧ = ⟦A \ D⟧`.

* **Inclusion order.** `⟦A⟧ ⊑ ⟦D⟧ ↔ μ (A \ D) = 0` (a.e. inclusion). This is the
  order induced by the Boolean-algebra structure.

* **Measure algebra.** For a complete sub-σ-algebra `𝓕`, `(𝐁(𝓕), ⊕, ⊓, ⊑)` is a
  Boolean σ-algebra which, since `μ` is a probability measure, is *Dedekind
  complete*: every subset has a least upper bound.

* **Knowledge operator.** For a complete sub-σ-algebra `𝓕` and a generalised event
  `α`, `K(𝓕, α) := sup_{𝐁(𝓕)} { δ ∈ 𝐁(𝓕) : δ ⊑ α }`, the essential supremum of
  the `𝓕`-classes lying below `α`, computed *inside* `𝐁(𝓕)`.

## Main Statement (Lemma 1.7.4)

`K(𝓕, α) = α ↔ α ∈ 𝐁(𝓕)`.

## Modelling notes

We follow the standard Mathlib pattern for sub-σ-algebras: two `MeasurableSpace`
arguments `m ≤ m0`, with the measure `μ` carried by the ambient `m0`.

* `𝐁(𝓤)` is modelled by `MeasureTheory.AEEqSet μ` (from `Auctionlib/ForMathlib/AEEqSet.lean`),
  the measure algebra of `μ`: the quotient of the ambient-*measurable* sets of `Ω`
  by `μ`-a.e.-equality. Its Boolean-algebra structure (`⊔`, `⊓`, `ᶜ`, `\`, `⊥`, `⊤`,
  the a.e.-inclusion order `≤`) and, for finite `μ`, its `CompleteBooleanAlgebra`
  structure (so `sSup` with `le_sSup`/`sSup_le`) are supplied there; here we only add the
  measure-theoretic order characterisation `le_iff`.
* `𝐁(𝓕)` is `subAlgebra m`, the set of classes admitting an `m`-measurable
  representative (`m` is the sub-σ-algebra `𝓕`).
* The knowledge operator needs the supremum to stay *within* `𝐁(𝓕)`. We take `sSup` in `𝐁(𝓤)`
  (using `AEEqSet`'s completeness) and prove separately that `𝐁(𝓕)` is closed under it
  (`sSup_mem_subAlgebra`) — the one place the essential-union / countable-exhaustion argument
  (and finiteness of `μ`) is used.
-/

open MeasureTheory MeasureTheory.AEEqSet
open scoped symmDiff

namespace MeasureAlgebra

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : @Measure Ω m0}

/-- `𝔹` is the measure algebra `𝐁(𝓤)` of the ambient space, i.e. `AEEqSet μ` pinned to the
ambient `MeasurableSpace` `m0`. Pinning is necessary because the sub-σ-algebra `m` appearing in
the theorems below is itself a local `MeasurableSpace Ω`, which would otherwise be picked up by
instance resolution in place of `m0`. -/
local notation "𝔹" => @AEEqSet Ω m0 μ

/-- The class `⟦A⟧` of an ambient-measurable representative, pinned to `m0`. -/
local notation "mkₐ" => @AEEqSet.mk Ω m0 μ

/-! ### Definition 1 (Null event) and Definition 2 (Complete sub-σ-algebra) -/

/-- **Definition 1 (Null event).** An (ambient-measurable) event `A` is `μ`-null when
`μ A = 0`. -/
def IsNull (μ : @Measure Ω m0) (A : Set Ω) : Prop := μ A = 0

/-- **Definition 2 (Complete sub-σ-algebra).** A sub-σ-algebra `m ≤ m0` is *complete*
when it contains every `μ`-null (ambient-measurable) event. -/
def IsComplete (μ : @Measure Ω m0) (m : MeasurableSpace Ω) (_hm : m ≤ m0) : Prop :=
  ∀ A : Set Ω, MeasurableSet[m0] A → μ A = 0 → MeasurableSet[m] A

/-! ### Generalised events `𝐁(𝓤)` and their API

The carrier `𝐁(𝓤)` is `AEEqSet μ`; its Boolean-algebra structure and the basic
`mk_*` rewriting lemmas come from `Auctionlib/ForMathlib/AEEqSet.lean`. We record
here the two facts about `AEEqSet` that this development needs but that are not in
that file: the existence of a representative, and the measure-theoretic form of the
order. -/

/-- Every generalised event has a measurable representative. -/
theorem exists_rep (α : 𝔹) : ∃ (A : Set Ω) (hA : MeasurableSet[m0] A), α = mkₐ A hA :=
  Quotient.inductionOn α fun A => ⟨A.1, A.2, rfl⟩

/-- Two classes coincide iff their representatives are a.e. equal. -/
theorem mk_eq_mk {A D : Set Ω} {hA : MeasurableSet[m0] A} {hD : MeasurableSet[m0] D} :
    (mkₐ A hA = mkₐ D hD) ↔ A =ᵐ[μ] D := Quotient.eq''

/-- **Order characterisation:** `⟦A⟧ ⊑ ⟦D⟧ ↔ μ (A \ D) = 0`. -/
theorem le_iff {A D : Set Ω} {hA : MeasurableSet[m0] A} {hD : MeasurableSet[m0] D} :
    (mkₐ A hA ≤ mkₐ D hD) ↔ μ (A \ D) = 0 := (mk_le_mk hA hD).trans ae_le_set

/-- Boolean addition (symmetric difference) of classes: `⟦A⟧ ∆ ⟦D⟧ = ⟦A ∆ D⟧`. -/
theorem mk_symmDiff_mk {A D : Set Ω} (hA : MeasurableSet[m0] A) (hD : MeasurableSet[m0] D) :
    (mkₐ A hA) ∆ (mkₐ D hD) = mkₐ (A ∆ D) (hA.symmDiff hD) := rfl

/-! ### The subalgebra `𝐁(𝓕)` -/

/-- A generalised event `α` *belongs to* `𝐁(𝓕)` if it has an `m`-measurable
representative, where `m` is the (complete) sub-σ-algebra `𝓕`. -/
def MemSub (m : MeasurableSpace Ω) (α : 𝔹) : Prop :=
  ∃ (A : Set Ω) (hA : MeasurableSet[m0] A), MeasurableSet[m] A ∧ α = mkₐ A hA

/-- The subalgebra `𝐁(𝓕) = { ⟦A⟧ : A ∈ 𝓕 }` viewed as a subset of `𝐁(𝓤)`. -/
def subAlgebra (m : MeasurableSpace Ω) : Set 𝔹 := {α | MemSub m α}

@[simp] theorem mem_subAlgebra {m : MeasurableSpace Ω} {α : 𝔹} :
    α ∈ subAlgebra (μ := μ) m ↔ MemSub m α := Iff.rfl

/-- The bottom class `⟦∅⟧` lies in `𝐁(𝓕)`, so `𝐁(𝓕)` is nonempty. -/
theorem bot_mem_subAlgebra (m : MeasurableSpace Ω) : (⊥ : 𝔹) ∈ subAlgebra (μ := μ) m :=
  ⟨∅, @MeasurableSet.empty Ω m0, @MeasurableSet.empty Ω m, rfl⟩

instance instNonemptySub {m : MeasurableSpace Ω} : Nonempty (↥(subAlgebra (μ := μ) m)) :=
  ⟨⟨⊥, bot_mem_subAlgebra m⟩⟩

/-! ### Completeness: `𝐁(𝓕)` is closed under the supremum of `𝐁(𝓤)`

`AEEqSet μ` is a `CompleteBooleanAlgebra` (as `μ` is finite), so `sSup` and its universal
property `le_sSup`/`sSup_le` are already available on `𝐁(𝓤)`. The only extra fact needed for the
knowledge operator is that `𝐁(𝓕)` is **closed under this supremum**: this is the
Dedekind-completeness content, and the one place the countable-exhaustion / essential-union
argument (and finiteness of `μ`) is used. -/

/-- **`𝐁(𝓕)` is closed under `sSup`.** If every member of `S` has an `m`-measurable
representative, then so does `sSup S`. The witness is the essential union `U = ⋃ₙ Bₙ` of a
countable, measure-maximising family of finite unions of `m`-measurable representatives:
finiteness of `μ` forces `mkₐ U` to be a least upper bound of `S`, and `AEEqSet`'s completeness
then identifies it with `sSup S`. -/
theorem sSup_mem_subAlgebra [IsProbabilityMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ m0)
    {S : Set 𝔹} (hS : S ⊆ subAlgebra m) : sSup S ∈ subAlgebra (μ := μ) m := by
  classical
  -- An `m`-measurable representative of each member of `S`.
  set rep : ↥S → Set Ω := fun x => (hS x.2).choose with hrepdef
  have hrep_m0 : ∀ x, MeasurableSet[m0] (rep x) := fun x => (hS x.2).choose_spec.choose
  have hrep_m : ∀ x, MeasurableSet[m] (rep x) := fun x => (hS x.2).choose_spec.choose_spec.1
  have hrep_eq : ∀ x : ↥S, (x : 𝔹) = mkₐ (rep x) (hrep_m0 x) :=
    fun x => (hS x.2).choose_spec.choose_spec.2
  -- The finite-union measure of a finite subfamily.
  set val : Finset ↥S → ENNReal := fun T => μ (⋃ x ∈ T, rep x) with hvaldef
  set c : ENNReal := ⨆ T : Finset ↥S, val T with hcdef
  have hval_le_one : ∀ T, val T ≤ 1 := fun T =>
    (measure_mono (Set.subset_univ _)).trans_eq measure_univ
  have hc_ne_top : c ≠ ⊤ := ne_top_of_le_ne_top (by simp) (iSup_le hval_le_one)
  -- Finite subfamilies whose value approaches `c`.
  have hachieve : ∀ n : ℕ, ∃ T : Finset ↥S, c ≤ val T + (1 : ENNReal) / (n + 1) := by
    intro n
    by_cases hc0 : c = 0
    · exact ⟨∅, by simp [hc0]⟩
    · have hpos : (0 : ENNReal) < (1 : ENNReal) / (n + 1) :=
        ENNReal.div_pos_iff.mpr ⟨by norm_num, by simp⟩
      have hlt : c - (1 : ENNReal) / (n + 1) < c := ENNReal.sub_lt_self hc_ne_top hc0 hpos.ne'
      rw [hcdef, lt_iSup_iff] at hlt
      obtain ⟨T, hT⟩ := hlt
      exact ⟨T, by rw [← tsub_le_iff_right]; exact hT.le⟩
  choose T0 hT0 using hachieve
  -- Increasing partial unions `Bₙ := ⋃_{k ≤ n} (T0 k)`.
  set Bset : ℕ → Finset ↥S := fun n => (Finset.range (n + 1)).biUnion T0 with hBsetdef
  set B : ℕ → Set Ω := fun n => ⋃ x ∈ Bset n, rep x with hBdef
  have hB_meas_m : ∀ n, MeasurableSet[m] (B n) :=
    fun n => Finset.measurableSet_biUnion _ fun x _ => hrep_m x
  have hB_meas : ∀ n, MeasurableSet[m0] (B n) := fun n => hm _ (hB_meas_m n)
  have hBset_mono : Monotone Bset := by
    intro a b hab x hx
    simp only [hBsetdef, Finset.mem_biUnion, Finset.mem_range] at hx ⊢
    obtain ⟨k, hk, hkx⟩ := hx
    exact ⟨k, lt_of_lt_of_le hk (by omega), hkx⟩
  have hB_mono : Monotone B :=
    fun a b hab => Set.biUnion_subset_biUnion_left (by exact_mod_cast hBset_mono hab)
  have hB_val_le : ∀ n, μ (B n) ≤ c := fun n => le_iSup val (Bset n)
  have hT0_sub_B : ∀ n, T0 n ⊆ Bset n := by
    intro n x hx
    simp only [hBsetdef, Finset.mem_biUnion, Finset.mem_range]
    exact ⟨n, by omega, hx⟩
  have hB_ge : ∀ n, val (T0 n) ≤ μ (B n) :=
    fun n => measure_mono (Set.biUnion_subset_biUnion_left (by exact_mod_cast hT0_sub_B n))
  have hB_close : ∀ n, c ≤ μ (B n) + (1 : ENNReal) / (n + 1) := fun n =>
    (hT0 n).trans (by gcongr; exact hB_ge n)
  -- The essential union `U := ⋃ n, B n`.
  set U : Set Ω := ⋃ n, B n with hUdef
  have hU_meas_m : MeasurableSet[m] U := MeasurableSet.iUnion hB_meas_m
  have hU_meas : MeasurableSet[m0] U := hm _ hU_meas_m
  have htend : Filter.Tendsto (fun n => μ (B n)) Filter.atTop (nhds (μ U)) := by
    simpa [hUdef] using tendsto_measure_iUnion_atTop (μ := μ) hB_mono
  have hμU_le : μ U ≤ c := le_of_tendsto htend (Filter.Eventually.of_forall hB_val_le)
  have hμU_ge : c ≤ μ U := by
    have htend2 : Filter.Tendsto (fun n => μ (B n) + (1 : ENNReal) / (n + 1))
        Filter.atTop (nhds (μ U + 0)) := by
      refine Filter.Tendsto.add htend ?_
      have hcomp := ENNReal.tendsto_inv_nat_nhds_zero.comp (Filter.tendsto_add_atTop_nat 1)
      simpa [Function.comp_def, Nat.cast_add, Nat.cast_one, one_div] using hcomp
    rw [add_zero] at htend2
    exact ge_of_tendsto htend2 (Filter.Eventually.of_forall hB_close)
  have hμU : μ U = c := le_antisymm hμU_le hμU_ge
  -- `mkₐ U` is the least upper bound of `S`; being `m`-measurable, this puts `sSup S` in `𝐁(𝓕)`.
  have hlub : IsLUB S (mkₐ U hU_meas) := by
    constructor
    · -- upper bound
      intro α hα
      set x : ↥S := ⟨α, hα⟩ with hxdef
      show (x : 𝔹) ≤ mkₐ U hU_meas
      rw [hrep_eq x, le_iff]
      by_contra hne
      have hpos : 0 < μ (rep x \ U) := pos_iff_ne_zero.mpr hne
      -- Adjoining `x` to each `Bset n` gives finite subfamilies with union `B n ∪ rep x`.
      set C : ℕ → Set Ω := fun n => B n ∪ rep x with hCdef
      have hC_eq : ∀ n, (⋃ y ∈ insert x (Bset n), rep y) = C n := by
        intro n
        simp only [hCdef, Finset.set_biUnion_insert, hBdef]
        rw [Set.union_comm]
      have hC_val_le : ∀ n, μ (C n) ≤ c := by
        intro n
        have : μ (C n) = val (insert x (Bset n)) := by simp only [hvaldef]; rw [← hC_eq n]
        rw [this]; exact le_iSup val (insert x (Bset n))
      have hC_mono : Monotone C := fun a b hab => Set.union_subset_union_left _ (hB_mono hab)
      have hCtend : Filter.Tendsto (fun n => μ (C n)) Filter.atTop (nhds (μ (⋃ n, C n))) := by
        simpa using tendsto_measure_iUnion_atTop (μ := μ) hC_mono
      have hCU : (⋃ n, C n) = U ∪ rep x := by simp only [hCdef, hUdef]; rw [Set.iUnion_union]
      have hμCU : μ (⋃ n, C n) ≤ c := le_of_tendsto hCtend (Filter.Eventually.of_forall hC_val_le)
      rw [hCU, ← measure_add_diff hU_meas.nullMeasurableSet (rep x), hμU] at hμCU
      have hle2 : c + μ (rep x \ U) ≤ c + 0 := by rw [add_zero]; exact hμCU
      have hle := ENNReal.le_of_add_le_add_left hc_ne_top hle2
      exact hne (le_antisymm hle (zero_le _))
    · -- least upper bound
      intro v hv
      obtain ⟨V, hV, rfl⟩ := exists_rep v
      rw [le_iff]
      have hrep_null : ∀ x : ↥S, μ (rep x \ V) = 0 := by
        intro x
        have hxv := hv x.2
        rw [hrep_eq x, le_iff] at hxv
        exact hxv
      have hB_null : ∀ n, μ (B n \ V) = 0 := by
        intro n
        rw [show B n \ V = ⋃ x ∈ Bset n, (rep x \ V) by simp only [hBdef, Set.iUnion_diff]]
        exact (measure_biUnion_null_iff (Bset n).countable_toSet).mpr fun x _ => hrep_null x
      rw [show U \ V = ⋃ n, (B n \ V) by simp only [hUdef, Set.iUnion_diff]]
      exact measure_iUnion_null hB_null
  rw [(isLUB_sSup S).unique hlub]
  exact ⟨U, hU_meas, hU_meas_m, rfl⟩

/-! ### The knowledge operator `K` -/

/-- The classes in `𝐁(𝓕)` lying `⊑`-below `α`. -/
def belowSub (m : MeasurableSpace Ω) (α : 𝔹) : Set 𝔹 := {δ | δ ∈ subAlgebra m ∧ δ ≤ α}

/-- **The knowledge operator.** `K(𝓕, α)` is the supremum, taken in `𝐁(𝓤)`, of the elements of
`𝐁(𝓕)` lying `⊑`-below `α`. By `sSup_mem_subAlgebra` it again lies in `𝐁(𝓕)`. -/
noncomputable def K [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (α : 𝔹) : 𝔹 :=
  sSup (belowSub m α)

/-- `K(𝓕, α) ∈ 𝐁(𝓕)`: closure of `𝐁(𝓕)` under `sSup`. -/
theorem K_mem_subAlgebra [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ m0) (α : 𝔹) :
    K m α ∈ subAlgebra (μ := μ) m :=
  sSup_mem_subAlgebra hm fun _ hδ => hδ.1

/-- **`K(𝓕, α) ⊑ α`.** -/
theorem K_le [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (α : 𝔹) : K m α ≤ α :=
  sSup_le fun _ hδ => hδ.2

/-- **For `δ ∈ 𝐁(𝓕)`, `δ ⊑ K(𝓕, α) ↔ δ ⊑ α`.** -/
theorem le_K_iff [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) {α δ : 𝔹} (hδ : MemSub m δ) :
    δ ≤ K m α ↔ δ ≤ α :=
  ⟨fun h => le_trans h (K_le m α), fun h => le_sSup ⟨hδ, h⟩⟩

/-! ## Main Statement (Lemma 1.7.4) -/

/-- **Main Statement (Lemma 1.7.4).** Let `(Ω, 𝓤, μ)` be a probability space (`𝓤 = m0`)
and `𝓕 = m` a sub-σ-algebra of `𝓤` (`hm : m ≤ m0`). For a generalised event `α`,
`K(𝓕, α) = α ↔ α ∈ 𝐁(𝓕)`. -/
theorem lemma_1_7_4 [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ m0) (α : 𝔹) :
    K m α = α ↔ α ∈ subAlgebra (μ := μ) m := by
  constructor
  · intro h
    rw [← h]
    exact K_mem_subAlgebra m hm α
  · intro hα
    exact le_antisymm (K_le m α) ((le_K_iff m (α := α) (δ := α) hα).mpr le_rfl)

end MeasureAlgebra
