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
representative, then so does `sSup S`. This is `AEEqSet`'s countable chain condition
(`exists_countable_sSup_eq`) combined with "a countable supremum is the class of a union"
(`AEEqSet.iSup_mk`): `sSup S` is the class of a *countable* union of `m`-measurable
representatives, which is again `m`-measurable since `m` is a σ-algebra. -/
theorem sSup_mem_subAlgebra [IsProbabilityMeasure μ] {m : MeasurableSpace Ω} (_hm : m ≤ m0)
    {S : Set 𝔹} (hS : S ⊆ subAlgebra m) : sSup S ∈ subAlgebra (μ := μ) m := by
  obtain ⟨t, hts, htc, hst⟩ := @AEEqSet.exists_countable_sSup_eq Ω m0 μ _ S
  haveI := htc.to_subtype
  -- an `m`-measurable representative of each element of the countable subfamily `t`
  choose A hA0 hAm hAeq using fun x : ↥t ↦ hS (hts x.2)
  rw [hst, sSup_eq_iSup',
    show (fun x : ↥t ↦ (x : 𝔹)) = fun x ↦ mkₐ (A x) (hA0 x) from funext hAeq,
    @AEEqSet.iSup_mk Ω m0 μ _ (↥t) _ A hA0]
  exact ⟨⋃ x : ↥t, A x, MeasurableSet.iUnion hA0, MeasurableSet.iUnion hAm, rfl⟩

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
