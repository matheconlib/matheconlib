import Mathlib

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

* `𝐁(𝓤)` is modelled by `GEvent μ`, the quotient of the *`m0`-measurable* sets of
  `Ω` by `μ`-a.e.-equality (`aeSetoid`). Crucially the quotient is over ambient
  *measurable* events (the subtype `{A // MeasurableSet[m0] A}`), NOT over all
  subsets of `Ω`.
* `𝐁(𝓕)` is `subAlgebra m`, the set of classes admitting an `m`-measurable
  representative (`m` is the sub-σ-algebra `𝓕`).
* The Dedekind completeness of the measure algebra of a probability space is a
  classical fact Mathlib does not yet package. We equip the *subtype*
  `↥(subAlgebra m)` with its own `SupSet` (a classically-chosen least upper bound,
  existing by Dedekind completeness of `𝐁(𝓕)`), and define `K` as the supremum
  taken *inside* `𝐁(𝓕)`. Its defining least-upper-bound property under the
  probability-measure and completeness hypotheses is isolated in
  `sub_le_sSup` and `sub_sSup_le`.

All the lattice/order facts below (the meet, join, and order operations, the
partial-order axioms, well-definedness of the Boolean operations) are genuine,
fully proven results with no proof holes.
-/

open MeasureTheory
open scoped symmDiff

namespace MeasureAlgebra

variable {Ω : Type*}

-- Main Definition(s)

/-! ### Definition 1 (Null event) and Definition 2 (Complete sub-σ-algebra) -/

/-- **Definition 1 (Null event).** An `m0`-measurable event `A` is `μ`-null when
`μ A = 0`. -/
def IsNull {m0 : MeasurableSpace Ω} (μ : @Measure Ω m0) (A : Set Ω) : Prop := μ A = 0

/-- **Definition 2 (Complete sub-σ-algebra).** A sub-σ-algebra `m ≤ m0` is *complete*
when it contains every `μ`-null (ambient-measurable) event. -/
def IsComplete {m0 : MeasurableSpace Ω} (μ : @Measure Ω m0) (m : MeasurableSpace Ω)
    (_hm : m ≤ m0) : Prop :=
  ∀ A : Set Ω, MeasurableSet[m0] A → μ A = 0 → MeasurableSet[m] A

/-! ### Definition 3 (Generalised events `𝐁(𝓤)`) -/

/-- The a.e.-equality setoid on `m0`-measurable sets of `Ω`: two measurable sets are
equivalent when they differ by a null set, i.e. `μ (A ∆ D) = 0`, equivalently
`A =ᵐ[μ] D`. -/
def aeSetoid {m0 : MeasurableSpace Ω} (μ : @Measure Ω m0) :
    Setoid {A : Set Ω // MeasurableSet[m0] A} where
  r A D := (A : Set Ω) =ᵐ[μ] (D : Set Ω)
  iseqv := ⟨fun _ => Filter.EventuallyEq.refl _ _, fun h => h.symm, fun h h' => h.trans h'⟩

/-- A **generalised event** (relative to the ambient algebra `𝓤 = m0`) is an
equivalence class of `m0`-measurable sets under a.e.-equality. This is the carrier
of the measure algebra `𝐁(𝓤)`. -/
def GEvent {m0 : MeasurableSpace Ω} (μ : @Measure Ω m0) : Type _ :=
  Quotient (aeSetoid μ)

/-- The class `⟦A⟧` of an ambient-measurable representative `A`. -/
def mk {m0 : MeasurableSpace Ω} {μ : @Measure Ω m0} (A : Set Ω) (hA : MeasurableSet[m0] A) :
    GEvent μ :=
  Quotient.mk (aeSetoid μ) ⟨A, hA⟩

@[simp] theorem mk_eq_mk {m0 : MeasurableSpace Ω} {μ : @Measure Ω m0}
    {A D : Set Ω} {hA : MeasurableSet[m0] A} {hD : MeasurableSet[m0] D} :
    (mk A hA : GEvent μ) = mk D hD ↔ A =ᵐ[μ] D :=
  Quotient.eq (r := aeSetoid μ)

/-- Every generalised event has a measurable representative. -/
theorem exists_rep {m0 : MeasurableSpace Ω} {μ : @Measure Ω m0} (α : GEvent μ) :
    ∃ (A : Set Ω) (hA : MeasurableSet[m0] A), α = mk A hA := by
  refine Quotient.inductionOn α (fun A => ?_)
  exact ⟨A.1, A.2, rfl⟩

/-! ### Definition 5 (Inclusion order `⊑`) -/

/-- The a.e.-inclusion order: `⟦A⟧ ⊑ ⟦D⟧ ↔ μ (A \ D) = 0`. -/
protected def le {m0 : MeasurableSpace Ω} {μ : @Measure Ω m0} :
    GEvent μ → GEvent μ → Prop :=
  Quotient.lift₂ (fun A D => μ ((A : Set Ω) \ (D : Set Ω)) = 0)
    (by
      rintro ⟨A, hA⟩ ⟨D, hD⟩ ⟨A', hA'⟩ ⟨D', hD'⟩ hAeq hDeq
      simp only [eq_iff_iff]
      have hAeq : A =ᵐ[μ] A' := hAeq
      have hDeq : D =ᵐ[μ] D' := hDeq
      constructor
      · intro h
        have : A' \ D' =ᵐ[μ] A \ D := ae_eq_set_diff hAeq.symm hDeq.symm
        rwa [measure_congr this]
      · intro h
        have : A \ D =ᵐ[μ] A' \ D' := ae_eq_set_diff hAeq hDeq
        rwa [measure_congr this])

instance {m0 : MeasurableSpace Ω} {μ : @Measure Ω m0} : LE (GEvent μ) :=
  ⟨MeasureAlgebra.le⟩

@[simp] theorem mk_le_mk {m0 : MeasurableSpace Ω} {μ : @Measure Ω m0} {A D : Set Ω}
    {hA : MeasurableSet[m0] A} {hD : MeasurableSet[m0] D} :
    (mk A hA : GEvent μ) ≤ mk D hD ↔ μ (A \ D) = 0 := Iff.rfl

/-! ### Definition 4 (Boolean operations `⊓`, `⊔`) -/

/-- The infimum `⟦A⟧ ⊓ ⟦D⟧ = ⟦A ∩ D⟧`, well defined on classes. -/
protected def inf {m0 : MeasurableSpace Ω} {μ : @Measure Ω m0} :
    GEvent μ → GEvent μ → GEvent μ :=
  Quotient.lift₂ (fun A D => mk ((A : Set Ω) ∩ (D : Set Ω)) (A.2.inter D.2))
    (by
      rintro ⟨A, hA⟩ ⟨D, hD⟩ ⟨A', hA'⟩ ⟨D', hD'⟩ hAeq hDeq
      exact Quotient.sound (ae_eq_set_inter hAeq hDeq))

/-- The supremum `⟦A⟧ ⊔ ⟦D⟧ = ⟦A ∪ D⟧`, well defined on classes. -/
protected def sup {m0 : MeasurableSpace Ω} {μ : @Measure Ω m0} :
    GEvent μ → GEvent μ → GEvent μ :=
  Quotient.lift₂ (fun A D => mk ((A : Set Ω) ∪ (D : Set Ω)) (A.2.union D.2))
    (by
      rintro ⟨A, hA⟩ ⟨D, hD⟩ ⟨A', hA'⟩ ⟨D', hD'⟩ hAeq hDeq
      exact Quotient.sound (ae_eq_set_union hAeq hDeq))

/-- The symmetric-difference / Boolean addition `⟦A⟧ ⊕ ⟦D⟧ = ⟦A ∆ D⟧`. -/
protected def symmDiff {m0 : MeasurableSpace Ω} {μ : @Measure Ω m0} :
    GEvent μ → GEvent μ → GEvent μ :=
  Quotient.lift₂ (fun A D => mk ((A : Set Ω) ∆ (D : Set Ω)) (A.2.symmDiff D.2))
    (by
      rintro ⟨A, hA⟩ ⟨D, hD⟩ ⟨A', hA'⟩ ⟨D', hD'⟩ hAeq hDeq
      have hAeq : A =ᵐ[μ] A' := hAeq
      have hDeq : D =ᵐ[μ] D' := hDeq
      refine Quotient.sound ?_
      change (A ∆ D) =ᵐ[μ] (A' ∆ D')
      filter_upwards [hAeq, hDeq] with x hx hy
      have hx' : (x ∈ A) = (x ∈ A') := hx
      have hy' : (x ∈ D) = (x ∈ D') := hy
      change (x ∈ (A ∆ D)) = (x ∈ (A' ∆ D'))
      simp only [Set.mem_symmDiff, hx', hy'])

instance {m0 : MeasurableSpace Ω} {μ : @Measure Ω m0} : Min (GEvent μ) := ⟨MeasureAlgebra.inf⟩
instance {m0 : MeasurableSpace Ω} {μ : @Measure Ω m0} : Max (GEvent μ) := ⟨MeasureAlgebra.sup⟩

/-- The Boolean difference `⟦A⟧ - ⟦D⟧ = ⟦A \ D⟧`, well defined on classes. -/
protected def diff {m0 : MeasurableSpace Ω} {μ : @Measure Ω m0} :
    GEvent μ → GEvent μ → GEvent μ :=
  Quotient.lift₂ (fun A D => mk ((A : Set Ω) \ (D : Set Ω)) (A.2.diff D.2))
    (by
      rintro ⟨A, hA⟩ ⟨D, hD⟩ ⟨A', hA'⟩ ⟨D', hD'⟩ hAeq hDeq
      exact Quotient.sound (ae_eq_set_diff hAeq hDeq))

instance {m0 : MeasurableSpace Ω} {μ : @Measure Ω m0} : SDiff (GEvent μ) := ⟨MeasureAlgebra.diff⟩

/-- `⊕`, Boolean addition (symmetric difference) on generalised events. -/
scoped infixl:65 " ⊕ᵍ " => MeasureAlgebra.symmDiff

@[simp] theorem inf_mk {m0 : MeasurableSpace Ω} {μ : @Measure Ω m0}
    (A D : Set Ω) (hA : MeasurableSet[m0] A) (hD : MeasurableSet[m0] D) :
    (mk A hA : GEvent μ) ⊓ mk D hD = mk (A ∩ D) (hA.inter hD) := rfl
@[simp] theorem sup_mk {m0 : MeasurableSpace Ω} {μ : @Measure Ω m0}
    (A D : Set Ω) (hA : MeasurableSet[m0] A) (hD : MeasurableSet[m0] D) :
    (mk A hA : GEvent μ) ⊔ mk D hD = mk (A ∪ D) (hA.union hD) := rfl
@[simp] theorem symmDiff_mk {m0 : MeasurableSpace Ω} {μ : @Measure Ω m0}
    (A D : Set Ω) (hA : MeasurableSet[m0] A) (hD : MeasurableSet[m0] D) :
    (mk A hA : GEvent μ) ⊕ᵍ mk D hD = mk (A ∆ D) (hA.symmDiff hD) := rfl
@[simp] theorem diff_mk {m0 : MeasurableSpace Ω} {μ : @Measure Ω m0}
    (A D : Set Ω) (hA : MeasurableSet[m0] A) (hD : MeasurableSet[m0] D) :
    (mk A hA : GEvent μ) \ mk D hD = mk (A \ D) (hA.diff hD) := rfl

/-- Bottom element `⟦∅⟧`. -/
instance {m0 : MeasurableSpace Ω} {μ : @Measure Ω m0} : Bot (GEvent μ) :=
  ⟨mk ∅ MeasurableSet.empty⟩
/-- Top element `⟦univ⟧`. -/
instance {m0 : MeasurableSpace Ω} {μ : @Measure Ω m0} : Top (GEvent μ) :=
  ⟨mk Set.univ MeasurableSet.univ⟩

@[simp] theorem bot_eq {m0 : MeasurableSpace Ω} {μ : @Measure Ω m0} :
    (⊥ : GEvent μ) = mk ∅ MeasurableSet.empty := rfl
@[simp] theorem top_eq {m0 : MeasurableSpace Ω} {μ : @Measure Ω m0} :
    (⊤ : GEvent μ) = mk Set.univ MeasurableSet.univ := rfl

/-- `GEvent μ` is a partial order under a.e.-inclusion. -/
instance instPartialOrder {m0 : MeasurableSpace Ω} {μ : @Measure Ω m0} :
    PartialOrder (GEvent μ) where
  le := (· ≤ ·)
  le_refl := by
    refine Quotient.ind fun A => ?_
    change μ ((A : Set Ω) \ (A : Set Ω)) = 0
    simp
  le_trans := by
    refine Quotient.ind fun A => Quotient.ind fun D => Quotient.ind fun E => ?_
    intro hAD hDE
    have hAD : μ ((A : Set Ω) \ (D : Set Ω)) = 0 := hAD
    have hDE : μ ((D : Set Ω) \ (E : Set Ω)) = 0 := hDE
    change μ ((A : Set Ω) \ (E : Set Ω)) = 0
    have hsub : (A : Set Ω) \ (E : Set Ω) ⊆
        ((A : Set Ω) \ (D : Set Ω)) ∪ ((D : Set Ω) \ (E : Set Ω)) := by
      intro x hx; by_cases hxD : x ∈ (D : Set Ω)
      · exact Or.inr ⟨hxD, hx.2⟩
      · exact Or.inl ⟨hx.1, hxD⟩
    refine measure_mono_null hsub ?_
    have h := measure_union_le (μ := μ) ((A : Set Ω) \ (D : Set Ω)) ((D : Set Ω) \ (E : Set Ω))
    rw [hAD, hDE, add_zero] at h
    exact le_antisymm h (zero_le _)
  le_antisymm := by
    refine Quotient.ind fun A => Quotient.ind fun D => ?_
    intro hAD hDA
    have hAD : μ ((A : Set Ω) \ (D : Set Ω)) = 0 := hAD
    have hDA : μ ((D : Set Ω) \ (A : Set Ω)) = 0 := hDA
    exact Quotient.sound (ae_eq_set.mpr ⟨hAD, hDA⟩)

/-! ### Definition 3 / Lemma 1.2 (the subalgebra `𝐁(𝓕)`) -/

/-- A generalised event `α` *belongs to* `𝐁(𝓕)` if it has an `m`-measurable
representative, where `m` is the (complete) sub-σ-algebra `𝓕`. -/
def MemSub {m0 : MeasurableSpace Ω} {μ : @Measure Ω m0} (m : MeasurableSpace Ω)
    (α : GEvent μ) : Prop :=
  ∃ (A : Set Ω) (hA : MeasurableSet[m0] A), MeasurableSet[m] A ∧ α = mk A hA

/-- The subalgebra `𝐁(𝓕) = { ⟦A⟧ : A ∈ 𝓕 }` viewed as a subset of `𝐁(𝓤)`. -/
def subAlgebra {m0 : MeasurableSpace Ω} {μ : @Measure Ω m0} (m : MeasurableSpace Ω) :
    Set (GEvent μ) := {α | MemSub m α}

@[simp] theorem mem_subAlgebra {m0 : MeasurableSpace Ω} {μ : @Measure Ω m0}
    {m : MeasurableSpace Ω} {α : GEvent μ} :
    α ∈ subAlgebra m ↔ MemSub m α := Iff.rfl

/-- The bottom class `⟦∅⟧` lies in `𝐁(𝓕)`, so `𝐁(𝓕)` is nonempty. -/
theorem bot_mem_subAlgebra {m0 : MeasurableSpace Ω} {μ : @Measure Ω m0}
    (m : MeasurableSpace Ω) : (⊥ : GEvent μ) ∈ subAlgebra (μ := μ) m :=
  ⟨∅, (@MeasurableSet.empty Ω m0), ⟨(@MeasurableSet.empty Ω m), rfl⟩⟩

instance instNonemptySub {m0 : MeasurableSpace Ω} {μ : @Measure Ω m0}
    {m : MeasurableSpace Ω} : Nonempty (↥(subAlgebra (μ := μ) m)) :=
  ⟨⟨⊥, bot_mem_subAlgebra m⟩⟩

/-! ### Definition 6 (Dedekind completeness of `𝐁(𝓕)`) and the supremum *inside* `𝐁(𝓕)`.

Because `μ` is a probability (finite) measure and `𝓕` is complete, the measure
algebra `𝐁(𝓕)` is Dedekind complete: every subset of `𝐁(𝓕)` has a least upper
bound *within* `𝐁(𝓕)`. We equip the subtype `↥(subAlgebra m)` with a `SupSet`
given by a classically-chosen least upper bound, and isolate its defining property
(that the choice really is a least upper bound in `𝐁(𝓕)`, under the probability +
completeness hypotheses) in `sub_le_sSup` and `sub_sSup_le` below. -/

/-- The arbitrary supremum on the subalgebra `𝐁(𝓕)`, computed *inside* `𝐁(𝓕)`
(i.e. on the subtype `↥(subAlgebra m)`). It is the classically-chosen least upper
bound in `𝐁(𝓕)`, existing by Dedekind completeness of the measure algebra of a
probability space. See `sub_le_sSup`/`sub_sSup_le` for the defining property. -/
noncomputable instance instSupSetSub {m0 : MeasurableSpace Ω} {μ : @Measure Ω m0}
    {m : MeasurableSpace Ω} : SupSet (↥(subAlgebra (μ := μ) m)) :=
  ⟨fun S => Classical.epsilon
    (fun u => (∀ x ∈ S, (x : GEvent μ) ≤ u) ∧
      ∀ v : ↥(subAlgebra (μ := μ) m), (∀ x ∈ S, (x : GEvent μ) ≤ v) → (u : GEvent μ) ≤ v)⟩

/-! ### Definition 7 (The knowledge operator `K`) -/

/-- The set of elements of `𝐁(𝓕)` (as a subtype) lying `⊑`-below `α`. -/
def belowSub {m0 : MeasurableSpace Ω} {μ : @Measure Ω m0} (m : MeasurableSpace Ω)
    (α : GEvent μ) : Set (↥(subAlgebra (μ := μ) m)) :=
  {δ | (δ : GEvent μ) ≤ α}

/-- **Definition 7 (The knowledge operator).** For a complete sub-σ-algebra
`𝓕 = m` and a generalised event `α`, `K(𝓕, α)` is the supremum, computed *inside*
`𝐁(𝓕)`, of the `𝓕`-generalised events lying `⊑`-below `α`. It is by construction an
element of `𝐁(𝓕)`. -/
noncomputable def K {m0 : MeasurableSpace Ω} {μ : @Measure Ω m0}
    (m : MeasurableSpace Ω) (α : GEvent μ) : GEvent μ :=
  ((sSup (belowSub m α) : ↥(subAlgebra (μ := μ) m)) : GEvent μ)

/-- `K(𝓕, α) ∈ 𝐁(𝓕)`: the knowledge operator lands in the subalgebra by
construction (its value is the coercion of an element of `↥(subAlgebra m)`). -/
theorem K_mem_subAlgebra {m0 : MeasurableSpace Ω} {μ : @Measure Ω m0}
    (m : MeasurableSpace Ω) (α : GEvent μ) : K m α ∈ subAlgebra (μ := μ) m :=
  (sSup (belowSub m α)).2

/-! ## Supporting API (parts 1–3, 5 of Lemma 1.7 and the structural lemmas) -/

-- Supporting fact 1 (well-definedness) is realised by `MeasureAlgebra.inf`,
-- `MeasureAlgebra.sup`, `MeasureAlgebra.symmDiff`, `MeasureAlgebra.le` above.

/-- Supporting fact 3 (order characterisation): `⟦A⟧ ⊑ ⟦D⟧ ↔ μ (A \ D) = 0`. -/
theorem le_iff_sdiff_null {m0 : MeasurableSpace Ω} {μ : @Measure Ω m0} {A D : Set Ω}
    {hA : MeasurableSet[m0] A} {hD : MeasurableSet[m0] D} :
    (mk A hA : GEvent μ) ≤ mk D hD ↔ μ (A \ D) = 0 := Iff.rfl

/-- Supporting fact 3 (join by union): `⟦A⟧ ⊔ ⟦D⟧ = ⟦A ∪ D⟧`. -/
theorem sup_eq_union {m0 : MeasurableSpace Ω} {μ : @Measure Ω m0}
    (A D : Set Ω) (hA : MeasurableSet[m0] A) (hD : MeasurableSet[m0] D) :
    (mk A hA : GEvent μ) ⊔ mk D hD = mk (A ∪ D) (hA.union hD) := rfl

/-- **Dedekind completeness of the probability measure algebra (STRONG lub existence).**
This is the analytic crux the whole file rests on. For any set `S` of elements of the
subalgebra `𝐁(𝓕)`, there is `u ∈ 𝐁(𝓕)` which is a *least upper bound of `S` over ALL
of `𝐁(𝓤)`*: it is an upper bound of `S`, and it is `⊑`-below every generalised event
`v` (measurable in the ambient `m0`, not just in `m`) that is an upper bound of `S`.

INFORMAL PROOF (countable-exhaustion / essential supremum; uses `IsProbabilityMeasure`
finiteness and completeness `hcomplete`):
Let `s := ⨆ {μ B : B is an m-measurable finite union of representatives of members of S}`.
Since `μ` is a probability measure, `s ≤ μ Set.univ = 1 < ∞`, so `s` is finite and there
is a sequence `(Bₙ)` of such finite unions with `μ Bₙ → s` and (by replacing `Bₙ` with
`B₀ ∪ … ∪ Bₙ`, still an m-measurable finite union) increasing. Put `U := ⋃ₙ Bₙ`; `U` is
`m`-measurable (a σ-algebra is closed under countable unions) and `μ U = lim μ Bₙ = s`
(monotone-convergence / `tendsto_measure_iUnion`). Let `u := ⟦U⟧ ∈ 𝐁(𝓕)`.
• Upper bound: for `x ∈ S` with rep `X` (m-measurable), if `μ (X \ U) > 0` then
  `U ∪ X` is an m-measurable finite union with `μ (U ∪ X) = μ U + μ (X \ U) > s`,
  contradicting the definition of `s` as the supremum. Hence `μ (X \ U) = 0`, i.e.
  `x ≤ u`.
• Leastness over any GEvent upper bound `v = ⟦V⟧` (V m0-measurable): each `Bₙ` is a
  finite union of reps `X` of members of S, and each such `x ≤ v` means `μ (X \ V) = 0`,
  so `μ (Bₙ \ V) = 0`; taking the countable union, `μ (U \ V) = 0`, i.e. `u ≤ v`.
This `u` is a least upper bound over all of `𝐁(𝓤)`; a fortiori over `𝐁(𝓕)`.

This is exactly the classical statement that the measure algebra of a finite measure
space is Dedekind complete; Mathlib does not package it, so it is proved here from the
countable-exhaustion construction. -/
theorem exists_strong_lub {m0 : MeasurableSpace Ω} {μ : @Measure Ω m0}
    [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ m0)
    (S : Set (↥(subAlgebra (μ := μ) m))) :
    ∃ u : ↥(subAlgebra (μ := μ) m),
      (∀ x ∈ S, (x : GEvent μ) ≤ (u : GEvent μ)) ∧
      (∀ v : GEvent μ, (∀ x ∈ S, (x : GEvent μ) ≤ v) → (u : GEvent μ) ≤ v) := by
  classical
  -- Representative choice function.
  set rep : ↥(subAlgebra (μ := μ) m) → Set Ω := fun x => x.2.choose with hrepdef
  have hrep_m0 : ∀ x, MeasurableSet[m0] (rep x) := fun x => x.2.choose_spec.choose
  have hrep_m : ∀ x, MeasurableSet[m] (rep x) := fun x => x.2.choose_spec.choose_spec.1
  have hrep_eq : ∀ x : ↥(subAlgebra (μ := μ) m), (x : GEvent μ) = mk (rep x) (hrep_m0 x) := by
    intro x
    have h := x.2.choose_spec.choose_spec.2
    exact h
  -- The finite-union measure of a finite subset of S.
  set J : Type _ := {T : Finset (↥(subAlgebra (μ := μ) m)) // (↑T : Set _) ⊆ S} with hJdef
  set val : J → ENNReal := fun T => μ (⋃ x ∈ (T.1 : Finset _), rep x) with hvaldef
  set c : ENNReal := ⨆ T : J, val T with hcdef
  -- Each value ≤ 1.
  have hval_le_one : ∀ T : J, val T ≤ 1 := by
    intro T
    calc val T ≤ μ (Set.univ : Set Ω) := measure_mono (Set.subset_univ _)
      _ = 1 := by simp [measure_univ]
  have hc_le_one : c ≤ 1 := iSup_le hval_le_one
  have hc_ne_top : c ≠ ⊤ := ne_top_of_le_ne_top (by simp) hc_le_one
  -- J is nonempty (empty finset).
  have hJne : Nonempty J := ⟨⟨∅, by simp⟩⟩
  -- Achieving sets: for each n, a finite subset with value within 1/(n+1) of c.
  have hachieve : ∀ n : ℕ, ∃ T : J, c ≤ val T + (1 : ENNReal) / (n + 1) := by
    intro n
    by_cases hc0 : c = 0
    · exact ⟨Classical.choice hJne, by simp [hc0]⟩
    · have hpos : (0 : ENNReal) < (1 : ENNReal) / (n + 1) := by
        apply ENNReal.div_pos_iff.mpr
        constructor
        · norm_num
        · simp
      have hlt : c - (1 : ENNReal) / (n + 1) < c := by
        apply ENNReal.sub_lt_self hc_ne_top hc0
        exact ne_of_gt hpos
      rw [hcdef, lt_iSup_iff] at hlt
      obtain ⟨T, hT⟩ := hlt
      refine ⟨T, ?_⟩
      -- c - d < val T ⇒ c ≤ val T + d
      rw [← tsub_le_iff_right]
      exact le_of_lt hT
  -- Choose the achieving finite sets.
  choose T0 hT0 using hachieve
  -- Increasing partial unions: Tn := ⋃_{k ≤ n} (T0 k).
  set Bset : ℕ → Finset (↥(subAlgebra (μ := μ) m)) :=
    fun n => (Finset.range (n+1)).biUnion (fun k => (T0 k).1) with hBsetdef
  have hBset_sub : ∀ n, (↑(Bset n) : Set _) ⊆ S := by
    intro n x hx
    simp only [hBsetdef, Finset.coe_biUnion, Set.mem_iUnion] at hx
    obtain ⟨k, _, hk⟩ := hx
    exact (T0 k).2 hk
  set B : ℕ → Set Ω := fun n => ⋃ x ∈ Bset n, rep x with hBdef
  have hB_meas_m : ∀ n, MeasurableSet[m] (B n) := by
    intro n
    apply Finset.measurableSet_biUnion
    intro x _
    exact hrep_m x
  have hB_meas : ∀ n, MeasurableSet[m0] (B n) := fun n => hm _ (hB_meas_m n)
  have hBset_mono : Monotone Bset := by
    intro a b hab x hx
    simp only [hBsetdef, Finset.mem_biUnion, Finset.mem_range] at hx ⊢
    obtain ⟨k, hk, hkx⟩ := hx
    exact ⟨k, lt_of_lt_of_le hk (by omega), hkx⟩
  have hB_mono : Monotone B := by
    intro a b hab
    apply Set.biUnion_subset_biUnion_left
    exact_mod_cast hBset_mono hab
  -- Each B n is a finite union of reps of S-members, hence val (as a Finset in J) ≤ c
  -- and includes T0 n so μ (B n) ≥ val (T0 n).
  have hB_val_le : ∀ n, μ (B n) ≤ c := by
    intro n
    have : μ (B n) = val ⟨Bset n, hBset_sub n⟩ := rfl
    rw [this]
    exact le_iSup val ⟨Bset n, hBset_sub n⟩
  have hT0_sub_B : ∀ n, (T0 n).1 ⊆ Bset n := by
    intro n  x hx
    simp only [hBsetdef, Finset.mem_biUnion, Finset.mem_range]
    exact ⟨n, by omega, hx⟩
  have hB_ge : ∀ n, val (T0 n) ≤ μ (B n) := by
    intro n
    apply measure_mono
    apply Set.biUnion_subset_biUnion_left
    exact_mod_cast hT0_sub_B n
  -- Hence c ≤ μ (B n) + 1/(n+1).
  have hB_close : ∀ n, c ≤ μ (B n) + (1:ENNReal)/(n+1) := by
    intro n
    calc c ≤ val (T0 n) + (1:ENNReal)/(n+1) := hT0 n
      _ ≤ μ (B n) + (1:ENNReal)/(n+1) := by
          gcongr
          exact hB_ge n
  -- U := ⋃ n, B n.
  set U : Set Ω := ⋃ n, B n with hUdef
  have hU_meas_m : MeasurableSet[m] U := MeasurableSet.iUnion hB_meas_m
  have hU_meas : MeasurableSet[m0] U := hm _ hU_meas_m
  -- μ U = c via monotone convergence and squeeze.
  have htend : Filter.Tendsto (fun n => μ (B n)) Filter.atTop (nhds (μ U)) := by
    have := tendsto_measure_iUnion_atTop (μ := μ) hB_mono
    simpa [hUdef] using this
  have hμU_le : μ U ≤ c := by
    apply le_of_tendsto htend
    filter_upwards with n using hB_val_le n
  have hμU_ge : c ≤ μ U := by
    -- c ≤ μ (B n) + 1/(n+1); μ(B n) → μ U and 1/(n+1) → 0, so c ≤ μ U
    have htend2 : Filter.Tendsto (fun n => μ (B n) + (1:ENNReal)/(n+1))
        Filter.atTop (nhds (μ U + 0)) := by
      apply Filter.Tendsto.add htend
      have hshift : Filter.Tendsto (fun n : ℕ => ((n : ENNReal) + 1)⁻¹)
          Filter.atTop (nhds 0) := by
        have hbase := ENNReal.tendsto_inv_nat_nhds_zero
        have hcomp : Filter.Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ENNReal)⁻¹)
            Filter.atTop (nhds 0) :=
          hbase.comp (Filter.tendsto_add_atTop_nat 1)
        simpa [Nat.cast_add, Nat.cast_one] using hcomp
      simpa [one_div] using hshift
    rw [add_zero] at htend2
    apply ge_of_tendsto htend2
    filter_upwards with n using hB_close n
  have hμU : μ U = c := le_antisymm hμU_le hμU_ge
  -- The candidate lub u.
  refine ⟨⟨mk U hU_meas, ⟨U, hU_meas, hU_meas_m, rfl⟩⟩, ?_, ?_⟩
  · -- Upper bound: for x ∈ S, μ (rep x \ U) = 0.
    intro x hxS
    rw [hrep_eq x]
    change μ (rep x \ U) = 0
    by_contra hne
    -- consider B n ∪ rep x, measure ≤ c but tends to μ U + μ(rep x \ U) > c
    have hpos : 0 < μ (rep x \ U) := by
      rw [pos_iff_ne_zero]; exact hne
    -- For each n, Bset n ∪ {x} is a finite subset of S, its union is B n ∪ rep x
    set Cset : ℕ → Finset (↥(subAlgebra (μ := μ) m)) :=
      fun n => insert x (Bset n) with hCsetdef
    have hCset_sub : ∀ n, (↑(Cset n) : Set _) ⊆ S := by
      intro n y hy
      simp only [hCsetdef, Finset.coe_insert, Set.mem_insert_iff] at hy
      rcases hy with rfl | hy
      · exact hxS
      · exact hBset_sub n hy
    set C : ℕ → Set Ω := fun n => B n ∪ rep x with hCdef
    have hC_eq : ∀ n, (⋃ y ∈ Cset n, rep y) = C n := by
      intro n
      simp only [hCsetdef, hCdef, Finset.set_biUnion_insert, hBdef]
      rw [Set.union_comm]
    have hC_val_le : ∀ n, μ (C n) ≤ c := by
      intro n
      have : μ (C n) = val ⟨Cset n, hCset_sub n⟩ := by
        simp only [hvaldef]; rw [← hC_eq n]
      rw [this]
      exact le_iSup val ⟨Cset n, hCset_sub n⟩
    have hC_mono : Monotone C := by
      intro a b hab
      apply Set.union_subset_union_left
      exact hB_mono hab
    have hCtend : Filter.Tendsto (fun n => μ (C n)) Filter.atTop (nhds (μ (⋃ n, C n))) := by
      have := tendsto_measure_iUnion_atTop (μ := μ) hC_mono
      simpa using this
    have hCU : (⋃ n, C n) = U ∪ rep x := by
      simp only [hCdef, hUdef]
      rw [Set.iUnion_union]
    have hμCU : μ (⋃ n, C n) ≤ c := by
      apply le_of_tendsto hCtend
      filter_upwards with n using hC_val_le n
    rw [hCU] at hμCU
    -- μ (U ∪ rep x) = μ U + μ (rep x \ U)
    have hunion : μ U + μ (rep x \ U) = μ (U ∪ rep x) :=
      measure_add_diff hU_meas.nullMeasurableSet (rep x)
    rw [← hunion, hμU] at hμCU
    -- c + μ(rep x \ U) ≤ c with c finite and μ(rep x \ U) > 0
    have hle2 : c + μ (rep x \ U) ≤ c + 0 := by rw [add_zero]; exact hμCU
    have hle := ENNReal.le_of_add_le_add_left hc_ne_top hle2
    exact absurd (le_antisymm hle (zero_le _)) hne
  · -- Leastness over any GEvent upper bound v.
    intro v hv
    obtain ⟨V, hV, rfl⟩ := exists_rep v
    change μ (U \ V) = 0
    -- each rep x with x ∈ S is ≤ mk V, i.e. μ (rep x \ V) = 0
    have hrep_null : ∀ x ∈ S, μ (rep x \ V) = 0 := by
      intro x hxS
      have hxv := hv x hxS
      rw [hrep_eq x] at hxv
      exact hxv
    -- μ (B n \ V) = 0 for all n
    have hB_null : ∀ n, μ (B n \ V) = 0 := by
      intro n
      have : B n \ V = ⋃ x ∈ Bset n, (rep x \ V) := by
        simp only [hBdef, Set.iUnion_diff]
      rw [this]
      apply (measure_biUnion_null_iff (Bset n).countable_toSet).mpr
      intro x hx
      exact hrep_null x (hBset_sub n hx)
    -- U \ V = ⋃ n, (B n \ V) is null
    have hUV : U \ V = ⋃ n, (B n \ V) := by
      simp only [hUdef, Set.iUnion_diff]
    rw [hUV]
    apply measure_iUnion_null
    exact hB_null

/-- The (weak) epsilon-predicate of `instSupSetSub` holds for `sSup S`.
`sSup S = Classical.epsilon P` where `P u` = "u upper bound of S ∧ u ≤ every subAlgebra
upper bound v". `exists_strong_lub` provides a witness of `P` (its strong `u` is least
over all GEvent upper bounds, in particular over subAlgebra ones), so `Classical.epsilon_spec`
gives `P (sSup S)`.
SANITY CHECK PASSED: the strong `u` from `exists_strong_lub` satisfies `P`, so `P` is
inhabited and `Classical.epsilon_spec` applies.
HINT: unfold `sSup`/`instSupSetSub` to expose `Classical.epsilon`; obtain `⟨u, hub, hleast⟩`
from `exists_strong_lub m hm hcomplete S`; apply `Classical.epsilon_spec` to
`⟨u, hub, fun v hv => hleast (v : GEvent μ) hv⟩`. -/
theorem sSup_spec {m0 : MeasurableSpace Ω} {μ : @Measure Ω m0}
    [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ m0)
    (S : Set (↥(subAlgebra (μ := μ) m))) :
    (∀ x ∈ S, (x : GEvent μ) ≤ (sSup S : ↥(subAlgebra (μ := μ) m))) ∧
      ∀ v : ↥(subAlgebra (μ := μ) m),
        (∀ x ∈ S, (x : GEvent μ) ≤ v) → ((sSup S : ↥(subAlgebra (μ := μ) m)) : GEvent μ) ≤ v := by
  obtain ⟨u, hub, hleast⟩ := exists_strong_lub m hm S
  have hspec := Classical.epsilon_spec
    (p := fun u : ↥(subAlgebra (μ := μ) m) => (∀ x ∈ S, (x : GEvent μ) ≤ (u : GEvent μ)) ∧
      ∀ v : ↥(subAlgebra (μ := μ) m),
        (∀ x ∈ S, (x : GEvent μ) ≤ (v : GEvent μ)) → (u : GEvent μ) ≤ (v : GEvent μ))
    ⟨u, hub, fun v hv => hleast (v : GEvent μ) hv⟩
  exact hspec

/-- **`sSup S` is least even over arbitrary GEvent upper bounds.** Although the epsilon
predicate only enforces leastness over `subAlgebra` upper bounds, `sSup S` in fact lies
below every generalised-event upper bound of `S` (needed for `K_le`, where `α` need not be
in `𝐁(𝓕)`). Proof: let `u` be the strong lub from `exists_strong_lub`; it is a subAlgebra
element, so by `sSup_spec` leastness (over subAlgebra) `sSup S ≤ u`; and `sSup S` is a
subAlgebra upper bound so by strong leastness of `u`, `u ≤ sSup S`; hence (antisymmetry)
`sSup S = u` as GEvents, and `u ≤ v` for any GEvent upper bound `v` gives `sSup S ≤ v`.
HINT: derive `sSup S ≤ u` and `u ≤ sSup S` (via `sSup_spec` and `exists_strong_lub`),
`le_antisymm` to get equality of the coerced GEvents, then transport `hleast v hv`. -/
theorem sSup_le_gevent {m0 : MeasurableSpace Ω} {μ : @Measure Ω m0}
    [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ m0)
    (S : Set (↥(subAlgebra (μ := μ) m))) (v : GEvent μ)
    (hv : ∀ x ∈ S, (x : GEvent μ) ≤ v) :
    ((sSup S : ↥(subAlgebra (μ := μ) m)) : GEvent μ) ≤ v := by
  obtain ⟨u, hub, hleast⟩ := exists_strong_lub m hm S
  -- sSup S ≤ u (as GEvents) via sSup_spec leastness over subAlgebra elements
  have hspec := sSup_spec m hm S
  have h1 : ((sSup S : ↥(subAlgebra (μ := μ) m)) : GEvent μ) ≤ (u : GEvent μ) :=
    hspec.2 u hub
  -- u ≤ sSup S via strong leastness of u applied to the GEvent upper bound sSup S
  have h2 : (u : GEvent μ) ≤ ((sSup S : ↥(subAlgebra (μ := μ) m)) : GEvent μ) :=
    hleast _ hspec.1
  -- so as GEvents they are equal
  have heq : ((sSup S : ↥(subAlgebra (μ := μ) m)) : GEvent μ) = (u : GEvent μ) :=
    le_antisymm h1 h2
  rw [heq]
  exact hleast v hv

/-- **Dedekind completeness (upper bound part), under probability + completeness.**
`sSup S` (computed in `𝐁(𝓕)`) is an upper bound of `S`. -/
theorem sub_le_sSup {m0 : MeasurableSpace Ω} {μ : @Measure Ω m0}
    [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ m0)
    (S : Set (↥(subAlgebra (μ := μ) m))) (x : ↥(subAlgebra (μ := μ) m)) (hx : x ∈ S) :
    (x : GEvent μ) ≤ sSup S := by
  -- Immediate from `(sSup_spec m hm hcomplete S).1 x hx`.
  exact (sSup_spec m hm S).1 x hx

/-- **Dedekind completeness (least part), under probability + completeness.**
`sSup S` (computed in `𝐁(𝓕)`) is below every upper bound of `S` lying in `𝐁(𝓕)`. -/
theorem sub_sSup_le {m0 : MeasurableSpace Ω} {μ : @Measure Ω m0}
    [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ m0)
    (S : Set (↥(subAlgebra (μ := μ) m))) (v : ↥(subAlgebra (μ := μ) m))
    (hv : ∀ x ∈ S, (x : GEvent μ) ≤ v) :
    ((sSup S : ↥(subAlgebra (μ := μ) m)) : GEvent μ) ≤ v := by
  -- Immediate from `(sSup_spec m hm hcomplete S).2 v hv`.
  exact (sSup_spec m hm S).2 v hv

/-- **Supporting fact 4 (Lemma 1.7.2):** `K(𝓕, α) ⊑ α`. -/
theorem K_le {m0 : MeasurableSpace Ω} {μ : @Measure Ω m0}
    [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ m0) (α : GEvent μ) : K m α ≤ α := by
  -- `K m α = ↑(sSup (belowSub m α))`. `α` is a GEvent upper bound of `belowSub m α`
  -- (by definition every `x ∈ belowSub m α` satisfies `(x:GEvent) ≤ α`), so
  -- `sSup_le_gevent` applies directly.
  -- SANITY CHECK PASSED: `belowSub m α = {δ | (δ:GEvent μ) ≤ α}`, membership is exactly
  -- the required upper-bound hypothesis.
  exact sSup_le_gevent m hm (belowSub m α) α (fun x hx => hx)

/-- **Supporting fact 5 (Lemma 1.7.3):** for `δ ∈ 𝐁(𝓕)`, `δ ⊑ K(𝓕, α) ↔ δ ⊑ α`. -/
theorem le_K_iff {m0 : MeasurableSpace Ω} {μ : @Measure Ω m0}
    [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ m0)
    {α : GEvent μ} {δ : GEvent μ} (hδ : MemSub m δ) :
    δ ≤ K m α ↔ δ ≤ α := by
  -- SANITY CHECK PASSED (both directions are order-theoretic consequences of
  -- `sub_le_sSup`/`K_le`).
  constructor
  · -- (⇒) δ ≤ K m α ≤ α by `K_le` + transitivity.
    intro h
    exact le_trans h (K_le m hm α)
  · -- (⇐) δ ≤ α with δ ∈ 𝐁(𝓕): let δ' := ⟨δ,hδ⟩ ∈ belowSub m α, then
    -- (δ':GEvent) ≤ sSup (belowSub m α) = K m α by `sub_le_sSup`.
    intro h
    have hmem : (⟨δ, hδ⟩ : ↥(subAlgebra (μ := μ) m)) ∈ belowSub m α := h
    exact sub_le_sSup m hm (belowSub m α) ⟨δ, hδ⟩ hmem

/-! ## Main Statement (Lemma 1.7.4) -/

/-- **Main Statement (Lemma 1.7.4).** Let `(Ω, 𝓤, μ)` be a probability space (here
`𝓤 = m0`, `μ` a probability measure on it) and `𝓕 = m` a complete sub-σ-algebra of
`𝓤` (`hm : m ≤ m0`, together with the completeness hypothesis `hcomplete`). For a
generalised event `α`, `K(𝓕, α) = α ↔ α ∈ 𝐁(𝓕)`. -/
theorem lemma_1_7_4 {m0 : MeasurableSpace Ω} {μ : @Measure Ω m0}
    [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ m0) (α : GEvent μ) :
    K m α = α ↔ α ∈ subAlgebra (μ := μ) m := by
  -- SANITY CHECK PASSED (antisymmetry argument from `K_le` + `le_K_iff`).
  constructor
  · -- (⇒) K m α = α ⇒ α = K m α ∈ 𝐁(𝓕) since K lands in the subalgebra.
    intro h
    rw [← h]
    exact K_mem_subAlgebra m α
  · -- (⇐) α ∈ 𝐁(𝓕): α ≤ K m α (from `le_K_iff` ⇐ with δ=α, using α ≤ α) and
    -- K m α ≤ α (`K_le`); antisymmetry gives K m α = α.
    intro hα
    have h1 : K m α ≤ α := K_le m hm α
    have h2 : α ≤ K m α := (le_K_iff m hm (α := α) (δ := α) hα).mpr le_rfl
    exact le_antisymm h1 h2

end MeasureAlgebra
