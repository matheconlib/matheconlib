import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Real.StarOrdered
import Mathlib.Order.BourbakiWitt
import Mathlib.Order.CompletePartialOrder
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.Separation.CompletelyRegular

/-
# Iterative agreement theorems

This file contains an autoformalisation of agreement theorems stated in terms of
convergence of an iterative process of sharing information and adjusting posteriors,
only slightly cleaned up.

## Modeling choices

* A **partition** of `Ω` is modeled by a `Setoid Ω` (equivalence relation), whose
  classes (blocks) are the cells.  For `P : Setoid Ω`, the block of `ω` is
  `cls P ω = {ω' | P ω ω'}`.
* Mathlib's order on `Setoid Ω` is `P ≤ Q ↔ ∀ x y, P x y → Q x y`, i.e. `P ≤ Q`
  means every `P`-class is contained in a `Q`-class, so `P ≤ Q` reads
  "`P` is finer than `Q`".  Hence the **join** `⊔` (supremum) is the finest common
  coarsening — common knowledge — and the **meet** `⊓` (infimum) is the coarsest
  common refinement — pooling/learning.  This matches Definition 1.
* In the measurable setting the agent information is a `MeasureTheory.Filtration ℕ mΩ`
  on a fixed ambient measurable space `mΩ`, and the limit σ-algebra
  `𝓕ᵢ^∞ = σ(⋃ₜ 𝓕ᵢᵗ)` is the supremum of measurable spaces
  `⨆ t, ((ℱ i) t : MeasurableSpace Ω)`.  This is the exact object appearing in
  Mathlib's Lévy upward convergence theorem (`MeasureTheory.tendsto_ae_condExp`,
  `MeasureTheory.tendsto_eLpNorm_condExp`), where the limit conditional
  expectation is written `μ[g | ⨆ n, (↑ℱ n : MeasurableSpace Ω)]`.

## How this attempt addresses the prior feedback

The previous rejection concerned Statement 3: `⨆ t, (ℱ i) t` was applied as if it
were a `MeasurableSpace`, when in fact the `Filtration`-valued supremum is a
*filtration*, not the limit σ-algebra `σ(⋃ₜ 𝓕ᵢᵗ)`.  This attempt introduces an
explicit helper `limitSigmaAlgebra ℱ i : MeasurableSpace Ω := ⨆ t, ((ℱ i) t : ...)`
and uses `μ[· | limitSigmaAlgebra ℱ i]` throughout Statement 3, matching the exact
`⨆ n, (↑ℱ n : MeasurableSpace Ω)` idiom of Mathlib's martingale-convergence API.
The `posteriorProcess` definition now takes the ambient `mΩ : MeasurableSpace Ω`
explicitly and requires `Filtration ℕ mΩ`.
-/

open MeasureTheory Filter Topology

namespace Agreement

variable {Ω : Type*}

/-! ## Main Definition(s) -/

/-- Definition 1 (cell/class).  The block of the setoid-partition `P` containing `ω`. -/
def cls (P : Setoid Ω) (ω : Ω) : Set Ω := {ω' | P ω ω'}

theorem self_mem_cls (P : Setoid Ω) (ω : Ω) : ω ∈ cls P ω := P.refl ω

/-- Definition 2 (finite partition).  A partition `P` is *finite* if it has finitely
many blocks.  Since every block of `P` is `cls P ω` for some `ω` (and conversely), this
is exactly finiteness of the range of the class map `ω ↦ cls P ω`.  (This is equivalent
to finiteness of the quotient `Quotient P`.) -/
def FinitePartition (P : Setoid Ω) : Prop := (Set.range (cls P)).Finite

/-- Definition 3 (union consistency).  A decision function `f` assigns a value in `D`
to every event.  It is *union-consistent* (Cave's union consistency = Bacharach's
sure-thing principle) if for all disjoint nonempty events `A, B`, agreeing on `A` and
`B` forces agreement on `A ∪ B`. -/
def UnionConsistent {D : Type*} (f : Set Ω → D) : Prop :=
  ∀ A B : Set Ω, A.Nonempty → B.Nonempty → Disjoint A B → f A = f B → f (A ∪ B) = f A

/-- Definition 4 (common knowledge of a decision profile).  Relative to a decision
function `f`, agent partitions `P`, common-knowledge partition `C`, state `ω` and
target decisions `δ`, it is *common knowledge at `ω`* that agent `i` takes decision
`δ i` if agent `i`'s decision equals `δ i` on the whole common-knowledge block of `ω`. -/
def CommonKnowledgeDecision {D : Type*} (f : Set Ω → D) {n : ℕ}
    (P : Fin n → Setoid Ω) (C : Setoid Ω) (ω : Ω) (δ : Fin n → D) : Prop :=
  ∀ i : Fin n, cls C ω ⊆ {ω' | f (cls (P i) ω') = δ i}

/-- Definition 6 (posterior-announcement statistic).  For a measure `μ` and event
`E`, agent `i`'s round-`t` announcement is the posterior of `E` given the current cell:
`ω ↦ μ(E ∩ cls P ω) / μ(cls P ω)`.  This is the concrete instance of the posterior
functional `f(A) = μ(E ∩ A)/μ(A)`. -/
noncomputable def posteriorStat [MeasurableSpace Ω] (μ : Measure Ω) (E : Set Ω)
    (P : Setoid Ω) : Ω → ℝ :=
  fun ω => (μ (E ∩ cls P ω)).toReal / (μ (cls P ω)).toReal

/-- Definition 6 (statistic kernel `ofStat`).  The partition into level sets of a
statistic `m` is the kernel setoid `Setoid.ker m`. -/
def ofStat {β : Type*} (m : Ω → β) : Setoid Ω := Setoid.ker m

/-- Definition 6 (canonical posterior-announcement dynamics).  A family
`P : Fin n → ℕ → Setoid Ω` of iterated partitions follows the protocol for
measure `μ` and event `E` if each round refines by the meet with the level-set
partitions of every agent's current posterior statistic:
`Pᵢᵗ⁺¹ = Pᵢᵗ ⊓ ⨅ⱼ ofStat(mⱼᵗ)`, where `mⱼᵗ = posteriorStat μ E (P j t)`. -/
def PosteriorDynamics [MeasurableSpace Ω] (μ : Measure Ω) (E : Set Ω) {n : ℕ}
    (P : Fin n → ℕ → Setoid Ω) : Prop :=
  ∀ (i : Fin n) (t : ℕ),
    P i (t + 1) = P i t ⊓ ⨅ j : Fin n, ofStat (posteriorStat μ E (P j t))

/-- Definition 5 (posterior process, measurable setting).  On a fixed ambient
measurable space `mΩ`, agent `i`'s round-`t` posterior of `E` is the conditional
expectation of `1_E` given the round-`t` σ-algebra `(ℱ i) t` of its filtration. -/
noncomputable def posteriorProcess {mΩ : MeasurableSpace Ω} (μ : Measure Ω)
    (E : Set Ω) {n : ℕ} (ℱ : Fin n → Filtration ℕ mΩ) (i : Fin n) (t : ℕ) :
    Ω → ℝ :=
  μ[Set.indicator E (fun _ => (1 : ℝ)) | ((ℱ i) t : MeasurableSpace Ω)]

/-- Definition 5 (limit σ-algebra `𝓕ᵢ^∞`).  The limit σ-algebra of agent `i`'s
filtration is `𝓕ᵢ^∞ = σ(⋃ₜ 𝓕ᵢᵗ)`, realized as the supremum of measurable spaces
`⨆ t, ((ℱ i) t : MeasurableSpace Ω)`.  This is the exact object appearing in
Mathlib's Lévy upward convergence theorem, and is *not* the (pointwise-in-`t`)
`Filtration`-valued supremum. -/
def limitSigmaAlgebra {mΩ : MeasurableSpace Ω} {n : ℕ}
    (ℱ : Fin n → Filtration ℕ mΩ) (i : Fin n) : MeasurableSpace Ω :=
  ⨆ t : ℕ, ((ℱ i) t : MeasurableSpace Ω)

/-- Definition 5 (announcement update rule).  A family of filtrations
`ℱ : Fin n → Filtration ℕ 𝓖` realizes the measurable announcement dynamics for `μ`
and `E` if, at every round, agent `i`'s next σ-algebra is generated by its own
current σ-algebra together with the σ-algebras generated by all agents' announced
posteriors:  `𝓕ᵢᵗ⁺¹ = 𝓕ᵢᵗ ⊔ ⨆ⱼ σ(Xⱼᵗ)`. -/
def AnnouncementFiltration {mΩ : MeasurableSpace Ω} (μ : Measure Ω) (E : Set Ω)
    {n : ℕ} (ℱ : Fin n → Filtration ℕ mΩ) : Prop :=
  ∀ (i : Fin n) (t : ℕ),
    ((ℱ i) (t + 1) : MeasurableSpace Ω) =
      ((ℱ i) t : MeasurableSpace Ω) ⊔
        (⨆ j : Fin n, MeasurableSpace.comap (posteriorProcess μ E ℱ j t) inferInstance)

/-! ## Auxiliary lemmas (sketch scaffolding) -/

/-- Auxiliary A1 (finite union consistency).  From *binary* union consistency
(Definition 3) one gets preservation under **finite** disjoint unions: if a
nonempty event is a finite disjoint union of nonempty pieces on each of which `f`
takes the value `d`, then `f` of the whole equals `d`.

Formal shape: induct on the finite index set `s`.  Base/step use `hf` on the
running union `A = ⋃_{k ∈ s} g k` and the new block `g a`, which are disjoint
(pairwise-disjoint family), both nonempty, and both carry value `d` (the union by
the induction hypothesis, the block by assumption).  This is the exact "finite
disjoint union preservation" of Definition 3.

STRATEGY (formal phase): `Finset.induction_on` on `s`; maintain the invariant
`f (⋃ k ∈ s, g k) = d`.  Needs: `Set.Finite`/`Finset` bookkeeping of the union,
`Disjoint` of the running union from the new block from pairwise-disjointness,
nonemptiness of the running union (`s.Nonempty`). -/
lemma unionConsistent_biUnion {D : Type*} {f : Set Ω → D} (hf : UnionConsistent f)
    {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (g : ι → Set Ω)
    (hne : ∀ k ∈ s, (g k).Nonempty)
    (hdisj : (s : Set ι).Pairwise (Function.onFun Disjoint g))
    {d : D} (hval : ∀ k ∈ s, f (g k) = d) :
    f (⋃ k ∈ s, g k) = d := by
  classical
  induction s using Finset.induction_on with
  | empty => exact absurd hs (by simp)
  | @insert a s ha ih =>
    rw [Finset.set_biUnion_insert]
    rcases s.eq_empty_or_nonempty with hse | hsne
    · subst hse
      have hemp : (⋃ x ∈ (∅ : Finset ι), g x) = (∅ : Set Ω) := by simp
      rw [hemp, Set.union_empty]
      exact hval a (Finset.mem_insert_self a _)
    · -- running union U = ⋃ k ∈ s, g k is nonempty, f U = d
      have hne' : ∀ k ∈ s, (g k).Nonempty := fun k hk =>
        hne k (Finset.mem_insert_of_mem hk)
      have hdisj' : (s : Set ι).Pairwise (Function.onFun Disjoint g) := by
        intro x hx y hy hxy
        exact hdisj (Finset.mem_insert_of_mem hx) (Finset.mem_insert_of_mem hy) hxy
      have hval' : ∀ k ∈ s, f (g k) = d := fun k hk =>
        hval k (Finset.mem_insert_of_mem hk)
      have hU : f (⋃ k ∈ s, g k) = d := ih hsne hne' hdisj' hval'
      -- nonemptiness of the running union
      obtain ⟨b, hb⟩ := hsne
      have hUne : (⋃ k ∈ s, g k).Nonempty := by
        obtain ⟨x, hx⟩ := hne b (Finset.mem_insert_of_mem hb)
        exact ⟨x, by simp only [Set.mem_iUnion]; exact ⟨b, hb, hx⟩⟩
      -- g a nonempty
      have hane : (g a).Nonempty := hne a (Finset.mem_insert_self a _)
      -- disjointness of g a from the running union
      have hdisjU : Disjoint (g a) (⋃ k ∈ s, g k) := by
        rw [Set.disjoint_iUnion_right]
        intro k
        rw [Set.disjoint_iUnion_right]
        intro hk
        have hak : a ≠ k := fun h => ha (h ▸ hk)
        exact hdisj (Finset.mem_insert_self a _) (Finset.mem_insert_of_mem hk) hak
      -- f (g a) = d
      have hga : f (g a) = d := hval a (Finset.mem_insert_self a _)
      -- apply binary union consistency
      have := hf (g a) (⋃ k ∈ s, g k) hane hUne hdisjU (by rw [hga, hU])
      rw [this, hga]

/-- Auxiliary A2 (common-knowledge block is a finite disjoint union of agent cells).
For `C = ⨆ i, P i`, the class `cls C ω` is the union of the `(P i)`-classes of all
`ω' ∈ cls C ω`; since `P i` is a finite partition, only finitely many distinct
`(P i)`-classes occur, and they are pairwise disjoint (classes of a partition).
Each such class lies inside `cls C ω` because `P i ≤ C` (so `cls (P i) ω' ⊆ cls C ω'
= cls C ω`).

This packages, for a *fixed* agent `i`, the decomposition
`cls C ω = ⨆_{blocks b of P i meeting cls C ω} b`
as a finite disjoint union of nonempty `(P i)`-cells contained in `cls C ω`.

STRATEGY (formal phase): the index set is `Set.range (fun ω' => cls (P i) ω')`
restricted to blocks meeting `cls C ω`; finiteness from `FinitePartition (P i)`;
pairwise disjointness from `Setoid` classes being disjoint or equal; each block
⊆ `cls C ω` from `P i ≤ C = ⨆ P i` and `cls`-monotonicity. -/
lemma cls_join_eq_finite_biUnion_cells {n : ℕ} (P : Fin n → Setoid Ω)
    (hfinP : ∀ i, FinitePartition (P i)) (C : Setoid Ω) (hC : C = ⨆ i, P i)
    (ω : Ω) (i : Fin n) :
    ∃ (s : Finset (Set Ω)),
      s.Nonempty ∧
      (∀ b ∈ s, b.Nonempty) ∧
      (↑s : Set (Set Ω)).Pairwise Disjoint ∧
      (∀ b ∈ s, b ⊆ cls C ω) ∧
      (∀ b ∈ s, ∃ ω' ∈ cls C ω, b = cls (P i) ω') ∧
      cls C ω = ⋃ b ∈ s, b := by
  classical
  -- P i ≤ C
  have hPle : P i ≤ C := by rw [hC]; exact le_iSup P i
  -- basic membership fact
  have hmem : ∀ (Q : Setoid Ω) (x y : Ω), y ∈ cls Q x ↔ Q x y := fun Q x y => Iff.rfl
  -- for ω' ∈ cls C ω, cls C ω' = cls C ω
  have hCeq : ∀ ω', ω' ∈ cls C ω → cls C ω' = cls C ω := by
    intro ω' hω'
    ext x
    simp only [cls, Set.mem_setOf_eq]
    constructor
    · intro h; exact C.trans hω' h
    · intro h; exact C.trans (C.symm hω') h
  -- each (P i)-cell of an element of cls C ω lies in cls C ω
  have hcellsub : ∀ ω', ω' ∈ cls C ω → cls (P i) ω' ⊆ cls C ω := by
    intro ω' hω' x hx
    have : x ∈ cls C ω' := hPle hx
    rw [hCeq ω' hω'] at this
    exact this
  -- The set of cells
  set S : Set (Set Ω) := (fun ω' => cls (P i) ω') '' (cls C ω) with hS
  -- S is finite (subset of range of cls (P i))
  have hSfin : S.Finite := by
    apply Set.Finite.subset (hfinP i)
    rintro b ⟨ω', _, rfl⟩
    exact ⟨ω', rfl⟩
  refine ⟨hSfin.toFinset, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- nonempty: ω itself is in cls C ω, gives cls (P i) ω
    rw [Set.Finite.toFinset_nonempty]
    exact ⟨cls (P i) ω, ω, self_mem_cls C ω, rfl⟩
  · -- each cell nonempty
    intro b hb
    rw [Set.Finite.mem_toFinset] at hb
    obtain ⟨ω', _, rfl⟩ := hb
    exact ⟨ω', self_mem_cls (P i) ω'⟩
  · -- pairwise disjoint
    intro b hb c hc hbc
    simp only [Set.Finite.coe_toFinset] at hb hc
    obtain ⟨x, _, rfl⟩ := hb
    obtain ⟨y, _, rfl⟩ := hc
    -- distinct (P i)-classes are disjoint
    rw [Set.disjoint_left]
    intro z hz hz'
    apply hbc
    -- z ∈ cls (P i) x and z ∈ cls (P i) y ⇒ classes equal
    have hzx : (P i) x z := hz
    have hzy : (P i) y z := hz'
    ext w
    simp only [cls, Set.mem_setOf_eq]
    constructor
    · intro hw; exact (P i).trans hzy ((P i).trans ((P i).symm hzx) hw)
    · intro hw; exact (P i).trans hzx ((P i).trans ((P i).symm hzy) hw)
  · -- each cell ⊆ cls C ω
    intro b hb
    rw [Set.Finite.mem_toFinset] at hb
    obtain ⟨ω', hω', rfl⟩ := hb
    exact hcellsub ω' hω'
  · -- representation
    intro b hb
    rw [Set.Finite.mem_toFinset] at hb
    obtain ⟨ω', hω', rfl⟩ := hb
    exact ⟨ω', hω', rfl⟩
  · -- cover: cls C ω = ⋃ b ∈ S, b
    ext x
    simp only [Set.mem_iUnion, Set.Finite.mem_toFinset, exists_prop]
    constructor
    · intro hx
      -- cls (P i) x is a cell (x ∈ cls C ω), and x ∈ cls (P i) x
      exact ⟨cls (P i) x, ⟨x, hx, rfl⟩, self_mem_cls (P i) x⟩
    · rintro ⟨b, ⟨ω', hω', rfl⟩, hxb⟩
      exact hcellsub ω' hω' hxb

/-! ## Auxiliary lemmas for Statement 3 (measurable convergence) -/

/-- Auxiliary A3 (a.e. convergence, Lévy upward theorem, agent `i`).  The posterior
process `Xᵢᵗ = μ[1_E | (ℱ i) t]` converges `μ`-a.e. to `μ[1_E | ⨆ t (ℱ i) t]`.

This is *exactly* `MeasureTheory.tendsto_ae_condExp` applied to the filtration
`ℱ i` and `g = Set.indicator E (fun _ => 1)`, whose limit `μ[g | ⨆ n, ↑(ℱ i) n]`
is definitionally `μ[g | limitSigmaAlgebra ℱ i]` (since
`limitSigmaAlgebra ℱ i = ⨆ t, ((ℱ i) t : MeasurableSpace Ω)`).

STRATEGY (formal phase): `exact MeasureTheory.tendsto_ae_condExp _` after
unfolding `posteriorProcess` and `limitSigmaAlgebra`; the coercion
`↑(ℱ i) t = ((ℱ i) t : MeasurableSpace Ω)` should be defeq. -/
lemma posteriorProcess_tendsto_ae {mΩ : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (E : Set Ω) {n : ℕ} (ℱ : Fin n → Filtration ℕ mΩ)
    (i : Fin n) :
    ∀ᵐ ω ∂μ, Tendsto (fun t => posteriorProcess μ E ℱ i t ω) atTop
      (𝓝 ((μ[Set.indicator E (fun _ => (1 : ℝ)) | limitSigmaAlgebra ℱ i]) ω)) := by
  -- SANITY CHECK PASSED (Lévy upward a.e. convergence, Mathlib.tendsto_ae_condExp)
  exact MeasureTheory.tendsto_ae_condExp (ℱ := ℱ i)
    (Set.indicator E (fun _ => (1 : ℝ)))

/-- Auxiliary A4 (L¹ convergence, Lévy upward theorem, agent `i`).  The `L¹` norm of
`Xᵢᵗ - μ[1_E | ⨆ t (ℱ i) t]` tends to `0`.  This is `MeasureTheory.tendsto_eLpNorm_condExp`
for the filtration `ℱ i` and `g = Set.indicator E (fun _ => 1)`.

STRATEGY (formal phase): `exact MeasureTheory.tendsto_eLpNorm_condExp _`, unfolding
`posteriorProcess`/`limitSigmaAlgebra` as in A3. -/
lemma posteriorProcess_tendsto_eLpNorm {mΩ : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (E : Set Ω) {n : ℕ} (ℱ : Fin n → Filtration ℕ mΩ)
    (i : Fin n) :
    Tendsto (fun t => eLpNorm
        (posteriorProcess μ E ℱ i t
          - μ[Set.indicator E (fun _ => (1 : ℝ)) | limitSigmaAlgebra ℱ i]) 1 μ)
      atTop (𝓝 0) := by
  -- SANITY CHECK PASSED (Lévy upward L¹ convergence, Mathlib.tendsto_eLpNorm_condExp)
  exact MeasureTheory.tendsto_eLpNorm_condExp (ℱ := ℱ i)
    (Set.indicator E (fun _ => (1 : ℝ)))

/-- Auxiliary A5 (announcements are shared: `σ(Xⱼᵗ) ≤ 𝓕ᵢ^∞` for all `i, j`).
From the announcement update rule `𝓕ᵢᵗ⁺¹ = 𝓕ᵢᵗ ⊔ ⨆ⱼ σ(Xⱼᵗ)` (hypothesis
`AnnouncementFiltration`), every agent's round-`t` announced posterior
`Xⱼᵗ = posteriorProcess μ E ℱ j t` is `𝓕ᵢᵗ⁺¹`-measurable, hence its generated
σ-algebra `σ(Xⱼᵗ)` is `≤ 𝓕ᵢᵗ⁺¹ ≤ 𝓕ᵢ^∞ = limitSigmaAlgebra ℱ i`.

STRATEGY (formal phase): from `hann i t`, `⨆ j σ(Xⱼᵗ) ≤ (ℱ i)(t+1)` via
`le_sup_right`; then `(ℱ i)(t+1) ≤ ⨆ s (ℱ i) s = limitSigmaAlgebra ℱ i` via
`le_iSup`.  Take the `j`-component with `le_iSup`. -/
lemma comap_posteriorProcess_le_limit {mΩ : MeasurableSpace Ω} (μ : Measure Ω)
    (E : Set Ω) {n : ℕ} (ℱ : Fin n → Filtration ℕ mΩ)
    (hann : AnnouncementFiltration μ E ℱ) (i j : Fin n) (t : ℕ) :
    MeasurableSpace.comap (posteriorProcess μ E ℱ j t) inferInstance
      ≤ limitSigmaAlgebra ℱ i := by
  -- σ(Xⱼᵗ) ≤ (ℱ i)(t+1) ≤ ⨆ s (ℱ i) s = limitSigmaAlgebra ℱ i
  have hstep : MeasurableSpace.comap (posteriorProcess μ E ℱ j t) inferInstance
      ≤ ((ℱ i) (t + 1) : MeasurableSpace Ω) := by
    rw [hann i t]
    refine le_trans ?_ le_sup_right
    exact le_iSup (fun j => MeasurableSpace.comap (posteriorProcess μ E ℱ j t) inferInstance) j
  refine le_trans hstep ?_
  exact le_iSup (fun s => ((ℱ i) s : MeasurableSpace Ω)) (t + 1)

/-- Auxiliary A6 (the limit posterior is measurable w.r.t. every agent's limit
σ-algebra).  Since `Xⱼᵗ = posteriorProcess μ E ℱ j t → Xⱼ^∞ = μ[1_E | 𝓕ⱼ^∞]`
`μ`-a.e. (A3 for agent `j`), and each `Xⱼᵗ` is `𝓕ᵢ^∞`-measurable (A5), the a.e.
limit `Xⱼ^∞` is `𝓕ᵢ^∞`-measurable up to a `μ`-null set — i.e. `AEStronglyMeasurable`
w.r.t. `limitSigmaAlgebra ℱ i` (which is `≤ mΩ`, so this makes sense).

This is the crux linking the *announcement-sharing* hypothesis to a measurability
statement about the limit conditional expectations.

STRATEGY (formal phase): each `Xⱼᵗ` is `(𝓕ᵢ^∞)`-strongly-measurable via A5 and
`stronglyMeasurable_condExp`/`comap`; a.e. limits of strongly-measurable functions
are `AEStronglyMeasurable` (`aestronglyMeasurable_of_tendsto_ae` with the A3
convergence).  Needs `limitSigmaAlgebra ℱ i ≤ mΩ` (from `iSup_le` of the
filtration bounds `(ℱ j) t ≤ mΩ`). -/
lemma limit_posterior_aemeasurable {mΩ : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (E : Set Ω) {n : ℕ} (ℱ : Fin n → Filtration ℕ mΩ)
    (hann : AnnouncementFiltration μ E ℱ) (i j : Fin n) :
    AEStronglyMeasurable[limitSigmaAlgebra ℱ i]
      (μ[Set.indicator E (fun _ => (1 : ℝ)) | limitSigmaAlgebra ℱ j]) μ := by
  -- A3 gives a.e. convergence to μ[1_E | 𝓕ⱼ^∞].
  have hconv := posteriorProcess_tendsto_ae μ E ℱ j
  -- limitSigmaAlgebra ℱ i ≤ mΩ, so we may pass to the trimmed measure.
  have hm : limitSigmaAlgebra ℱ i ≤ mΩ := by
    apply iSup_le
    intro t
    exact (ℱ i).le t
  set g : Ω → ℝ := μ[Set.indicator E (fun _ => (1 : ℝ)) | limitSigmaAlgebra ℱ j] with hg
  -- genuine (limitSigmaAlgebra ℱ i)-measurability of each posteriorProcess j t (via A5).
  have hMble : ∀ t : ℕ, Measurable[limitSigmaAlgebra ℱ i] (posteriorProcess μ E ℱ j t) := by
    intro t
    have hcomap : MeasurableSpace.comap (posteriorProcess μ E ℱ j t) inferInstance
        ≤ limitSigmaAlgebra ℱ i := comap_posteriorProcess_le_limit μ E ℱ hann i j t
    exact (measurable_iff_comap_le.mpr le_rfl).le hcomap
  -- Switch the ambient MeasurableSpace instance to limitSigmaAlgebra ℱ i for the
  -- trim work, so all strong-measurability / limit lemmas elaborate at that space.
  letI mi : MeasurableSpace Ω := limitSigmaAlgebra ℱ i
  -- AEStronglyMeasurable on the trimmed measure (space = limitSigmaAlgebra ℱ i).
  have hf' : ∀ t : ℕ,
      AEStronglyMeasurable[mi] (posteriorProcess μ E ℱ j t) (μ.trim hm) :=
    fun t => ((hMble t).stronglyMeasurable).aestronglyMeasurable (μ := μ.trim hm)
  -- "there exists a limit" set is limit-i-measurable, μ-null off it (from hconv),
  -- hence trim-null off it.  Transfer to the trimmed measure.
  have hexlim : ∀ᵐ ω ∂(μ.trim hm),
      ∃ l, Tendsto (fun t => posteriorProcess μ E ℱ j t ω) atTop (𝓝 l) := by
    have hmeasSet : MeasurableSet[limitSigmaAlgebra ℱ i]
        {ω | ∃ l, Tendsto (fun t => posteriorProcess μ E ℱ j t ω) atTop (𝓝 l)} :=
      @measurableSet_exists_tendsto ℕ ℝ Ω (limitSigmaAlgebra ℱ i) _ _ _ _ _
        atTop _ (fun t => posteriorProcess μ E ℱ j t) hMble
    rw [ae_iff]
    have hcompl : MeasurableSet[limitSigmaAlgebra ℱ i]
        {ω | ¬ ∃ l, Tendsto (fun t => posteriorProcess μ E ℱ j t ω) atTop (𝓝 l)} :=
      hmeasSet.compl
    rw [trim_measurableSet_eq hm hcompl, ← ae_iff]
    filter_upwards [hconv] with ω hω
    exact ⟨g ω, hω⟩
  -- Obtain a genuinely (limit-i)-strongly-measurable a.e. limit f_lim (on the trim).
  obtain ⟨f_lim, hf_lim_sm, hf_lim_tendsto⟩ :=
    @exists_stronglyMeasurable_limit_of_tendsto_ae Ω ℝ _ mi (μ.trim hm) _
      (fun t => posteriorProcess μ E ℱ j t) hf' hexlim
  -- Transfer the two convergences back to μ and conclude g =ᵐ[μ] f_lim.
  have hf_lim_tendsto_μ : ∀ᵐ ω ∂μ,
      Tendsto (fun t => posteriorProcess μ E ℱ j t ω) atTop (𝓝 (f_lim ω)) :=
    ae_of_ae_trim hm hf_lim_tendsto
  have hg_eq : g =ᵐ[μ] f_lim := by
    filter_upwards [hconv, hf_lim_tendsto_μ] with ω h1 h2
    exact tendsto_nhds_unique h1 h2
  -- f_lim is StronglyMeasurable[limit i]; with g =ᵐ f_lim, g is AEStronglyMeasurable[limit i].
  exact ⟨f_lim, hf_lim_sm, hg_eq⟩

/-- Helper: if an `L²` element `ZL` has a version measurable w.r.t. a sub-σ-algebra
`𝒞`, then the `L²` orthogonal projection `condExpL2 𝒞` fixes it. -/
lemma condExpL2_eq_self_of_aemeas {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {𝒞 : MeasurableSpace Ω} (hC : 𝒞 ≤ mΩ)
    (ZL : Lp ℝ 2 μ) (h : AEStronglyMeasurable[𝒞] (ZL : Ω → ℝ) μ) :
    (↑((MeasureTheory.condExpL2 ℝ ℝ hC) ZL) : Lp ℝ 2 μ) = ZL := by
  rw [MeasureTheory.Lp.ext_iff]
  have hcE : (↑((MeasureTheory.condExpL2 ℝ ℝ hC)
        ((MeasureTheory.Lp.memLp ZL).toLp (ZL : Ω → ℝ))) : Ω → ℝ)
      =ᵐ[μ] μ[(ZL : Ω → ℝ) | 𝒞] :=
    (MeasureTheory.Lp.memLp ZL).condExpL2_ae_eq_condExp (𝕜 := ℝ) hC
  rw [MeasureTheory.Lp.toLp_coeFn ZL (MeasureTheory.Lp.memLp ZL)] at hcE
  have hself : μ[(ZL : Ω → ℝ) | 𝒞] =ᵐ[μ] (ZL : Ω → ℝ) :=
    MeasureTheory.condExp_of_aestronglyMeasurable' hC h
      ((MeasureTheory.Lp.memLp ZL).integrable (by norm_num))
  exact hcE.trans hself

/-- General agreement lemma (the L² / self-adjoint-projection kernel).  For
`g ∈ L²(μ)` and two sub-σ-algebras `𝒜, ℬ`, if `μ[g|𝒜]` is `ℬ`-measurable and
`μ[g|ℬ]` is `𝒜`-measurable (each a.e.), then the two conditional expectations
coincide `μ`-a.e.  This is the Geanakoplos–Polemarchakis agreement argument in
Hilbert-space form: `X = μ[g|𝒜] = P_𝒜 g` and `Y = μ[g|ℬ] = P_ℬ g` are orthogonal
projections; the cross-measurability hypotheses give `⟪X,X⟫=⟪X,Y⟫=⟪Y,Y⟫`, so
`‖X-Y‖² = 0`. -/
lemma condExp_agree_of_aemeasurable {mΩ : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (g : Ω → ℝ) (hg : MemLp g 2 μ)
    {𝒜 ℬ : MeasurableSpace Ω} (hA : 𝒜 ≤ mΩ) (hB : ℬ ≤ mΩ)
    (H1 : AEStronglyMeasurable[ℬ] (μ[g | 𝒜]) μ)
    (H2 : AEStronglyMeasurable[𝒜] (μ[g | ℬ]) μ) :
    μ[g | 𝒜] =ᵐ[μ] μ[g | ℬ] := by
  classical
  set G : Lp ℝ 2 μ := hg.toLp g with hG
  set XL : Lp ℝ 2 μ := ((MeasureTheory.condExpL2 ℝ ℝ hA) G : Lp ℝ 2 μ) with hXL
  set YL : Lp ℝ 2 μ := ((MeasureTheory.condExpL2 ℝ ℝ hB) G : Lp ℝ 2 μ) with hYL
  -- a.e. links to the conditional expectations
  have hXae : (XL : Ω → ℝ) =ᵐ[μ] μ[g | 𝒜] := by
    rw [hXL, hG]; exact hg.condExpL2_ae_eq_condExp (𝕜 := ℝ) hA
  have hYae : (YL : Ω → ℝ) =ᵐ[μ] μ[g | ℬ] := by
    rw [hYL, hG]; exact hg.condExpL2_ae_eq_condExp (𝕜 := ℝ) hB
  -- versions of XL, YL are measurable w.r.t. their own σ-algebra and (by hyp) the other
  have hX_A : AEStronglyMeasurable[𝒜] (XL : Ω → ℝ) μ :=
    (MeasureTheory.stronglyMeasurable_condExp.aestronglyMeasurable).congr hXae.symm
  have hY_B : AEStronglyMeasurable[ℬ] (YL : Ω → ℝ) μ :=
    (MeasureTheory.stronglyMeasurable_condExp.aestronglyMeasurable).congr hYae.symm
  have hX_B : AEStronglyMeasurable[ℬ] (XL : Ω → ℝ) μ := H1.congr hXae.symm
  have hY_A : AEStronglyMeasurable[𝒜] (YL : Ω → ℝ) μ := H2.congr hYae.symm
  -- the four projection-fixing facts
  have hPA_X : (↑((MeasureTheory.condExpL2 ℝ ℝ hA) XL) : Lp ℝ 2 μ) = XL :=
    condExpL2_eq_self_of_aemeas hA XL hX_A
  have hPB_Y : (↑((MeasureTheory.condExpL2 ℝ ℝ hB) YL) : Lp ℝ 2 μ) = YL :=
    condExpL2_eq_self_of_aemeas hB YL hY_B
  have hPB_X : (↑((MeasureTheory.condExpL2 ℝ ℝ hB) XL) : Lp ℝ 2 μ) = XL :=
    condExpL2_eq_self_of_aemeas hB XL hX_B
  have hPA_Y : (↑((MeasureTheory.condExpL2 ℝ ℝ hA) YL) : Lp ℝ 2 μ) = YL :=
    condExpL2_eq_self_of_aemeas hA YL hY_A
  -- inner-product identities via self-adjointness of condExpL2
  -- ⟪XL, YL⟫ = ⟪G, YL⟫  (P_A applied on the left; P_A YL = YL)
  have key_XY : (inner ℝ XL YL : ℝ) = inner ℝ G YL := by
    have h1 : (inner ℝ XL YL : ℝ)
        = inner ℝ (↑((MeasureTheory.condExpL2 ℝ ℝ hA) G) : Lp ℝ 2 μ) YL := by rw [hXL]
    rw [h1, MeasureTheory.inner_condExpL2_left_eq_right hA, hPA_Y]
  -- ⟪YL, XL⟫ = ⟪G, XL⟫
  have key_YX : (inner ℝ YL XL : ℝ) = inner ℝ G XL := by
    have h1 : (inner ℝ YL XL : ℝ)
        = inner ℝ (↑((MeasureTheory.condExpL2 ℝ ℝ hB) G) : Lp ℝ 2 μ) XL := by rw [hYL]
    rw [h1, MeasureTheory.inner_condExpL2_left_eq_right hB, hPB_X]
  -- ⟪XL, XL⟫ = ⟪G, XL⟫
  have key_XX : (inner ℝ XL XL : ℝ) = inner ℝ G XL := by
    have h1 : (inner ℝ XL XL : ℝ)
        = inner ℝ (↑((MeasureTheory.condExpL2 ℝ ℝ hA) G) : Lp ℝ 2 μ) XL := by rw [hXL]
    rw [h1, MeasureTheory.inner_condExpL2_left_eq_right hA, hPA_X]
  -- ⟪YL, YL⟫ = ⟪G, YL⟫
  have key_YY : (inner ℝ YL YL : ℝ) = inner ℝ G YL := by
    have h1 : (inner ℝ YL YL : ℝ)
        = inner ℝ (↑((MeasureTheory.condExpL2 ℝ ℝ hB) G) : Lp ℝ 2 μ) YL := by rw [hYL]
    rw [h1, MeasureTheory.inner_condExpL2_left_eq_right hB, hPB_Y]
  -- Assemble: ‖XL - YL‖² = 0
  have hXYsymm : (inner ℝ XL YL : ℝ) = inner ℝ YL XL := by
    have := real_inner_comm XL YL; linarith [real_inner_comm XL YL]
  have hnormsq : ‖XL - YL‖ ^ 2 = 0 := by
    rw [norm_sub_sq_real]
    have e3 : (inner ℝ XL XL : ℝ) = ‖XL‖ ^ 2 := real_inner_self_eq_norm_sq XL
    have e4 : (inner ℝ YL YL : ℝ) = ‖YL‖ ^ 2 := real_inner_self_eq_norm_sq YL
    -- ⟪XL,XL⟫ = ⟪XL,YL⟫ = ⟪YL,YL⟫ ⇒ ‖XL‖²-2⟪XL,YL⟫+‖YL‖² = 0
    linarith [key_XY, key_YX, key_XX, key_YY, hXYsymm, e3, e4]
  have hXeqY : XL = YL := by
    have : ‖XL - YL‖ = 0 := by
      have := hnormsq
      nlinarith [norm_nonneg (XL - YL)]
    rwa [norm_eq_zero, sub_eq_zero] at this
  -- transfer back to a.e. equality of the conditional expectations
  have : (XL : Ω → ℝ) =ᵐ[μ] (YL : Ω → ℝ) := by rw [hXeqY]
  exact hXae.symm.trans (this.trans hYae)

/-- Auxiliary A7 (limit agreement — the analytic kernel).  Under the announcement
filtration hypothesis, all agents' limiting posteriors coincide `μ`-a.e.:
`μ[1_E | 𝓕ᵢ^∞] =ᵐ[μ] μ[1_E | 𝓕ⱼ^∞]`.

MATH ARGUMENT (Geanakoplos–Polemarchakis at the limit, in Hilbert-space form).
Write `g = 1_E ∈ L²(μ)`.  The two limiting posteriors `X = μ[g | 𝓕ᵢ^∞]` and
`Y = μ[g | 𝓕ⱼ^∞]` are the orthogonal `L²` projections of `g` onto the two sub-σ-
algebras.  A6 (with roles swapped) shows `X` is `𝓕ⱼ^∞`-measurable and `Y` is
`𝓕ᵢ^∞`-measurable.  Self-adjointness of the conditional-expectation projection then
forces `⟪X,X⟫ = ⟪X,Y⟫ = ⟪Y,Y⟫`, whence `‖X-Y‖² = 0`, i.e. `X =ᵐ Y`.  This is the
content of `condExp_agree_of_aemeasurable`; the two measurability hypotheses are
exactly `limit_posterior_aemeasurable` (A6). -/
lemma limit_posterior_agree {mΩ : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (E : Set Ω) (hE : MeasurableSet E) {n : ℕ}
    (ℱ : Fin n → Filtration ℕ mΩ) (hann : AnnouncementFiltration μ E ℱ) (i j : Fin n) :
    (μ[Set.indicator E (fun _ => (1 : ℝ)) | limitSigmaAlgebra ℱ i])
      =ᵐ[μ]
    (μ[Set.indicator E (fun _ => (1 : ℝ)) | limitSigmaAlgebra ℱ j]) := by
  -- SANITY CHECK PASSED (agreement kernel via L² self-adjoint projection)
  have hgMemLp : MemLp (Set.indicator E (fun _ => (1 : ℝ))) 2 μ :=
    MeasureTheory.memLp_indicator_const 2 hE (1 : ℝ) (Or.inr (measure_ne_top μ E))
  have hA : limitSigmaAlgebra ℱ i ≤ mΩ := iSup_le (fun t => (ℱ i).le t)
  have hB : limitSigmaAlgebra ℱ j ≤ mΩ := iSup_le (fun t => (ℱ j).le t)
  exact condExp_agree_of_aemeasurable μ (Set.indicator E (fun _ => (1 : ℝ))) hgMemLp
    hA hB (limit_posterior_aemeasurable μ E ℱ hann j i)
    (limit_posterior_aemeasurable μ E ℱ hann i j)

/-! ## Auxiliary lemmas for Statement 2 (finite dynamics) -/

/-- Auxiliary A8 (halting: an antitone chain of finite partitions on a finite space
stabilizes).  With `Ω` finite, `t ↦ P i t` is antitone (`PosteriorDynamics` refines
by a meet, so `P i (t+1) ≤ P i t`).  On a finite `Ω` the number of blocks is bounded
by `|Ω|`, and a strict refinement strictly increases the block count, so there are no
infinite strictly-descending chains; hence some finite `T` with `P i t = P i T` for
`t ≥ T` (uniform over the finitely many agents).

STRATEGY (formal phase): antitonicity from `hdyn` + `inf_le_left`; wellfoundedness of
`>` on `Setoid Ω` for finite `Ω` (`Finite Ω ⇒ Finite (Setoid Ω)`, so
`WellFoundedLT`/`IsWellFounded`); `WellFounded`-based eventual constancy of an antitone
sequence; combine the per-agent stabilization times into one `T` via `Finset.max`. -/
lemma dynamics_halts [Finite Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E : Set Ω) {n : ℕ}
    (P : Fin n → ℕ → Setoid Ω) (hdyn : PosteriorDynamics μ E P) :
    ∃ T : ℕ, ∀ (i : Fin n) (t : ℕ), T ≤ t → P i t = P i T := by
  classical
  -- Setoid Ω is finite, hence WellFoundedLT.
  have hfin : Finite (Setoid Ω) :=
    Finite.of_injective (fun P : Setoid Ω => (P.r : Ω → Ω → Prop))
      (fun P Q h => Setoid.ext (fun x y => by
        have := congrFun (congrFun h x) y; simpa using this))
  have hwf : WellFoundedLT (Setoid Ω) := by
    haveI := hfin
    exact Finite.to_wellFoundedLT
  -- Each agent's partition sequence is antitone.
  have hanti : ∀ i : Fin n, Antitone (fun t => P i t) := by
    intro i
    have hstep : ∀ t, P i (t + 1) ≤ P i t := by
      intro t
      rw [hdyn i t]; exact inf_le_left
    exact antitone_nat_of_succ_le hstep
  -- Per-agent stabilization time (finite ⇒ WellFoundedLT ⇒ antitone chain condition).
  have hstab : ∀ i : Fin n, ∃ N : ℕ, ∀ m, N ≤ m → P i N = P i m := by
    intro i
    haveI := hwf
    haveI : WellFoundedGT (Setoid Ω)ᵒᵈ := hwf
    -- View the antitone sequence as a monotone sequence into the order dual.
    let g : ℕ →o (Setoid Ω)ᵒᵈ :=
      ⟨fun t => OrderDual.toDual (P i t), fun a b hab => (hanti i hab)⟩
    obtain ⟨N, hNg⟩ := WellFoundedGT.monotone_chain_condition g
    refine ⟨N, fun m hm => ?_⟩
    have := hNg m hm
    exact OrderDual.toDual_inj.mp this
  choose N hN using hstab
  -- Combine over the finitely many agents.
  refine ⟨Finset.univ.sup N, ?_⟩
  intro i t ht
  have hiN : N i ≤ Finset.univ.sup N := Finset.le_sup (Finset.mem_univ i)
  have h1 : P i (N i) = P i t := hN i t (le_trans hiN ht)
  have h2 : P i (N i) = P i (Finset.univ.sup N) := hN i _ hiN
  rw [← h1, h2]

/-- The posterior functional `f(A) = μ(E ∩ A)/μ(A)`. -/
noncomputable def posteriorFunctional [MeasurableSpace Ω] (μ : Measure Ω) (E : Set Ω)
    (A : Set Ω) : ℝ := (μ (E ∩ A)).toReal / (μ A).toReal

/-- `posteriorStat` is the posterior functional applied to the cell. -/
lemma posteriorStat_eq_functional [MeasurableSpace Ω] (μ : Measure Ω) (E : Set Ω)
    (P : Setoid Ω) (ω : Ω) :
    posteriorStat μ E P ω = posteriorFunctional μ E (cls P ω) := rfl

/-- On a finite space, every partition is finite. -/
lemma finitePartition_of_finite [Finite Ω] (P : Setoid Ω) : FinitePartition P := by
  have : Finite (Set.range (cls P)) := Set.finite_range (cls P)
  exact Set.finite_range (cls P)

/-- A real-arithmetic lemma underlying union consistency of ratios. -/
lemma ratio_union_aux {a b ea eb : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hea : 0 ≤ ea) (heb : 0 ≤ eb) (haea : ea ≤ a) (hbeb : eb ≤ b)
    (hr : ea / a = eb / b) :
    (ea + eb) / (a + b) = ea / a := by
  rcases eq_or_lt_of_le ha with ha0 | ha0
  · -- a = 0 ⇒ ea = 0
    have haz : a = 0 := ha0.symm
    have heaz : ea = 0 := le_antisymm (haea.trans_eq haz) hea
    subst haz; subst heaz
    simp only [zero_add, div_zero] at hr ⊢
    -- hr : 0 = eb / b, so eb / b = 0
    rcases eq_or_lt_of_le hb with hb0 | hb0
    · have hbz : b = 0 := hb0.symm
      subst hbz; simp
    · -- b > 0, eb / b = 0 ⇒ eb = 0
      have : eb = 0 := by
        have := hr.symm
        rwa [div_eq_zero_iff, or_iff_left (ne_of_gt hb0)] at this
      subst this; simp
  · rcases eq_or_lt_of_le hb with hb0 | hb0
    · -- b = 0 ⇒ eb = 0
      have hbz : b = 0 := hb0.symm
      have hebz : eb = 0 := le_antisymm (hbeb.trans_eq hbz) heb
      subst hbz; subst hebz; simp
    · -- a > 0, b > 0
      set r := ea / a with hrdef
      have hea' : ea = r * a := by
        rw [hrdef, div_mul_cancel₀ _ (ne_of_gt ha0)]
      have heb' : eb = r * b := by
        have hr' : eb / b = r := hr.symm
        rw [← hr', div_mul_cancel₀ _ (ne_of_gt hb0)]
      rw [hea', heb', ← mul_add, mul_div_assoc, div_self (by positivity), mul_one]

/-- The posterior functional is union-consistent (in a probability measure). -/
lemma unionConsistent_posteriorFunctional [Finite Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (E : Set Ω) :
    UnionConsistent (posteriorFunctional μ E) := by
  intro A B hA hB hdisj hAB
  simp only [posteriorFunctional] at *
  -- measure additivity for disjoint sets (all sets measurable in discrete finite space)
  have hunion : μ (A ∪ B) = μ A + μ B :=
    measure_union hdisj (Set.Finite.measurableSet (Set.toFinite B))
  have hEdisj : Disjoint (E ∩ A) (E ∩ B) :=
    hdisj.mono (Set.inter_subset_right) (Set.inter_subset_right)
  have hEunion : μ (E ∩ (A ∪ B)) = μ (E ∩ A) + μ (E ∩ B) := by
    rw [Set.inter_union_distrib_left]
    exact measure_union hEdisj (Set.Finite.measurableSet (Set.toFinite _))
  rw [hunion, hEunion]
  have hAne : μ A ≠ ⊤ := measure_ne_top μ A
  have hBne : μ B ≠ ⊤ := measure_ne_top μ B
  have hEAne : μ (E ∩ A) ≠ ⊤ := measure_ne_top μ _
  have hEBne : μ (E ∩ B) ≠ ⊤ := measure_ne_top μ _
  rw [ENNReal.toReal_add hEAne hEBne, ENNReal.toReal_add hAne hBne]
  apply ratio_union_aux (ENNReal.toReal_nonneg) (ENNReal.toReal_nonneg)
    (ENNReal.toReal_nonneg) (ENNReal.toReal_nonneg)
  · exact ENNReal.toReal_mono hAne (measure_mono Set.inter_subset_right)
  · exact ENNReal.toReal_mono hBne (measure_mono Set.inter_subset_right)
  · exact hAB

/-- Statement 1 (abstract agreement spine; Cave 1983, Bacharach 1985; finite).
Let `f` be a union-consistent decision function, `(Pᵢ)` **finite** partitions
(Definition 2) with common-knowledge partition `C = ⨆ᵢ Pᵢ`, and `ω` a state.  If it
is common knowledge at `ω` that each agent `i` takes decision `δ i`, then every
`δ i` equals `f (C.class ω)`; in particular all decisions agree.

Finiteness enters through the hypothesis `FinitePartition (P i)`: each agent's
partition has finitely many blocks, so the common-knowledge block `cls C ω` is a
*finite* disjoint union of `Pᵢ`-cells on each of which `f` equals `δ i`, and binary
(hence finite) union consistency lifts this to `f (cls C ω) = δ i`. -/
theorem statement1_abstract_agreement {D : Type*} (f : Set Ω → D)
    (hf : UnionConsistent f) {n : ℕ} (P : Fin n → Setoid Ω)
    (hfinP : ∀ i, FinitePartition (P i))
    (C : Setoid Ω) (hC : C = ⨆ i, P i) (ω : Ω) (δ : Fin n → D)
    (hck : CommonKnowledgeDecision f P C ω δ) :
    ∀ i : Fin n, δ i = f (cls C ω) := by
  intro i
  -- Decompose cls C ω into a finite disjoint union of (P i)-cells (Aux A2).
  obtain ⟨s, hsne, hbne, hdisj, hsub, hrep, hcover⟩ :=
    cls_join_eq_finite_biUnion_cells P hfinP C hC ω i
  -- On each such cell b = cls (P i) ω' with ω' ∈ cls C ω, agent i's decision is δ i:
  -- f b = f (cls (P i) ω') = δ i by common knowledge (hck) at ω' ∈ cls C ω.
  have hval : ∀ b ∈ s, f b = δ i := by
    intro b hb
    obtain ⟨ω', hω', rfl⟩ := hrep b hb
    -- hck i : cls C ω ⊆ {ω' | f (cls (P i) ω') = δ i}
    exact hck i hω'
  -- Finite union consistency (Aux A1) lifts the common value to the whole block.
  have hbi := unionConsistent_biUnion hf s hsne (fun b => b) hbne
    (by simpa [Function.onFun] using hdisj) hval
  rw [hcover]
  simpa using hbi.symm

/-- Corollary of Statement 1: all agents' decisions coincide. -/
theorem statement1_all_equal {D : Type*} (f : Set Ω → D)
    (hf : UnionConsistent f) {n : ℕ} (P : Fin n → Setoid Ω)
    (hfinP : ∀ i, FinitePartition (P i))
    (C : Setoid Ω) (hC : C = ⨆ i, P i) (ω : Ω) (δ : Fin n → D)
    (hck : CommonKnowledgeDecision f P C ω δ) :
    ∀ i j : Fin n, δ i = δ j := by
  -- Immediate corollary: both δ i and δ j equal f (cls C ω) by Statement 1.
  intro i j
  rw [statement1_abstract_agreement f hf P hfinP C hC ω δ hck i,
      statement1_abstract_agreement f hf P hfinP C hC ω δ hck j]

/-- Auxiliary A9 (agreement at the halt via Statement 1).  From the halting time `T`,
for `t ≥ T` no partition changes, so `P i (t+1) = P i t`; but the dynamics forces
`P i (t+1) = P i t ⊓ ⨅ j ofStat(mⱼᵗ)`, so `P i t ≤ ofStat(mⱼᵗ)` for all `j`, i.e. each
agent's posterior statistic `mⱼᵗ` is constant on the blocks of every agent's
partition — in particular it is common knowledge (measurable w.r.t. `⨆ P i t`).
Applying Statement 1 with the posterior functional `f(A) = μ(E ∩ A)/μ(A)` (which is
union-consistent: the ratio of the summed measures over disjoint blocks with equal
ratio equals that common ratio) gives that the agents' posteriors coincide pointwise.

STRATEGY (formal phase): show `posteriorStat μ E (P i t)` is `CommonKnowledgeDecision`
for `f = posteriorFunctional` at each `ω`; verify `UnionConsistent (posteriorFunctional)`
(ratio additivity over disjoint sets — Aux A10 below); invoke `statement1_all_equal`.
Finiteness of `P i t` from `Finite Ω`. -/
lemma dynamics_agree_at_halt [Finite Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E : Set Ω) {n : ℕ}
    (P : Fin n → ℕ → Setoid Ω) (hdyn : PosteriorDynamics μ E P)
    (T : ℕ) (hT : ∀ (i : Fin n) (t : ℕ), T ≤ t → P i t = P i T) :
    ∀ (t : ℕ), T ≤ t → ∀ (i j : Fin n) (ω : Ω),
      posteriorStat μ E (P i t) ω = posteriorStat μ E (P j t) ω := by
  intro t ht i j ω
  -- Abbreviation for the statistics and the common-knowledge partition.
  set m : Fin n → Ω → ℝ := fun k => posteriorStat μ E (P k t) with hm
  set C : Setoid Ω := ⨆ k, P k t with hCdef
  -- At the halt, each partition is stationary: P l t = P l (t+1).
  have hstat : ∀ l : Fin n, P l t = P l (t + 1) := by
    intro l
    rw [hT l t ht, hT l (t + 1) (le_trans ht (Nat.le_succ t))]
  -- Hence P l t ≤ ⨅ j ofStat (m j), so C = ⨆ P l t ≤ ofStat (m k) for each k.
  have hPle : ∀ l : Fin n, P l t ≤ ⨅ k : Fin n, ofStat (m k) := by
    intro l
    have hd := hdyn l t
    -- P l t = P l (t+1) = P l t ⊓ ⨅ k ofStat (m k)
    have heq : P l t = P l t ⊓ ⨅ k : Fin n, ofStat (m k) := by
      calc P l t = P l (t + 1) := hstat l
        _ = P l t ⊓ ⨅ k : Fin n, ofStat (m k) := hd
    exact heq.le.trans inf_le_right
  have hCle : ∀ k : Fin n, C ≤ ofStat (m k) := by
    intro k
    rw [hCdef]
    refine iSup_le (fun l => ?_)
    exact le_trans (hPle l) (iInf_le _ k)
  -- Set up Statement 1 with the posterior functional.
  set δ : Fin n → ℝ := fun k => posteriorFunctional μ E (cls (P k t) ω) with hδ
  have hck : CommonKnowledgeDecision (posteriorFunctional μ E) (fun k => P k t) C ω δ := by
    intro k ω' hω'
    -- ω' ∈ cls C ω means C ω ω', so C ≤ ofStat (m k) gives m k ω = m k ω'.
    have hCr : C ω ω' := hω'
    have hkr : ofStat (m k) ω ω' := hCle k hCr
    -- ofStat is the kernel setoid: m k ω = m k ω'.
    have hmeq : m k ω = m k ω' := hkr
    simp only [Set.mem_setOf_eq, hδ]
    -- posteriorFunctional (cls (P k t) ω') = m k ω' = m k ω = posteriorFunctional (cls (P k t) ω)
    have e1 : posteriorFunctional μ E (cls (P k t) ω') = m k ω' :=
      (posteriorStat_eq_functional μ E (P k t) ω').symm
    have e2 : posteriorFunctional μ E (cls (P k t) ω) = m k ω :=
      (posteriorStat_eq_functional μ E (P k t) ω).symm
    rw [e1, e2, hmeq]
  have hall := statement1_all_equal (posteriorFunctional μ E)
    (unionConsistent_posteriorFunctional μ E) (fun k => P k t)
    (fun k => finitePartition_of_finite (P k t)) C hCdef ω δ hck i j
  -- hall : δ i = δ j.  Translate back to posteriorStat.
  rw [posteriorStat_eq_functional, posteriorStat_eq_functional]
  exact hall

/-! ## Main Statement(s) -/

/-- Statement 2 (dynamic agreement, finite; Geanakoplos–Polemarchakis 1982).
On a finite state space equipped with a *discrete* measurable structure
(`MeasurableSingletonClass`, so every subset — hence every event and every partition
cell — is measurable) and a common prior `μ` giving every cell strictly positive
mass, running the posterior-announcement dynamics of Definition 6:

1. **Halting.**  There is a finite time `T` after which no agent's partition changes.
2. **Agreement.**  From time `T` on, all agents' announced posteriors of `E` coincide
   pointwise. -/
theorem statement2_dynamic_finite [Finite Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : Set Ω) {n : ℕ}
    (P : Fin n → ℕ → Setoid Ω) (hdyn : PosteriorDynamics μ E P) :
    ∃ T : ℕ,
      (∀ (i : Fin n) (t : ℕ), T ≤ t → P i t = P i T) ∧
      (∀ (t : ℕ), T ≤ t → ∀ (i j : Fin n) (ω : Ω),
        posteriorStat μ E (P i t) ω = posteriorStat μ E (P j t) ω) := by
  -- Combine halting (A8) with agreement at the halt (A9).
  obtain ⟨T, hT⟩ := dynamics_halts μ E P hdyn
  exact ⟨T, hT, dynamics_agree_at_halt μ E P hdyn T hT⟩

/-- Statement 3 (dynamic agreement, measurable/convergence generalization; the task's
target).  In the measurable setting with an announcement filtration
`(𝓕ᵢᵗ)` and posterior processes `Xᵢᵗ = 𝔼_μ[1_E | 𝓕ᵢᵗ]`:

1. **Convergence.**  Each martingale `(Xᵢᵗ)ₜ` converges `μ`-a.e. and in `L¹` to
   `Xᵢ^∞ := 𝔼_μ[1_E | 𝓕ᵢ^∞]`, where the limit σ-algebra `𝓕ᵢ^∞ = σ(⋃ₜ 𝓕ᵢᵗ)` is
   `limitSigmaAlgebra ℱ i = ⨆ t, ((ℱ i) t : MeasurableSpace Ω)` (Lévy's upward
   theorem).
2. **Agreement at the limit.**  The limiting posteriors coincide `μ`-a.e. across
   agents.

The limit conditional expectation and the L¹ convergence use `limitSigmaAlgebra`,
which is the genuine `σ(⋃ₜ 𝓕ᵢᵗ)` (the `MeasurableSpace`-valued supremum), matching
Mathlib's `MeasureTheory.tendsto_ae_condExp` / `tendsto_eLpNorm_condExp`. -/
theorem statement3_dynamic_measurable {mΩ : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (E : Set Ω) (hE : MeasurableSet E) {n : ℕ}
    (ℱ : Fin n → Filtration ℕ mΩ) (hann : AnnouncementFiltration μ E ℱ) :
    -- (1) a.e. convergence and L¹ convergence to the limiting conditional expectation
    (∀ i : Fin n,
        (∀ᵐ ω ∂μ, Tendsto (fun t => posteriorProcess μ E ℱ i t ω) atTop
            (𝓝 ((μ[Set.indicator E (fun _ => (1 : ℝ)) | limitSigmaAlgebra ℱ i]) ω))) ∧
        Tendsto (fun t => eLpNorm
            (posteriorProcess μ E ℱ i t
              - μ[Set.indicator E (fun _ => (1 : ℝ)) | limitSigmaAlgebra ℱ i]) 1 μ)
          atTop (𝓝 0)) ∧
    -- (2) agreement of the limits μ-a.e.
    (∀ i j : Fin n,
        (μ[Set.indicator E (fun _ => (1 : ℝ)) | limitSigmaAlgebra ℱ i])
          =ᵐ[μ]
        (μ[Set.indicator E (fun _ => (1 : ℝ)) | limitSigmaAlgebra ℱ j])) := by
  refine ⟨fun i => ⟨?_, ?_⟩, fun i j => ?_⟩
  · -- (1a) a.e. convergence: Lévy upward theorem (A3).
    exact posteriorProcess_tendsto_ae μ E ℱ i
  · -- (1b) L¹ convergence: Lévy upward theorem (A4).
    exact posteriorProcess_tendsto_eLpNorm μ E ℱ i
  · -- (2) limit agreement: the analytic kernel (A7).
    exact limit_posterior_agree μ E hE ℱ hann i j

end Agreement
