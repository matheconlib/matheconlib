/-
Copyright (c) 2026 Scott Duke Kominers, Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Duke Kominers, Bo Cowgill
-/
import Mathlib.Data.PEquiv
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Subsingleton

/-!
# Partial equivalences and functional relations

A `PEquiv` is represented by its graph. Conversely, a relation with at most
one value in each row and each column determines a `PEquiv`. The graph and
reconstruction operations are inverse. No preferences, markets, finiteness,
or decidability assumptions are involved in the graph constructions. The finite-cardinality
lemma below shows that a partial equivalence covering the right side also covers a no-larger
left side.

The existing `PEquiv` is the only matching structure. Its order remains the extension order.
-/

universe u v u' v' u'' v''

namespace PEquiv

variable {α : Type u} {β : Type v}

section Relabel

variable {α' : Type u'} {β' : Type v'} {α'' : Type u''} {β'' : Type v''}

/-- Change the labels of a partial equivalence by composing with total equivalences.
Unmatched arguments remain unmatched. -/
def relabel (μ : α ≃. β) (eα : α ≃ α') (eβ : β ≃ β') : α' ≃. β' :=
  eα.symm.toPEquiv.trans (μ.trans eβ.toPEquiv)

@[simp] theorem relabel_apply (μ : α ≃. β) (eα : α ≃ α') (eβ : β ≃ β') (a : α') :
    μ.relabel eα eβ a = (μ (eα.symm a)).map eβ := by
  change ((μ (eα.symm a)).bind fun b ↦ some (eβ b)) = _
  cases μ (eα.symm a) <;> rfl

@[simp] theorem relabel_symm (μ : α ≃. β) (eα : α ≃ α') (eβ : β ≃ β') :
    (μ.relabel eα eβ).symm = μ.symm.relabel eβ eα := by
  simp only [relabel, symm_trans_rev, ← Equiv.toPEquiv_symm, Equiv.symm_symm,
    trans_assoc]

@[simp] theorem relabel_refl (μ : α ≃. β) :
    μ.relabel (Equiv.refl α) (Equiv.refl β) = μ := by
  simp [relabel]

theorem relabel_trans (μ : α ≃. β) (eα : α ≃ α') (eβ : β ≃ β')
    (fα : α' ≃ α'') (fβ : β' ≃ β'') :
    (μ.relabel eα eβ).relabel fα fβ = μ.relabel (eα.trans fα) (eβ.trans fβ) := by
  ext a
  simp [Option.map_map, Function.comp_def]

end Relabel

/-- A partial equivalence covering the right side also covers the left side when the finite
left side is no larger. -/
theorem isSome_of_forall_symm_isSome_of_card_le [Fintype α] [Fintype β] (μ : α ≃. β)
    (hcard : Fintype.card α ≤ Fintype.card β) (hβ : ∀ b, (μ.symm b).isSome)
    (a : α) : (μ a).isSome := by
  classical
  by_contra ha
  have ha' : μ a = none := Option.not_isSome_iff_eq_none.mp ha
  let f : β → α := fun b ↦ (μ.symm b).get (hβ b)
  have hf (b : β) : μ (f b) = some b :=
    μ.eq_some_iff.mp (Option.some_get (hβ b)).symm
  have hinj : Function.Injective f := by
    intro b c h
    have he := congrArg μ h
    rw [hf b, hf c] at he
    exact Option.some.inj he
  have hnot : a ∉ Set.range f := by
    rintro ⟨b, hba⟩
    have he := hf b
    rw [hba, ha'] at he
    cases he
  exact (Nat.not_lt_of_ge hcard) (Fintype.card_lt_of_injective_of_notMem f hinj hnot)

/-- The graph of a partial equivalence. -/
def graph (μ : α ≃. β) : Set (α × β) :=
  {p | μ p.1 = some p.2}

@[simp] theorem mem_graph {μ : α ≃. β} {a : α} {b : β} :
    (a, b) ∈ μ.graph ↔ μ a = some b :=
  Iff.rfl

theorem mem_graph_symm {μ : α ≃. β} {a : α} {b : β} :
    (a, b) ∈ μ.graph ↔ μ.symm b = some a :=
  μ.eq_some_iff.symm

theorem graph_rightUnique (μ : α ≃. β) {a : α} {b b' : β}
    (hb : (a, b) ∈ μ.graph) (hb' : (a, b') ∈ μ.graph) : b = b' :=
  Option.some.inj (hb.symm.trans hb')

theorem graph_leftUnique (μ : α ≃. β) {a a' : α} {b : β}
    (ha : (a, b) ∈ μ.graph) (ha' : (a', b) ∈ μ.graph) : a = a' :=
  Option.some.inj
    ((mem_graph_symm.mp ha).symm.trans (mem_graph_symm.mp ha'))

theorem graph_injective : Function.Injective (graph : (α ≃. β) → Set (α × β)) := by
  intro μ ν h
  apply PEquiv.ext
  intro a
  have ha : ∀ b, μ a = some b ↔ ν a = some b := by
    intro b
    change (a, b) ∈ μ.graph ↔ (a, b) ∈ ν.graph
    rw [h]
  cases hμ : μ a with
  | none =>
      cases hν : ν a with
      | none => rfl
      | some b =>
          have hbad := (ha b).mpr hν
          rw [hμ] at hbad
          cases hbad
  | some b => exact ((ha b).mp hμ).symm

@[simp] theorem graph_symm (μ : α ≃. β) :
    μ.symm.graph = Prod.swap ⁻¹' μ.graph := by
  ext p
  exact μ.eq_some_iff

/-- An unmatched argument has an empty row in the graph. -/
theorem graph_fiber_fst_eq_empty {μ : α ≃. β} {a : α}
    (hμ : μ a = none) : {p ∈ μ.graph | p.1 = a} = ∅ := by
  ext ⟨a', b⟩
  simp only [Set.mem_setOf_eq, mem_graph, Set.mem_empty_iff_false, iff_false, not_and]
  rintro hp rfl
  rw [hμ] at hp
  contradiction

/-- A matched argument has precisely its matched pair in its graph row. -/
theorem graph_fiber_fst_eq_singleton {μ : α ≃. β} {a : α} {b : β}
    (hμ : μ a = some b) : {p ∈ μ.graph | p.1 = a} = {(a, b)} := by
  ext ⟨a', b'⟩
  change (μ a' = some b' ∧ a' = a) ↔ (a', b') = (a, b)
  rw [Prod.mk.injEq]
  constructor
  · rintro ⟨hp, rfl⟩
    exact ⟨rfl, (Option.some.inj (hμ.symm.trans hp)).symm⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨hμ, rfl⟩

/-- Columns are rows of the inverse partial equivalence, with coordinates swapped. -/
theorem graph_fiber_snd_eq_swap_preimage (μ : α ≃. β) (b : β) :
    {p ∈ μ.graph | p.2 = b} = Prod.swap ⁻¹' {q ∈ μ.symm.graph | q.1 = b} := by
  ext ⟨a', b'⟩
  exact and_congr mem_graph_symm Iff.rfl

theorem graph_fiber_snd_eq_empty {μ : α ≃. β} {b : β}
    (hμ : μ.symm b = none) : {p ∈ μ.graph | p.2 = b} = ∅ := by
  rw [graph_fiber_snd_eq_swap_preimage, graph_fiber_fst_eq_empty hμ, Set.preimage_empty]

theorem graph_fiber_snd_eq_singleton {μ : α ≃. β} {a : α} {b : β}
    (hμ : μ.symm b = some a) : {p ∈ μ.graph | p.2 = b} = {(a, b)} := by
  rw [graph_fiber_snd_eq_swap_preimage, graph_fiber_fst_eq_singleton hμ]
  ext ⟨a', b'⟩
  change (b', a') = (b, a) ↔ (a', b') = (a, b)
  simp only [Prod.mk.injEq, and_comm]

/-- A graph row has zero cardinality exactly at an unmatched argument. -/
theorem ncard_graph_fiber_fst_eq_zero_iff (μ : α ≃. β) (a : α) :
    ({p ∈ μ.graph | p.1 = a} : Set (α × β)).ncard = 0 ↔ μ a = none := by
  cases hμ : μ a with
  | none => rw [graph_fiber_fst_eq_empty hμ]; simp
  | some b => rw [graph_fiber_fst_eq_singleton hμ]; simp

/-- A graph column has zero cardinality exactly at an unmatched inverse argument. -/
theorem ncard_graph_fiber_snd_eq_zero_iff (μ : α ≃. β) (b : β) :
    ({p ∈ μ.graph | p.2 = b} : Set (α × β)).ncard = 0 ↔ μ.symm b = none := by
  cases hμ : μ.symm b with
  | none => rw [graph_fiber_snd_eq_empty hμ]; simp
  | some a => rw [graph_fiber_snd_eq_singleton hμ]; simp

/-- An optional value of a relation at an argument. Uniqueness is imposed
by the correctness lemma and constructor, rather than by the definition. -/
noncomputable def relationValue (r : α → β → Prop) (a : α) : Option β := by
  classical
  exact if h : ∃ b, r a b then some (Classical.choose h) else none

theorem relationValue_eq_some_iff {r : α → β → Prop} {a : α} {b : β}
    (hsub : {b | r a b}.Subsingleton) :
    relationValue r a = some b ↔ r a b := by
  classical
  unfold relationValue
  split_ifs with h
  · constructor
    · intro heq
      have hb : Classical.choose h = b := Option.some.inj heq
      simpa [hb] using Classical.choose_spec h
    · intro hb
      have heq : Classical.choose h = b :=
        hsub (Classical.choose_spec h) hb
      simp [heq]
  · constructor
    · simp
    · intro hb
      exact (h ⟨b, hb⟩).elim

/-- Reconstruct a partial equivalence from a relation functional in both
directions. -/
noncomputable def ofRelation (r : α → β → Prop)
    (hright : ∀ a, {b | r a b}.Subsingleton)
    (hleft : ∀ b, {a | r a b}.Subsingleton) : α ≃. β where
  toFun := relationValue r
  invFun := relationValue (fun b a => r a b)
  inv := fun a b =>
    (relationValue_eq_some_iff (hleft b)).trans
      (relationValue_eq_some_iff (hright a)).symm

@[simp] theorem ofRelation_apply_eq_some_iff
    (r : α → β → Prop)
    (hright : ∀ a, {b | r a b}.Subsingleton)
    (hleft : ∀ b, {a | r a b}.Subsingleton) {a : α} {b : β} :
    ofRelation r hright hleft a = some b ↔ r a b :=
  relationValue_eq_some_iff (hright a)

@[simp] theorem graph_ofRelation (r : α → β → Prop)
    (hright : ∀ a, {b | r a b}.Subsingleton)
    (hleft : ∀ b, {a | r a b}.Subsingleton) :
    (ofRelation r hright hleft).graph = {p | r p.1 p.2} := by
  ext p
  exact ofRelation_apply_eq_some_iff r hright hleft

/-- Reconstructing the graph of an existing partial equivalence recovers it. -/
@[simp] theorem ofRelation_graph (μ : α ≃. β) :
    ofRelation (fun a b => (a, b) ∈ μ.graph)
      (fun _ _ hb _ hb' => μ.graph_rightUnique hb hb')
      (fun _ _ ha _ ha' => μ.graph_leftUnique ha ha') = μ := by
  apply graph_injective
  exact graph_ofRelation _ _ _

end PEquiv
