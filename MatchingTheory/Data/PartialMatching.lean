import Mathlib.Data.PEquiv
import Mathlib.Data.Set.Subsingleton

/-!
# Partial equivalences and functional relations

A `PEquiv` is represented by its graph. Conversely, a relation with at most
one value in each row and each column determines a `PEquiv`. The graph and
reconstruction operations are inverse. No preferences, markets, finiteness,
or decidability assumptions are involved.

The existing `PEquiv` is the only matching structure: these are constructors
and graph lemmas for it. Its existing order remains the extension order.
-/

universe u v

namespace PEquiv

variable {α : Type u} {β : Type v}

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
