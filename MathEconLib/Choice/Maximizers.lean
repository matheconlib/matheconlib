/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import Mathlib.Order.Antisymmetrization
public import Mathlib.Order.Filter.Extr
public import Mathlib.Order.Preorder.Finite

/-!
# Feasible maximizers

`maximizers` retains every greatest feasible alternative under an explicit preorder.
Value-induced preferences recover feasible `IsMaxOn` witnesses. No choice rule, matching market,
or cardinal representation of arbitrary preferences is required.
-/

@[expose] public section

namespace MathEconLib.Choice

universe u v

variable {α : Type u} {β : Type v}

/-- All greatest feasible alternatives under the supplied preorder. -/
def maximizers (pref : Preorder α) (S : Set α) : Set α :=
  {a | letI := pref; IsGreatest S a}

@[simp] theorem mem_maximizers (pref : Preorder α) {S : Set α} {a : α} :
    a ∈ maximizers pref S ↔ a ∈ S ∧ ∀ b ∈ S, pref.le b a := Iff.rfl

/-- Value-induced maximizers are feasible `IsMaxOn` witnesses. `IsMaxOn` alone does not
require the candidate to belong to the feasible set. -/
theorem mem_maximizers_lift [Preorder β] (value : α → β) {S : Set α} {a : α} :
    a ∈ maximizers (Preorder.lift value) S ↔ a ∈ S ∧ IsMaxOn value S a := Iff.rfl

theorem maximizers_subset (pref : Preorder α) (S : Set α) : maximizers pref S ⊆ S :=
  fun _ h ↦ h.1

@[simp] theorem maximizers_empty (pref : Preorder α) : maximizers pref ∅ = ∅ := by
  ext a
  simp

/-- Any two maximizers are indifferent, although they need not be equal. -/
theorem indifferent_of_mem_maximizers (pref : Preorder α) {S : Set α} {a b : α}
    (ha : a ∈ maximizers pref S) (hb : b ∈ maximizers pref S) :
    AntisymmRel pref.le a b :=
  ⟨hb.2 ha.1, ha.2 hb.1⟩

/-- A nonempty finite feasible set attains a greatest element under complete preferences. -/
theorem maximizers_nonempty_of_finite (pref : Preorder α) (complete : Std.Total pref.le)
    {S : Set α} (hS : S.Finite) (hne : S.Nonempty) : (maximizers pref S).Nonempty := by
  let := pref
  let := complete
  obtain ⟨a, ha⟩ := hS.exists_maximal hne
  exact ⟨a, (Std.Total.directedOn S).maximal_iff_isGreatest.mp ha⟩

end MathEconLib.Choice
