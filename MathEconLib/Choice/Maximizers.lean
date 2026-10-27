/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.Preferences.Representation.Finite
public import Mathlib.Order.Preorder.Finite

/-!
# Feasible maximizers

`maximizers` retains every greatest feasible alternative under an explicit `Preference`.
Completeness is required only by the finite-existence theorem, through `CompletePreference`.
Value-induced preferences recover feasible `IsMaxOn` witnesses. No choice rule, matching market,
or cardinal representation of arbitrary preferences is required.
-/

@[expose] public section

namespace MathEconLib

open Preferences

namespace Choice

universe u v

variable {α : Type u} {β : Type v}

/-- All greatest feasible alternatives under the supplied preference. -/
def maximizers (pref : Preference α) (S : Set α) : Set α :=
  {a | letI := pref.toPreorder; IsGreatest S a}

@[simp] theorem mem_maximizers (pref : Preference α) {S : Set α} {a : α} :
    a ∈ maximizers pref S ↔ a ∈ S ∧ ∀ b ∈ S, pref.le b a := Iff.rfl

/-- Value-induced maximizers are feasible `IsMaxOn` witnesses. `IsMaxOn` alone does not
require the candidate to belong to the feasible set. -/
theorem mem_maximizers_ofUtility [Preorder β] (value : α → β) {S : Set α} {a : α} :
    a ∈ maximizers (Preference.ofUtility value) S ↔ a ∈ S ∧ IsMaxOn value S a := Iff.rfl

/-- The Mathlib lifted-order form of `mem_maximizers_ofUtility`, using explicit conversion. -/
theorem mem_maximizers_lift [Preorder β] (value : α → β) {S : Set α} {a : α} :
    a ∈ maximizers (Preference.ofPreorder (Preorder.lift value)) S ↔
      a ∈ S ∧ IsMaxOn value S a := mem_maximizers_ofUtility value

theorem maximizers_subset (pref : Preference α) (S : Set α) : maximizers pref S ⊆ S :=
  fun _ h ↦ h.1

@[simp] theorem maximizers_empty (pref : Preference α) : maximizers pref ∅ = ∅ := by
  ext a
  simp

/-- Any two maximizers are indifferent, although they need not be equal. -/
theorem indifferent_of_mem_maximizers (pref : Preference α) {S : Set α} {a b : α}
    (ha : a ∈ maximizers pref S) (hb : b ∈ maximizers pref S) :
    AntisymmRel pref.le a b :=
  ⟨hb.2 ha.1, ha.2 hb.1⟩

/-- A nonempty finite feasible set attains a greatest element under complete preferences. -/
theorem maximizers_nonempty_of_finite (pref : CompletePreference α)
    {S : Set α} (hS : S.Finite) (hne : S.Nonempty) : (maximizers pref S).Nonempty := by
  let := pref.toPreference.toPreorder
  let := pref.isTotal
  obtain ⟨a, ha⟩ := hS.exists_maximal hne
  exact ⟨a, (Std.Total.directedOn S).maximal_iff_isGreatest.mp ha⟩

end Choice

namespace Preferences

variable {α β : Type*}

/-- A represented preference chooses exactly the feasible utility maximizers. -/
theorem Preference.IsRepresentedBy.mem_maximizers_iff
    {R : Preference α} [Preorder β] {value : α → β} (hu : R.IsRepresentedBy value)
    {S : Set α} {a : α} :
    a ∈ Choice.maximizers R S ↔ a ∈ S ∧ IsMaxOn value S a :=
  and_congr_right fun _ ↦ hu.forall_le_iff_isMaxOn

/-- A single natural-number utility represents finite complete-preference choice on every menu. -/
theorem CompletePreference.exists_nat_utility_maximizers [Finite α] (R : CompletePreference α) :
    ∃ value : α → ℕ, ∀ (S : Set α) (a : α),
      a ∈ Choice.maximizers R S ↔ a ∈ S ∧ IsMaxOn value S a := by
  obtain ⟨value, hu⟩ := R.exists_isRepresentedBy_nat
  exact ⟨value, fun _ _ ↦ hu.mem_maximizers_iff⟩

end Preferences

end MathEconLib
