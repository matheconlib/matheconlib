/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.Preferences.Representation.Finite
public import MathEconLib.Preferences.Refinement
public import Mathlib.Order.Preorder.Finite

/-!
# Feasible maximizers

Retain every greatest feasible alternative under an explicit `Preference`, including incomplete
preferences. Finite existence and fixed tie-breaking use `CompletePreference` to supply totality.
The interface is independent of bundle representations and matching markets.

## Main definitions

* `maximizers`: the set of Mathlib `IsGreatest` witnesses on the feasible set.

## Main statements

* `mem_maximizers`: feasibility and weak comparison with every feasible alternative.
* `mem_maximizers_ofUtility`: utility-induced maximizers are precisely feasible `IsMaxOn`
  witnesses. Mathlib's `IsMaxOn` alone does not require the candidate to be feasible.
* `Preference.IsRepresentedBy.mem_maximizers_iff`: the same characterization for a supplied
  ordinal utility representation.
* `CompletePreference.exists_nat_utility_maximizers`: on a finite carrier, one natural-number
  utility describes maximizers on every feasible set.
* `maximizers_nonempty_of_finite`: a finite nonempty feasible set attains under completeness.
* `mem_maximizers_tieBreak_iff`: refined maximizers are weak maximizers with highest priority
  among weak maximizers.
* `maximizers_tieBreak_nonempty_iff`: refined attainment is greatest-value attainment in the
  priority image of the weak-maximizer set.

## Inputs and attainment

Use `Preference.ofPreorder` for an existing Mathlib preorder and `Preference.ofUtility` for a
supplied value function into any preordered type. `CompletePreference.ofPreorder` packages an
order and totality proof; `CompletePreference.ofUtility` uses a total utility preorder. A
complete preference coerces to `Preference`, with `.toPreference` available for explicit typing.
These ordinal choice results do not impose cardinal or welfare comparisons across different
representing utilities.

Finiteness alone is insufficient for incomplete preferences: maximal alternatives need not be
greatest. On infinite sets, even a complete preference can fail attainment. Fixed tie-breaking
can also lose attainment when weak maximizers exist but have no greatest priority. A finite
nonempty weak-maximizer set suffices by `maximizers_tieBreak_nonempty_of_finite`.
Under `WellFoundedGT` on the priority codomain, refined and weak attainment are equivalent by
`maximizers_tieBreak_nonempty_iff_of_wellFoundedGT`; original weak attainment remains necessary.
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

/-- Refinement retains precisely the weak maximizers with highest priority among weak maximizers. -/
theorem mem_maximizers_tieBreak_iff [LinearOrder β] (pref : CompletePreference α)
    (priority : α ↪ β) {S : Set α} {a : α} :
    a ∈ maximizers (Preference.ofPreorder (pref.tieBreak priority).toPreorder) S ↔
      a ∈ maximizers pref.toPreference S ∧
        ∀ b ∈ maximizers pref.toPreference S, priority b ≤ priority a :=
  Order.isGreatest_tieBreakOrder_iff pref.toPreference.toPreorder pref.isTotal priority

/-- Refined maximizers exist exactly when priorities attain a greatest value on weak maximizers. -/
theorem maximizers_tieBreak_nonempty_iff [LinearOrder β] (pref : CompletePreference α)
    (priority : α ↪ β) (S : Set α) :
    (maximizers (Preference.ofPreorder (pref.tieBreak priority).toPreorder) S).Nonempty ↔
      ∃ p, IsGreatest (priority '' maximizers pref.toPreference S) p :=
  Order.exists_isGreatest_tieBreakOrder_iff pref.toPreference.toPreorder pref.isTotal priority S

/-- A finite nonempty weak-maximizer set suffices even when the feasible set is infinite. -/
theorem maximizers_tieBreak_nonempty_of_finite [LinearOrder β] (pref : CompletePreference α)
    (priority : α ↪ β) {S : Set α} (hfinite : (maximizers pref.toPreference S).Finite)
    (hne : (maximizers pref.toPreference S).Nonempty) :
    (maximizers (Preference.ofPreorder (pref.tieBreak priority).toPreorder) S).Nonempty :=
  Order.exists_isGreatest_tieBreakOrder_of_finite
    pref.toPreference.toPreorder pref.isTotal priority hfinite hne

/-- Well-founded strict priority improvement preserves existing weak attainment. -/
theorem maximizers_tieBreak_nonempty_of_wellFoundedGT [LinearOrder β] [WellFoundedGT β]
    (pref : CompletePreference α) (priority : α ↪ β) {S : Set α}
    (hne : (maximizers pref.toPreference S).Nonempty) :
    (maximizers (Preference.ofPreorder (pref.tieBreak priority).toPreorder) S).Nonempty :=
  Order.exists_isGreatest_tieBreakOrder_of_wellFoundedGT
    pref.toPreference.toPreorder pref.isTotal priority hne

/-- With well-founded strict priority improvement, refined and weak attainment are equivalent. -/
theorem maximizers_tieBreak_nonempty_iff_of_wellFoundedGT [LinearOrder β] [WellFoundedGT β]
    (pref : CompletePreference α) (priority : α ↪ β) (S : Set α) :
    (maximizers (Preference.ofPreorder (pref.tieBreak priority).toPreorder) S).Nonempty ↔
      (maximizers pref.toPreference S).Nonempty :=
  Order.exists_isGreatest_tieBreakOrder_iff_of_wellFoundedGT
    pref.toPreference.toPreorder pref.isTotal priority S

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
