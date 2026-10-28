/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
import MathEconLib.Choice

/-!
# Value-choice API and boundary checks

The public Choice umbrella supplies the constructor and bundle bridges. The checks distinguish
greatest-element choice from maximal-element choice, preserve ties, and reject infeasible
maximizers. Bundle alternatives stay separate even when their values tie.
-/

namespace MathEconLibTest.Choice.Value

open MathEconLib.Choice MathEconLib.Preferences

example {α V : Type*} [Preorder V] (value : α → V) (S : Set α) :
    ChoiceFunction.ofValue value S = maximizers (Preference.ofUtility value) S := rfl

example {α V : Type*} [Preorder V] (value : α → V) (S : Set α) (a : α) :
    a ∈ ChoiceFunction.ofValue value S ↔ a ∈ S ∧ IsMaxOn value S a :=
  ChoiceFunction.mem_ofValue value

/-- All feasible alternatives survive a constant value, including ties on infinite menus. -/
example {α : Type*} (S : Set α) : ChoiceFunction.ofValue (fun _ : α ↦ (0 : ℕ)) S = S :=
  Set.ext fun _ ↦ by simp [isMaxOn_iff]

/-- An infeasible candidate can satisfy IsMaxOn but cannot belong to value choice. -/
example : IsMaxOn (fun _ : ℕ ↦ (0 : ℕ)) {0} 1 ∧
    1 ∉ ChoiceFunction.ofValue (fun _ : ℕ ↦ (0 : ℕ)) {0} := by
  simp [isMaxOn_iff]

/-- Two incomparable maximal values need not give any greatest feasible alternative. -/
example : ChoiceFunction.ofValue (fun b : Bool ↦ if b then (1, 0) else (0, 1) : Bool → ℕ × ℕ)
    Set.univ = ∅ := by
  ext b
  cases b <;> simp [isMaxOn_iff, Bool.forall_bool, Prod.le_def]

/-- Complete scalar preferences can also fail attainment on an infinite menu. -/
example : ChoiceFunction.ofValue (id : ℕ → ℕ) Set.univ = ∅ :=
  Set.eq_empty_iff_forall_notMem.mpr fun n hn ↦
    (Nat.not_succ_le_self n) (hn.2 (Set.mem_univ (n + 1)))

example {α β V : Type*} [Preorder V] (value : β → V) (bundle : β ↪ Set α) (Y : Set α) :
    optimalBundles (Preference.ofUtility value) bundle Y =
      bundle '' ChoiceFunction.ofValue value {b | bundle b ⊆ Y} :=
  optimalBundles_eq_image_ofValue value bundle Y

/-- Tied singleton bundles remain separate alternatives of the represented choice. -/
example :
    {(0 : Fin 2)} ∈ optimalBundles
      (Preference.ofUtility (fun _ : Option (Fin 2) ↦ (0 : ℕ)))
      ChoiceFunction.optionBundle Set.univ ∧
    {(1 : Fin 2)} ∈ optimalBundles
      (Preference.ofUtility (fun _ : Option (Fin 2) ↦ (0 : ℕ)))
      ChoiceFunction.optionBundle Set.univ :=
  ⟨⟨some 0, ⟨Set.subset_univ _, fun _ _ ↦ (show (0 : ℕ) ≤ 0 from le_rfl)⟩, rfl⟩,
    ⟨some 1, ⟨Set.subset_univ _, fun _ _ ↦ (show (0 : ℕ) ≤ 0 from le_rfl)⟩, rfl⟩⟩

example {α β : Type*} (pref : LinearOrder β) (bundle : β ↪ Set α) (Y : Set α) :
    letI := pref
    ChoiceFunction.ofBundleOrder pref bundle Y =
      ⋃₀ (bundle '' ChoiceFunction.ofValue (id : β → β) {b | bundle b ⊆ Y}) :=
  ChoiceFunction.ofBundleOrder_eq_sUnion_image_ofValue pref bundle Y

#print axioms ChoiceFunction.ofValue
#print axioms ChoiceFunction.mem_ofValue
#print axioms optimalBundles_eq_image_ofValue
#print axioms ChoiceFunction.ofBundleOrder_eq_sUnion_image_ofValue

end MathEconLibTest.Choice.Value
