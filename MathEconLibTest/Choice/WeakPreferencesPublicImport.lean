/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
import MathEconLib.Choice

/-!
# Public weak-preference choice interface

Import only the choice umbrella, so worked examples cannot supply a missing public export.
-/

namespace MathEconLibTest.Choice.WeakPreferencesPublicImport

open MathEconLib.Choice MathEconLib.Preferences

variable {α β γ : Type*}

example [Preorder β] (value : α → β) {S : Set α} {a : α} :
    a ∈ maximizers (Preference.ofUtility value) S ↔ a ∈ S ∧ IsMaxOn value S a :=
  mem_maximizers_ofUtility value

example [Preorder β] (value : α → β) {S : Set α} {a : α} :
    a ∈ maximizers (Preference.ofPreorder (Preorder.lift value)) S ↔
      a ∈ S ∧ IsMaxOn value S a := mem_maximizers_lift value

example (p : Preorder α) {S : Set α} {a : α} :
    a ∈ maximizers (Preference.ofPreorder p) S ↔ (letI := p; IsGreatest S a) := Iff.rfl

example [Preorder β] (value : α → β) :
    Preference.ofPreorder (Preorder.lift value) = Preference.ofUtility value := rfl

example (L : LinearOrder α) (x y : α) :
    (CompletePreference.ofLinearOrder L).le x y ↔ L.le x y := Iff.rfl

example (pref : Preference β) (bundle : β ↪ Set α) {Y A : Set α} :
    A ∈ optimalBundles pref bundle Y ↔
      ∃ b, bundle b = A ∧ bundle b ⊆ Y ∧ ∀ c, bundle c ⊆ Y → pref.le c b :=
  mem_optimalBundles_iff pref bundle

example (pref : Preference β) (refined : LinearOrder β)
    (hrefine : ∀ a b, refined.le a b → pref.le a b) (bundle : β ↪ Set α) {Y : Set α}
    (hF : {b | bundle b ⊆ Y}.Finite) (hne : ∃ b, bundle b ⊆ Y) :
    ChoiceFunction.ofBundleOrder refined bundle Y ∈ optimalBundles pref bundle Y :=
  ChoiceFunction.ofBundleOrder_mem_optimalBundles_of_finite_feasible pref refined hrefine
    bundle hF hne

example [LinearOrder γ] (pref : CompletePreference (Option α))
    (priority : Option α ↪ γ) :
    (ChoiceFunction.ofWeakBundleOrder pref priority
      ChoiceFunction.optionBundle).UnitDemand :=
  ChoiceFunction.unitDemand_ofOptionLinearOrder
    (pref.tieBreak priority)

example (pref : CompletePreference α) {S : Set α}
    (hS : S.Finite) (hne : S.Nonempty) : (maximizers pref S).Nonempty :=
  maximizers_nonempty_of_finite pref hS hne

example [LinearOrder γ] (pref : LinearOrder β) (priority : β ↪ γ) (bundle : β ↪ Set α) :
    ChoiceFunction.ofWeakBundleOrder (CompletePreference.ofLinearOrder pref) priority bundle =
      ChoiceFunction.ofBundleOrder pref bundle :=
  ChoiceFunction.ofWeakBundleOrder_linearOrder pref priority bundle

example [DecidableEq α] [LinearOrder γ] (pref : CompletePreference (Option α))
    (priority : Option α ↪ γ) (A : Finset α) :
    ChoiceFunction.bestOption (pref.tieBreak priority) A ∈
      maximizers pref (ChoiceFunction.optionMenu A : Set (Option α)) :=
  ChoiceFunction.bestOption_mem_maximizers pref priority A

example (R : Preference α) [Preorder β] (value : α → β) (hu : R.IsRepresentedBy value)
    {S : Set α} {a : α} :
    a ∈ maximizers R S ↔ a ∈ S ∧ IsMaxOn value S a := hu.mem_maximizers_iff

example [Finite α] (R : CompletePreference α) :
    ∃ value : α → ℕ, ∀ (S : Set α) (a : α),
      a ∈ maximizers R S ↔ a ∈ S ∧ IsMaxOn value S a :=
  R.exists_nat_utility_maximizers

example [LinearOrder γ] (pref : CompletePreference β) (priority : β ↪ γ)
    {S : Set β} {b : β} :
    b ∈ maximizers (Preference.ofPreorder (pref.tieBreak priority).toPreorder) S ↔
      b ∈ maximizers pref.toPreference S ∧
        ∀ c ∈ maximizers pref.toPreference S, priority c ≤ priority b :=
  mem_maximizers_tieBreak_iff pref priority

example [LinearOrder γ] (pref : CompletePreference β) (priority : β ↪ γ)
    (bundle : β ↪ Set α) {Y A : Set α} :
    A ∈ optimalBundles (Preference.ofPreorder (pref.tieBreak priority).toPreorder) bundle Y ↔
      ∃ b, b ∈ maximizers pref.toPreference {c | bundle c ⊆ Y} ∧ bundle b = A ∧
        ∀ c ∈ maximizers pref.toPreference {d | bundle d ⊆ Y}, priority c ≤ priority b :=
  mem_optimalBundles_tieBreak_iff pref priority bundle

example [LinearOrder γ] (pref : CompletePreference β) (priority : β ↪ γ)
    (bundle : β ↪ Set α) (Y : Set α) :
    (optimalBundles (Preference.ofPreorder (pref.tieBreak priority).toPreorder) bundle Y).Nonempty ↔
      ∃ p, IsGreatest (priority '' maximizers pref.toPreference {b | bundle b ⊆ Y}) p :=
  optimalBundles_tieBreak_nonempty_iff pref priority bundle Y

example (pref : LinearOrder β) (bundle : β ↪ Set α) (Y : Set α) :
    optimalBundles (Preference.ofPreorder pref.toPreorder) bundle Y ⊆
      {ChoiceFunction.ofBundleOrder pref bundle Y} :=
  optimalBundles_subset_ofBundleOrder pref bundle Y

example (pref : Preference β) (refined : LinearOrder β)
    (hrefine : ∀ a b, refined.le a b → pref.le a b) (bundle : β ↪ Set α) {Y : Set α}
    (hne : (maximizers (Preference.ofPreorder refined.toPreorder) {b | bundle b ⊆ Y}).Nonempty) :
    ChoiceFunction.ofBundleOrder refined bundle Y ∈ optimalBundles pref bundle Y :=
  ChoiceFunction.ofBundleOrder_mem_optimalBundles_of_maximizers_nonempty
    pref refined hrefine bundle hne

example [LinearOrder γ] (pref : CompletePreference β) (priority : β ↪ γ)
    (bundle : β ↪ Set α) {Y : Set α} {b : β}
    (hb : b ∈ maximizers (Preference.ofPreorder (pref.tieBreak priority).toPreorder)
      {c | bundle c ⊆ Y}) :
    ChoiceFunction.ofWeakBundleOrder pref priority bundle Y = bundle b :=
  ChoiceFunction.ofWeakBundleOrder_eq_of_mem_maximizers pref priority bundle hb

example [LinearOrder γ] (pref : CompletePreference β) (priority : β ↪ γ)
    (bundle : β ↪ Set α) {Y : Set α}
    (hne : (maximizers (Preference.ofPreorder (pref.tieBreak priority).toPreorder)
      {b | bundle b ⊆ Y}).Nonempty) :
    ChoiceFunction.ofWeakBundleOrder pref priority bundle Y ∈
      optimalBundles pref.toPreference bundle Y :=
  ChoiceFunction.ofWeakBundleOrder_mem_optimalBundles_of_maximizers_nonempty
    pref priority bundle hne

example [LinearOrder γ] (pref : CompletePreference β) (priority : β ↪ γ)
    (bundle : β ↪ Set α) {Y : Set α}
    (hfinite : (maximizers pref.toPreference {b | bundle b ⊆ Y}).Finite)
    (hne : (optimalBundles pref.toPreference bundle Y).Nonempty) :
    ChoiceFunction.ofWeakBundleOrder pref priority bundle Y ∈
      optimalBundles pref.toPreference bundle Y :=
  ChoiceFunction.ofWeakBundleOrder_mem_optimalBundles_of_finite_maximizers
    pref priority bundle hfinite hne

example [LinearOrder γ] [WellFoundedGT γ] (pref : CompletePreference β) (priority : β ↪ γ)
    (bundle : β ↪ Set α) {Y : Set α}
    (hne : (optimalBundles pref.toPreference bundle Y).Nonempty) :
    ChoiceFunction.ofWeakBundleOrder pref priority bundle Y ∈
      optimalBundles pref.toPreference bundle Y :=
  ChoiceFunction.ofWeakBundleOrder_mem_optimalBundles_of_wellFoundedGT pref priority bundle hne

#print axioms mem_maximizers_ofUtility
#print axioms Preference.IsRepresentedBy.mem_maximizers_iff
#print axioms CompletePreference.exists_nat_utility_maximizers
#print axioms CompletePreference.tieBreak_le_iff
#print axioms CompletePreference.tieBreak_ofLinearOrder
#print axioms mem_maximizers_tieBreak_iff
#print axioms maximizers_tieBreak_nonempty_iff
#print axioms optimalBundles_subset_ofBundleOrder
#print axioms ChoiceFunction.ofBundleOrder_mem_optimalBundles_of_maximizers_nonempty
#print axioms ChoiceFunction.ofWeakBundleOrder_mem_optimalBundles_of_wellFoundedGT

end MathEconLibTest.Choice.WeakPreferencesPublicImport
