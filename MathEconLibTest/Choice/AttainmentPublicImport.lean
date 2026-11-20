/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
import MathEconLib.Choice

/-!
# Public attainment and nonparticipation interface

Import only the choice umbrella. The predicates unfold to the original greatest-element and
comparison conditions, and the strict and correspondence characterizations require no finite
carrier, decidability, or implicit order on alternatives or bundles.
-/

open MathEconLib.Choice MathEconLib.Choice.ChoiceFunction MathEconLib.Preferences

example {α β : Type*} (pref : LinearOrder β) (bundle : β ↪ Set α) (Y : Set α) :
    HasBundleOptimum pref bundle Y ↔ (letI := pref; ∃ b, IsGreatest {c | bundle c ⊆ Y} b) :=
  Iff.rfl

example {α : Type*} (pref : LinearOrder (Option α)) (Y : Set α) :
    OutsideOptionOptimal pref Y ↔ ∀ x ∈ Y, pref.le (some x) none := Iff.rfl

example {α : Type*} (pref : LinearOrder (Option α)) (Y : Set α) :
    ofOptionLinearOrder pref Y = ∅ ↔
      ¬ HasBundleOptimum pref optionBundle Y ∨ OutsideOptionOptimal pref Y :=
  ofOptionLinearOrder_eq_empty_iff pref Y

example {α : Type*} (pref : LinearOrder (Option α)) {Y : Set α}
    (h : HasBundleOptimum pref optionBundle Y) :
    ofOptionLinearOrder pref Y = ∅ ↔ OutsideOptionOptimal pref Y :=
  ofOptionLinearOrder_eq_empty_iff_of_hasBundleOptimum pref h

example {α β : Type*} (pref : LinearOrder β) (bundle : β ↪ Set α) (Y : Set α) :
    HasBundleOptimum pref bundle Y ↔
      (optimalBundles (Preference.ofPreorder pref.toPreorder) bundle Y).Nonempty :=
  hasBundleOptimum_iff_optimalBundles_nonempty pref bundle Y

example {α : Type*} (pref : LinearOrder (Option α)) (Y : Set α) :
    OutsideOptionOptimal pref Y ↔
      ∅ ∈ optimalBundles (Preference.ofPreorder pref.toPreorder) optionBundle Y :=
  outsideOptionOptimal_iff_empty_mem_optimalBundles pref Y

example {α : Type*} (pref : LinearOrder (Option α)) :
    (ofOptionLinearOrder pref).Consistent ↔ ∀ Y, HasBundleOptimum pref optionBundle Y :=
  consistent_ofOptionLinearOrder_iff_hasBundleOptimum pref
