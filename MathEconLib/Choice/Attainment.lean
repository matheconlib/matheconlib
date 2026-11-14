/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.Choice.Value
public import MathEconLib.Choice.WeakPreferences

/-!
# Attainment and optimal-bundle correspondences

Relate strict choice and value-induced choice to the shared optimum correspondence. Each
represented bundle is one alternative, so value ties remain separate in the correspondence.

## Main statements

* `ChoiceFunction.hasBundleOptimum_iff_optimalBundles_nonempty`: strict attainment is
  nonemptiness of the optimum correspondence under the supplied linear order.
* `ChoiceFunction.outsideOptionOptimal_iff_empty_mem_optimalBundles`: outside-option optimality
  is membership of the empty bundle in the option correspondence.
* `optimalBundles_eq_image_ofValue`: value-induced choice of bundle indices gives the
  optimal-bundle correspondence.
* `ChoiceFunction.ofBundleOrder_eq_sUnion_optimalBundles`: the strict selector is the union of
  the optimum correspondence for its linear order.

Apply these bridges to the priority-refined order to describe the selected participation decision.
Weak correspondence nonemptiness alone does not imply refined attainment, and weak optimality of
the empty bundle alone does not determine which tied option a priority selects.
-/

public section

namespace MathEconLib.Choice

open Preferences

universe u v

variable {α : Type u} {β : Type v} {V : Type*}

/-- Represented value choices retain each tied bundle as a separate alternative. -/
theorem optimalBundles_eq_image_ofValue [Preorder V] (value : β → V)
    (bundle : β ↪ Set α) (Y : Set α) :
    optimalBundles (Preference.ofUtility value) bundle Y =
      bundle '' ChoiceFunction.ofValue value {b | bundle b ⊆ Y} := rfl

namespace ChoiceFunction

/-- The strict bundle selector is the union of its optimum correspondence.
Antisymmetry permits at most one greatest index. If none exists, the union is empty.
For option bundles, `OutsideOptionOptimal` separately certifies that staying out is optimal. -/
theorem ofBundleOrder_eq_sUnion_optimalBundles (pref : LinearOrder β)
    (bundle : β ↪ Set α) (Y : Set α) :
    ofBundleOrder pref bundle Y =
      ⋃₀ (optimalBundles (CompletePreference.ofLinearOrder pref) bundle Y) :=
  Set.ext fun _ ↦
    ⟨fun ⟨b, hb, hx, hmax⟩ ↦ ⟨bundle b, ⟨b, ⟨hb, hmax⟩, rfl⟩, hx⟩,
      fun ⟨_, ⟨b, hb, rfl⟩, hx⟩ ↦ ⟨b, hb.1, hx, hb.2⟩⟩

/-- Express strict bundle choice in terms of value-induced choice of represented indices. -/
theorem ofBundleOrder_eq_sUnion_image_ofValue (pref : LinearOrder β)
    (bundle : β ↪ Set α) (Y : Set α) :
    letI := pref
    ofBundleOrder pref bundle Y = ⋃₀ (bundle '' ofValue (id : β → β) {b | bundle b ⊆ Y}) := by
  let := pref
  calc
    ofBundleOrder pref bundle Y =
        ⋃₀ (optimalBundles (CompletePreference.ofLinearOrder pref) bundle Y) :=
      ofBundleOrder_eq_sUnion_optimalBundles pref bundle Y
    _ = ⋃₀ (bundle '' ofValue (id : β → β) {b | bundle b ⊆ Y}) :=
      congrArg Set.sUnion (optimalBundles_eq_image_ofValue (id : β → β) bundle Y)

/-- Strict bundle attainment is exactly nonemptiness of its optimum correspondence. -/
theorem hasBundleOptimum_iff_optimalBundles_nonempty (pref : LinearOrder β)
    (bundle : β ↪ Set α) (Y : Set α) :
    HasBundleOptimum pref bundle Y ↔
      (optimalBundles (Preference.ofPreorder pref.toPreorder) bundle Y).Nonempty :=
  (optimalBundles_nonempty_iff (Preference.ofPreorder pref.toPreorder) bundle Y).symm

/-- Strict outside-option optimality is exactly optimality of the represented empty bundle. -/
theorem outsideOptionOptimal_iff_empty_mem_optimalBundles (pref : LinearOrder (Option α))
    (Y : Set α) :
    OutsideOptionOptimal pref Y ↔
      ∅ ∈ optimalBundles (Preference.ofPreorder pref.toPreorder) optionBundle Y :=
  ⟨fun h ↦ (mem_optimalBundles_iff _ optionBundle).mpr
    ⟨none, rfl, h.isGreatest.1, fun _ ho ↦ h.isGreatest.2 ho⟩,
    fun h ↦
      let ⟨b, heq, _, hmax⟩ := (mem_optimalBundles_iff _ optionBundle).mp h
      have hbnone : b = none := optionBundle.injective heq
      fun x hx ↦ hbnone ▸ hmax (some x) (Set.singleton_subset_iff.mpr hx)⟩

end ChoiceFunction

end MathEconLib.Choice

end
