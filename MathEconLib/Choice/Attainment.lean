/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
import MathEconLib.Choice.WeakPreferences

/-!
# Attainment and optimal-bundle correspondences

Relate the strict-choice predicates from `Choice.Induced` to the shared optimum correspondence.
This module imports weak-preference choice; the strict constructors do not depend on it.
The public entry point is `MathEconLib.Choice`.

## Main statements

* `ChoiceFunction.hasBundleOptimum_iff_optimalBundles_nonempty`: strict attainment is
  nonemptiness of the optimum correspondence under the supplied linear order.
* `ChoiceFunction.outsideOptionOptimal_iff_empty_mem_optimalBundles`: outside-option optimality
  is membership of the empty bundle in the option correspondence.

Apply these bridges to the priority-refined order to describe the selected participation decision.
Weak correspondence nonemptiness alone does not imply refined attainment, and weak optimality of
the empty bundle alone does not determine which tied option a priority selects.
-/

namespace MathEconLib.Choice.ChoiceFunction

open Preferences

universe u v

variable {α : Type u} {β : Type v}

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

end MathEconLib.Choice.ChoiceFunction
