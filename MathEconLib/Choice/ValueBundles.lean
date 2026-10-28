/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.Choice.Value
public import MathEconLib.Choice.WeakPreferences

/-!
# Value choice and represented bundles

Treat each represented bundle as one alternative. Value-induced choice of feasible bundle indices
agrees with the shared optimal-bundle correspondence. Tied bundles remain separate members of that
correspondence, rather than being combined into a chosen bundle.

For a linear order, the existing strict bundle constructor equals the union of the represented
greatest indices. Antisymmetry permits at most one such index. If no greatest index exists, both
constructions give an empty union; that does not certify optimality of an outside option.

## Main statements

* `optimalBundles_eq_image_ofValue`: represented value choice agrees with preference choice.
* `ChoiceFunction.ofBundleOrder_eq_sUnion_image_ofValue`: agreement with strict bundle choice.
-/

@[expose] public section

namespace MathEconLib.Choice

open Preferences

variable {α β V : Type*}

/-- Represented value choices retain each tied bundle as a separate alternative. -/
theorem optimalBundles_eq_image_ofValue [Preorder V] (value : β → V)
    (bundle : β ↪ Set α) (Y : Set α) :
    optimalBundles (Preference.ofUtility value) bundle Y =
      bundle '' ChoiceFunction.ofValue value {b | bundle b ⊆ Y} := rfl

/-- Strict bundle choice is the union of the represented greatest feasible indices. -/
theorem ChoiceFunction.ofBundleOrder_eq_sUnion_image_ofValue (pref : LinearOrder β)
    (bundle : β ↪ Set α) (Y : Set α) :
    letI := pref
    ofBundleOrder pref bundle Y = ⋃₀ (bundle '' ofValue (id : β → β) {b | bundle b ⊆ Y}) :=
  Set.ext fun _ ↦
    ⟨fun ⟨b, hb, hx, hmax⟩ ↦ ⟨bundle b, ⟨b, ⟨hb, hmax⟩, rfl⟩, hx⟩,
      fun ⟨_, ⟨b, hb, rfl⟩, hx⟩ ↦ ⟨b, hb.1, hx, hb.2⟩⟩

end MathEconLib.Choice
