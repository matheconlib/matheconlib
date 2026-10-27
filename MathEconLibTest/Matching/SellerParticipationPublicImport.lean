/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
import MathEconLib.Matching

/-!
# Public seller nonparticipation interface

Import only the matching umbrella. Agent and contract types remain arbitrary, the menu is
restricted to own contracts, and participation statements retain an explicit attainment premise.
-/

open MathEconLib.Choice MathEconLib.Matching

variable {B S X : Type*} (buyer : X → B) (seller : X → S)
    (choiceB : B → ChoiceFunction X)
    (hB : ∀ ⦃b Y x⦄, x ∈ choiceB b Y → buyer x = b)
    (pref : ∀ s, LinearOrder (Option {x : X // seller x = s}))

example (s : S) (Y : Set X) :
    Market.HasSellerOptimum seller pref s Y ↔
      ChoiceFunction.HasBundleOptimum (pref s) ChoiceFunction.optionBundle
        ((Subtype.val : {x : X // seller x = s} → X) ⁻¹' Y) := Iff.rfl

example (s : S) (Y : Set X) :
    Market.Declines seller pref s Y ↔
      ∀ x : {x : X // seller x = s}, (x : X) ∈ Y → (pref s).le (some x) none :=
  Market.declines_iff seller pref s Y

example (s : S) (Y : Set X) :
    (Market.ofSellerPreferences buyer seller choiceB hB pref).choiceS s Y = ∅ ↔
      ¬ Market.HasSellerOptimum seller pref s Y ∨ Market.Declines seller pref s Y :=
  Market.choiceS_ofSellerPreferences_eq_empty_iff buyer seller choiceB hB pref s Y

example (s : S) {Y : Set X} (h : Market.HasSellerOptimum seller pref s Y) :
    (Market.ofSellerPreferences buyer seller choiceB hB pref).choiceS s Y = ∅ ↔
      Market.Declines seller pref s Y :=
  Market.choiceS_ofSellerPreferences_eq_empty_iff_of_hasSellerOptimum
    buyer seller choiceB hB pref s h

example (s : S) {Y : Set X} (h : Market.HasSellerOptimum seller pref s Y) :
    ((Market.ofSellerPreferences buyer seller choiceB hB pref).choiceS s Y).Nonempty ↔
      ¬ Market.Declines seller pref s Y :=
  Market.choiceS_ofSellerPreferences_nonempty_iff_of_hasSellerOptimum
    buyer seller choiceB hB pref s h

example (s : S) {Y : Set X}
    (hY : ((Subtype.val : {x : X // seller x = s} → X) ⁻¹' Y).Finite) :
    Market.HasSellerOptimum seller pref s Y :=
  Market.hasSellerOptimum_of_finite_ownMenu seller pref s hY
