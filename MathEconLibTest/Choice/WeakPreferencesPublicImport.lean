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

open MathEconLib.Choice

variable {α β γ : Type*}

example (pref : Preorder α) (complete : Std.Total pref.le) {S : Set α}
    (hS : S.Finite) (hne : S.Nonempty) : (maximizers pref S).Nonempty :=
  maximizers_nonempty_of_finite pref complete hS hne

example [LinearOrder γ] (pref : LinearOrder β) (priority : β ↪ γ) (bundle : β ↪ Set α) :
    ChoiceFunction.ofWeakBundleOrder pref.toPreorder ⟨pref.le_total⟩ priority bundle =
      ChoiceFunction.ofBundleOrder pref bundle :=
  ChoiceFunction.ofWeakBundleOrder_linearOrder pref priority bundle

example [DecidableEq α] [LinearOrder γ] (pref : Preorder (Option α))
    (complete : Std.Total pref.le) (priority : Option α ↪ γ) (A : Finset α) :
    ChoiceFunction.bestOption (MathEconLib.Order.tieBreakOrder pref complete priority) A ∈
      maximizers pref (ChoiceFunction.optionMenu A : Set (Option α)) :=
  ChoiceFunction.bestOption_mem_maximizers pref complete priority A

end MathEconLibTest.Choice.WeakPreferencesPublicImport
