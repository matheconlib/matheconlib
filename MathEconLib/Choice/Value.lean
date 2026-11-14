/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.Choice.Basic
public import MathEconLib.Choice.Maximizers

/-!
# Value-induced choice

Choose every feasible alternative whose supplied value is weakly above every feasible value.
The constructor uses the shared preference maximizers, so tied alternatives remain separate
choices. Values may lie in any preorder; completeness and existence are not assumed.

This is greatest-element choice, rather than maximal-element choice. Incomparable values can
make choice empty even on a finite nonempty menu. On an infinite menu, choice may also be empty
because the values do not attain a greatest element.

## Main definitions

* `ChoiceFunction.ofValue`: choice induced by a supplied value function.

## Main statements

* `ChoiceFunction.mem_ofValue`: membership is feasibility together with `IsMaxOn`.
-/

@[expose] public section

namespace MathEconLib.Choice.ChoiceFunction

open Preferences

variable {α V : Type*} [Preorder V]

/-- All greatest feasible alternatives under the supplied value function, retaining every tie. -/
def ofValue (value : α → V) : ChoiceFunction α where
  toFun := maximizers (Preference.ofUtility value)
  choose_subset := maximizers_subset (Preference.ofUtility value)

/-- Value-induced choice requires feasibility as well as value maximization. -/
@[simp] theorem mem_ofValue (value : α → V) {S : Set α} {a : α} :
    a ∈ ofValue value S ↔ a ∈ S ∧ IsMaxOn value S a :=
  mem_maximizers_ofUtility value

end MathEconLib.Choice.ChoiceFunction
