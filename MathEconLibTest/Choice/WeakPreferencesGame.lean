/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
import MathEconLib.Choice
import MathEconLib.GameTheory.Choice

/-!
# Weak-preference maximizers in an existing strategic game

The value-induced maximizer API expresses the existing Nash condition while retaining all tied
best responses.
-/

namespace MathEconLibTest.Choice.WeakPreferencesGame

open MathEconLib.Choice MathEconLib.GameTheory MathEconLib.Preferences

example {I : Type*} {A : I → Type*} {V : Type*} [DecidableEq I] [Preorder V]
    (G : StrategicGame I A V) (a : ∀ i, A i) :
    G.IsNash a ↔ ∀ i, a i ∈
      maximizers (Preference.ofUtility fun s ↦ G.payoff i (Function.update a i s)) Set.univ :=
  StrategicGame.isNash_iff_mem_bestResponses G a

end MathEconLibTest.Choice.WeakPreferencesGame
