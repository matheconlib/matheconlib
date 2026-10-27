/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
import MathEconLib.Choice
import MathEconLib.GameTheory.Strategic.Basic

/-!
# Weak-preference maximizers in an existing strategic game

The value-induced maximizer API expresses the existing Nash condition, retaining all tied
best responses. This checks the shared mathematics behind #177 without introducing a second
best-response definition or implementing that issue's broader interface.
-/

namespace MathEconLibTest.Choice.WeakPreferencesGame

open MathEconLib.Choice MathEconLib.GameTheory MathEconLib.Preferences

example {I : Type*} {A : I → Type*} {V : Type*} [DecidableEq I] [Preorder V]
    (G : StrategicGame I A V) (a : ∀ i, A i) :
    G.IsNash a ↔ ∀ i, a i ∈
      maximizers (Preference.ofUtility fun s ↦ G.payoff i (Function.update a i s)) Set.univ := by
  simp only [mem_maximizers_ofUtility, Set.mem_univ, true_and, isMaxOn_univ_iff,
    Function.update_eq_self, StrategicGame.isNash_iff]

end MathEconLibTest.Choice.WeakPreferencesGame
