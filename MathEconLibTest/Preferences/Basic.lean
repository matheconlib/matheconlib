/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/

import MathEconLib.Matching.Classical.Marriage.Preferences
import MathEconLib.Preferences

/-!
# Preference Orientation and Incomplete Comparisons

These compile-time checks fix the direction of weak preference and exhibit incomplete preferences on
concrete alternatives.

## Checks

* Orientation — `Preference.ofUtility u` ranks `y` above `x` when `u x ≤ u y`, and
  `CompletePreference.ofLinearOrder L` ranks `y` above `x` when `x ≤ y` in `L`.
* Marriage markets — `Matching.MarriageMarket.leM` agrees with the complete preference determined by
  the agent's linear order.
* Incomparability — on `Fin 2`, the vector payoff that pays one in an alternative's own coordinate
  determines a preference under which the two alternatives are incomparable.
* Maximal and greatest alternatives — under the preference given by equality on `Fin 2`, both
  alternatives are maximal, but no alternative is at least as good as every alternative.

## Tags

preference, orientation, incomparability, maximality
-/

set_option linter.privateModule false

namespace MathEconLib.Preferences.Tests

open scoped MathEconLib.Preferences

example {X U : Type*} [Preorder U] (u : X → U) (x y : X) :
    (Preference.ofUtility u).le x y ↔ u x ≤ u y := Iff.rfl

example {X : Type*} (L : LinearOrder X) (x y : X) :
    (CompletePreference.ofLinearOrder L).le x y ↔ L.le x y := Iff.rfl

example {M W : Type*} (mkt : Matching.MarriageMarket M W) (m : M) (y z : Option W) :
    mkt.leM m y z ↔ (CompletePreference.ofLinearOrder (mkt.prefM m)).le y z := Iff.rfl

/-- Each alternative pays one in its own coordinate and zero in the other coordinate. -/
private def vectorPayoff (x : Fin 2) (i : Fin 2) : ℕ := if x = i then 1 else 0

example :
    ¬(0 : Fin 2) ≼[Preference.ofUtility vectorPayoff] 1 ∧
      ¬(1 : Fin 2) ≼[Preference.ofUtility vectorPayoff] 0 := by
  constructor
  · intro h
    exact absurd (h 0) (by decide)
  · intro h
    exact absurd (h 1) (by decide)

/-- Equality regards distinct alternatives as incomparable. -/
private def discretePreference : Preference (Fin 2) where
  le := Eq
  isPreorder := { refl := Eq.refl, trans := fun _ _ _ => Eq.trans }

example (a : Fin 2) : ∀ x, a ≼[discretePreference] x → x ≼[discretePreference] a :=
  fun _ h => h.symm

example : ¬∃ a : Fin 2, ∀ x, x ≼[discretePreference] a := by
  rintro ⟨a, ha⟩
  have h : (0 : Fin 2) = 1 := (ha 0).trans (ha 1).symm
  exact (by decide : (0 : Fin 2) ≠ 1) h

end MathEconLib.Preferences.Tests
