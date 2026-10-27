/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/

module

import MathEconLib.Preferences
import Mathlib.Basic.Real.Basic

/-!
# Complete Preferences with Ties

These compile-time checks exercise complete preferences whose weak comparison is not antisymmetric,
so that distinct alternatives can be indifferent.

## Checks

* Coercion — a `CompletePreference` is total and inherits reflexivity from `Preference`.
* Utility scales — `CompletePreference.ofUtility` accepts natural-number and real-valued utilities.
* Constant maps — `CompletePreference.comap` along a constant map makes the two alternatives of
  `Fin 2` indifferent, so it does not preserve antisymmetry.
* Total preorders — scores compared by their integer halves form a total preorder that is not
  antisymmetric, and the preference they determine makes the distinct scores `0` and `1`
  indifferent.

## Tags

complete preference, total preorder, utility, indifference
-/

set_option linter.privateModule false

namespace MathEconLib.Preferences.Tests

open scoped MathEconLib.Preferences

example {X : Type*} (R : CompletePreference X) (x y : X) :
    x ≼[R] y ∨ y ≼[R] x := R.total x y

example {X : Type*} (R : CompletePreference X) (x : X) : x ≼[R] x :=
  Preference.le_refl R x

example {X : Type*} (u : X → ℕ) : CompletePreference X := CompletePreference.ofUtility u

example {X : Type*} (u : X → ℝ) : CompletePreference X := CompletePreference.ofUtility u

example :
    ¬Std.Antisymm
      ((CompletePreference.ofLinearOrder (inferInstance : LinearOrder (Fin 2))).comap
        (fun _ : Fin 2 => (0 : Fin 2))).le := by
  intro h
  have h01 : (0 : Fin 2) = 1 := h.antisymm 0 1 (by change (0 : Fin 2) ≤ 0; exact le_rfl)
    (by change (0 : Fin 2) ≤ 0; exact le_rfl)
  exact (by decide : (0 : Fin 2) ≠ 1) h01

/-- Scores whose preference compares the integer half of the stored natural number. -/
private structure HalfScore where
  n : ℕ

private instance : Preorder HalfScore := Preorder.lift (fun x => x.n / 2)

private instance : Std.Total (α := HalfScore) (· ≤ ·) :=
  ⟨fun x y => le_total (x.n / 2) (y.n / 2)⟩

example : ¬Std.Antisymm (α := HalfScore) (· ≤ ·) := by
  intro h
  have heq : (⟨0⟩ : HalfScore) = ⟨1⟩ := h.antisymm ⟨0⟩ ⟨1⟩ (by decide) (by decide)
  have h01 : (0 : ℕ) = 1 := congrArg HalfScore.n heq
  exact (by decide : (0 : ℕ) ≠ 1) h01

example : CompletePreference HalfScore := CompletePreference.ofUtility id

example : (⟨0⟩ : HalfScore) ~[CompletePreference.ofUtility (id : HalfScore → HalfScore)] ⟨1⟩ :=
  ⟨by change (0 : ℕ) / 2 ≤ 1 / 2; decide, by change (1 : ℕ) / 2 ≤ 0 / 2; decide⟩

end MathEconLib.Preferences.Tests
