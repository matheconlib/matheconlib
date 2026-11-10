/-
Copyright (c) 2026 Ritik Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ritik Jain
-/
module

import MathEconLib.Preferences
import Mathlib.Data.Fin.VecNotation

/-!
# Preference Profiles: Examples

These checks apply the profile operations and the new representation results to small finite
examples, through the umbrella import `MathEconLib.Preferences`.

## Checks

* Utility — Osborne and Rubinstein's Example 1.1, a complete preference with an indifference given
  by an integer utility, and a real-valued representation of it.
* Profiles — a profile of three agents with cyclic strict rankings, its reindexing along a
  non-injective map, and a relabelling of the alternatives.

## References

* Martin J. Osborne and Ariel Rubinstein (2023), *Models in Microeconomic Theory*, Example 1.1.
-/

set_option linter.privateModule false

namespace MathEconLib.Preferences.Tests

open scoped MathEconLib.Preferences

/-- Osborne and Rubinstein's Example 1.1: `a ≻ b ∼ c ≻ d`, with `u = (5, -1, -1, -17)`. -/
example : (1 : Fin 4) ≺[CompletePreference.ofUtility ![(5 : ℤ), -1, -1, -17]] 0 ∧
    (1 : Fin 4) ~[CompletePreference.ofUtility ![(5 : ℤ), -1, -1, -17]] 2 ∧
    (3 : Fin 4) ≺[CompletePreference.ofUtility ![(5 : ℤ), -1, -1, -17]] 2 := by
  simp

/-- A strictly increasing transformation of the utility of Example 1.1 represents the same
preference. -/
example : (CompletePreference.ofUtility ![(5 : ℤ), -1, -1, -17]).IsRepresentedBy
    ((fun t : ℤ => 2 * t + 3) ∘ ![(5 : ℤ), -1, -1, -17]) :=
  (Preference.isRepresentedBy_ofUtility ![(5 : ℤ), -1, -1, -17]).comp_strictMono
    fun s t (hst : s < t) => show 2 * s + 3 < 2 * t + 3 by omega

example : ∃ u : Fin 4 → ℝ,
    (CompletePreference.ofUtility ![(5 : ℤ), -1, -1, -17]).IsRepresentedBy u :=
  CompletePreference.exists_isRepresentedBy_real _

/-- Three agents with cyclic strict rankings of three alternatives: agent `i` ranks `x` by
`x - i`. -/
def cyclic : Profile (Fin 3) fun _ => Fin 3 :=
  Profile.ofUtility fun i x => x - i

/-- Agent `0` ranks `2` above `0`. -/
example : (0 : Fin 3) ≺[cyclic 0] 2 := by
  simp [cyclic]

example (i : Fin 3) : Std.Antisymm (cyclic i).le :=
  ⟨fun (x y : Fin 3) hxy hyx => by
    simp only [cyclic, Profile.ofUtility_apply, CompletePreference.toPreference_ofUtility,
      Preference.ofUtility_le_iff] at hxy hyx
    revert i x y
    decide⟩

/-- Reindexing along a constant map gives every new agent the preference of agent `0`. -/
example (j : Fin 2) : cyclic.reindexAgents (fun _ => 0) j = cyclic 0 := rfl

/-- Relabelling the alternatives by `x ↦ x + 1` turns agent `1`'s ranking into agent `0`'s. -/
example (x y : Fin 3) :
    x ≼[cyclic.comap (fun _ (z : Fin 3) => z + 1) 1] y ↔ x ≼[cyclic 0] y := by
  simp only [cyclic, Profile.comap_apply, Profile.ofUtility_apply,
    CompletePreference.toPreference_comap, Preference.comap_le,
    CompletePreference.toPreference_ofUtility, Preference.ofUtility_le_iff]
  revert x y
  decide

end MathEconLib.Preferences.Tests
