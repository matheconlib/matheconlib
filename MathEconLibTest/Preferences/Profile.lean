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
clients, through the umbrella import `MathEconLib.Preferences`.

## Checks

* Utility — Osborne and Rubinstein's Example 1.1, a complete preference with an indifference given
  by an integer utility, and a real-valued representation of it.
* Profiles — a profile of three agents with cyclic strict rankings, its reindexing along a
  non-injective map, and a relabelling of the alternatives.
* Seller-dependent alternatives — as in the cumulative-offer process (#261, #279), each seller ranks
  its own contracts and an outside option; restricting to contracts is `Profile.comap` along
  `some`, which is injective and so preserves strict rankings.
* Constant families with ties — agents ranking the same alternatives, one of them indifferent, and
  a constant map of alternatives, along which antisymmetry fails.

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

/-! ### Seller-dependent alternatives -/

/-- The seller of each of four contracts: contracts `0`, `1` belong to seller `0`, the rest to
seller `1`. -/
def seller (x : Fin 4) : Fin 2 := if x.val < 2 then 0 else 1

/-- Each seller ranks its own contracts by index, above the outside option `none`. -/
def sellerProfile : Profile (Fin 2) fun s => Option {x : Fin 4 // seller x = s} :=
  Profile.ofUtility fun _ o => o.elim 0 fun x => x.1.val + 1

/-- Each seller's ranking of its own contracts, compared through `some`. -/
def contractProfile : Profile (Fin 2) fun s => {x : Fin 4 // seller x = s} :=
  sellerProfile.comap fun _ => some

example (s : Fin 2) (x y : {x : Fin 4 // seller x = s}) :
    x ≼[contractProfile s] y ↔ some x ≼[sellerProfile s] some y := Iff.rfl

/-- Every contract is strictly better for its seller than the outside option. -/
example (s : Fin 2) (x : {x : Fin 4 // seller x = s}) : none ≺[sellerProfile s] some x := by
  simp [sellerProfile]

/-- Each seller's ranking is strict, so its ranking of contracts is strict too. -/
example (s : Fin 2) : Std.Antisymm (contractProfile s).le := by
  have : Std.Antisymm (sellerProfile s).le := ⟨fun a b hab hba => by
    simp only [sellerProfile, Profile.ofUtility_apply, CompletePreference.toPreference_ofUtility,
      Preference.ofUtility_le_iff] at hab hba
    have h := le_antisymm hab hba
    rcases a with _ | ⟨a, ha⟩ <;> rcases b with _ | ⟨b, hb⟩
    · rfl
    · simp at h
    · simp at h
    · change a.val + 1 = b.val + 1 at h
      exact congrArg some (Subtype.ext (Fin.ext (Nat.add_right_cancel h)))⟩
  exact sellerProfile.antisymm_comap (fun _ => Option.some_injective _) s

/-! ### Constant families with ties and arbitrary maps -/

/-- Three agents rank `Bool`; agent `0` is indifferent, the others prefer `true`. -/
def tied : Profile (Fin 3) fun _ => Bool :=
  Profile.ofUtility fun i b => if i = 0 then 0 else b.toNat

example : true ~[tied 0] false := by
  simp [tied]

example : false ≺[tied 1] true := by
  simp [tied]

/-- Along a constant map of alternatives every pair is indifferent, so antisymmetry fails even
though agent `1`'s ranking is strict. -/
example : ¬ Std.Antisymm (tied.comap (fun _ (_ : Fin 2) => true) 1).le := fun h =>
  absurd (h.antisymm 0 1 (by simp [tied]) (by simp [tied])) (by decide)

/-- Reindexing along an arbitrary map of agents: five new agents all hold agent `0`'s
preference. -/
def tiedFive : Profile (Fin 5) fun _ => Bool :=
  tied.reindexAgents fun _ => 0

example (j : Fin 5) : true ~[tiedFive j] false := by
  simp [tiedFive, tied]

end MathEconLib.Preferences.Tests
