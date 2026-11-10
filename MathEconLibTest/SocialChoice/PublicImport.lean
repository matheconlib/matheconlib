/-
Copyright (c) 2026 Ritik Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ritik Jain
-/
module

import MathEconLib.SocialChoice

/-!
# Public Social Choice Interfaces

These compile-time checks pin the headline statements of the social choice layer through the
umbrella import `MathEconLib.SocialChoice`.

## Checks

* Domains — a social welfare function on linear profiles is a function on the subtype of strict
  individual profiles.
* Orientation — `supporters P x y` collects the agents with `y ≺[P i] x`, and `majority P x y`
  compares the two counts.
* Arrow — the impossibility theorem, Proposition 20.1, and the version for a finite type.
* Majority and May — the Condorcet paradox and May's theorem with its converse.

## Tags

social choice, public api, Arrow's theorem, May's theorem
-/

set_option linter.privateModule false

namespace MathEconLib.SocialChoice.Tests

open scoped MathEconLib.Preferences
open MathEconLib.Preferences MathEconLib.SocialChoice

variable {N : Type*} {X : Type*}

example : SocialWelfareFunction (linearProfiles N X) =
    ({P // P ∈ linearProfiles N X} → CompletePreference X) := rfl

example (P : Profile N fun _ => X) : P ∈ linearProfiles N X ↔ ∀ i, Std.Antisymm (P i).le :=
  Iff.rfl

example [Fintype N] (P : Profile N fun _ => X) (x y : X) (i : N) :
    i ∈ supporters P x y ↔ y ≺[P i] x := mem_supporters

example [Fintype N] (P : Profile N fun _ => X) (x y : X) :
    majority P x y ↔ (supporters P x y).card ≤ (supporters P y x).card := majority_apply P x y

example [Finite N] {a b c : X} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {F : SocialWelfareFunction (linearProfiles N X)} (hPar : IsPareto F) (hIIA : IsIIA F) :
    IsDictatorial F :=
  isDictatorial_of_isPareto_of_isIIA hab hac hbc hPar hIIA

example [Finite N] {a b c : X} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {F : SocialWelfareFunction (linearProfiles N X)} :
    IsPareto F ∧ IsIIA F ↔ IsDictatorial F :=
  isPareto_and_isIIA_iff_isDictatorial hab hac hbc

example [Finite N] [Fintype X] (hX : 2 < Fintype.card X)
    {F : SocialWelfareFunction (linearProfiles N X)} (hPar : IsPareto F) (hIIA : IsIIA F) :
    IsDictatorial F :=
  isDictatorial_of_isPareto_of_isIIA_of_two_lt_card hX hPar hIIA

example {a b c : X} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ P ∈ linearProfiles (Fin 3) X, ¬ majority P a b ∧ ¬ majority P b c ∧ ¬ majority P c a :=
  exists_mem_linearProfiles_majority_cycle hab hac hbc

example {a b c : X} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ P ∈ linearProfiles (Fin 3) X, ¬ IsTrans X (majority P) :=
  exists_mem_linearProfiles_not_isTrans_majority hab hac hbc

example [Fintype N] {a b : X} (hab : a ≠ b) (hX : ∀ z, z = a ∨ z = b)
    {F : SocialWelfareFunction (linearProfiles N X)} (hA : IsAnonymous F) (hN : IsNeutral F)
    (hR : IsPositivelyResponsive F) (P : {P // P ∈ linearProfiles N X}) (x y : X) :
    x ≼[F P] y ↔ majority P.1 x y :=
  le_iff_majority_of_isAnonymous_of_isNeutral_of_isPositivelyResponsive hab hX hA hN hR P x y

example [Fintype N] {a b : X} (hab : a ≠ b) (hX : ∀ z, z = a ∨ z = b)
    {F : SocialWelfareFunction (linearProfiles N X)} :
    IsAnonymous F ∧ IsNeutral F ∧ IsPositivelyResponsive F ↔
      ∀ (P : {P // P ∈ linearProfiles N X}) (x y : X), x ≼[F P] y ↔ majority P.1 x y :=
  isAnonymous_and_isNeutral_and_isPositivelyResponsive_iff_le_iff_majority hab hX

end MathEconLib.SocialChoice.Tests
