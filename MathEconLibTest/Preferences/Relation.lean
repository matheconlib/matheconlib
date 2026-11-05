/-
Copyright (c) 2026 Ritik Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ritik Jain
-/
module

import MathEconLib.Preferences.Profile
import Mathlib.Data.Fin.VecNotation

/-!
# Preference Relations, Utility Relations, and Profiles

These compile-time checks pin the public API of preference relations read from the better
alternative, their bridges to `Preference` and `CompletePreference`, and profiles.

## Checks

* Orientation — `S.ge x y` is `y ≼[S] x`, and the strict part and indifference of `S.ge` are
  `≺[S]` reversed and `~[S]`.
* Bridges — a preference relation is exactly `S.ge` for a complete preference `S`, and a utility
  represents `S.ge` exactly when it represents `S`.
* Utility — transformations of representations, and finite representations derived from
  `CompletePreference.exists_isRepresentedBy_nat`.
* Profiles — permuting agents, relabelling alternatives, and profiles defined by utilities.
-/

set_option linter.privateModule false

namespace MathEconLib.Preferences.Tests

open scoped MathEconLib.Preferences

section Bridges

variable {X : Type*} (S : Preference X) (T : CompletePreference X) {R : X → X → Prop} (x y : X)

example : S.ge x y ↔ y ≼[S] x := Iff.rfl

example : StrictPart S.ge x y ↔ y ≺[S] x := S.strictPart_ge

example : Indiff S.ge x y ↔ x ~[S] y := S.indiff_ge

example : IsPreferenceRelation T.ge := T.isPreferenceRelation_ge

example [Std.Antisymm T.le] : IsLinearPreference T.ge := T.isLinearPreference_ge

example (h : IsPreferenceRelation R) : x ≼[CompletePreference.ofGE R h] y ↔ R y x := Iff.rfl

example (h : IsPreferenceRelation R) : (CompletePreference.ofGE R h).ge = R :=
  CompletePreference.ge_ofGE h

example : CompletePreference.ofGE T.ge T.isPreferenceRelation_ge = T := T.ofGE_ge

example : IsPreferenceRelation R ↔ ∃ S : CompletePreference X, S.ge = R :=
  isPreferenceRelation_iff_exists_ge

end Bridges

section Utility

variable {X α : Type*} {R : X → X → Prop}

example [Preorder α] (S : Preference X) (u : X → α) :
    Represents u S.ge ↔ S.IsRepresentedBy u := Preference.represents_ge_iff

example [Preorder α] (u : X → α) : UtilityRel u = (Preference.ofUtility u).ge :=
  utilityRel_eq_ge u

example [Preorder α] (u : X → α) (x y : X) : StrictPart (UtilityRel u) x y ↔ u y < u x :=
  strictPart_utilityRel_iff u

example [LinearOrder α] (u : X → α) : IsPreferenceRelation (UtilityRel u) :=
  isPreferenceRelation_utilityRel u

example [LinearOrder α] {β : Type*} [Preorder β] (S : Preference X) {u : X → α} {f : α → β}
    (hu : S.IsRepresentedBy u) (hf : StrictMono f) : S.IsRepresentedBy (f ∘ u) :=
  hu.comp_strictMono hf

example {u : X → ℝ} (hu : Represents u R) {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Represents (fun x => a * u x + b) R := hu.affine ha b

example [Finite X] (T : CompletePreference X) : ∃ u : X → ℝ, T.IsRepresentedBy u :=
  T.exists_isRepresentedBy_real

example [Finite X] (hR : IsPreferenceRelation R) : ∃ u : X → ℕ, Represents u R :=
  exists_nat_represents_of_finite hR

example [Finite X] (hR : IsPreferenceRelation R) : ∃ u : X → ℝ, Represents u R :=
  exists_represents_of_finite hR

/-- Osborne and Rubinstein's Example 1.1: `a ≻ b ∼ c ≻ d`, with `u = (5, -1, -1, -17)`. -/
example : StrictPart (UtilityRel ![(5 : ℤ), -1, -1, -17]) 0 1 ∧
    Indiff (UtilityRel ![(5 : ℤ), -1, -1, -17]) 1 2 ∧
    StrictPart (UtilityRel ![(5 : ℤ), -1, -1, -17]) 2 3 := by
  decide

end Utility

section Profile

variable {N X : Type*} (P : Profile N X)

example (σ : N ≃ N) (i : N) : Profile.permuteAgents σ P i = P (σ i) := rfl

example (τ : X ≃ X) (h : P.IsPreferenceRelation) : (Profile.relabel τ P).IsPreferenceRelation :=
  h.relabel τ

example (τ : X ≃ X) (h : P.IsStrict) : (Profile.relabel τ P).IsStrict := h.relabel τ

example (h : P.IsPreferenceRelation) (i : N) : (h.toCompletePreference i).ge = P i := rfl

example (P : Profile (Fin 2) (Fin 2)) (i : Fin 2) :
    Profile.relabel (Equiv.swap 0 1) P i 0 1 ↔ P i 1 0 := by
  simp

/-- Three agents with cyclic strict rankings of three alternatives. -/
example : (Profile.ofUtilities fun i x : Fin 3 => (2 - ((x.val + 3 - i.val) % 3) : ℕ)).IsStrict ∧
    (Profile.ofUtilities fun i x : Fin 3 =>
      (2 - ((x.val + 3 - i.val) % 3) : ℕ)).IsPreferenceRelation := by
  refine ⟨Profile.isStrict_ofUtilities fun i => ?_, Profile.isPreferenceRelation_ofUtilities _⟩
  revert i
  decide

end Profile

end MathEconLib.Preferences.Tests
