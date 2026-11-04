/-
Copyright (c) 2026 Ritik Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ritik Jain
-/
module

public import MathEconLib.Preferences.Profile
public import Mathlib.Data.Fintype.Card

/-!
# Aggregating preferences: definitions

Social welfare functions and their axioms, each on an explicit domain `D` of profiles.

## References

* M. J. Osborne, A. Rubinstein, *Models in Microeconomic Theory* (2023), Chapter 20
* K. O. May, Econometrica **20** (1952), 680–684
-/

@[expose] public section

namespace MathEconLib.SocialChoice

open MathEconLib.Preferences

universe u v

/-- A social welfare function (Definition 20.2): `F P x y` reads "at `P`, society finds `x ≿ y`". -/
abbrev SocialWelfareFunction (N : Type u) (X : Type v) : Type (max u v) :=
  Profile N X → X → X → Prop

variable {N : Type u} {X : Type v}

/-- The profiles in which every agent's relation is a linear preference. -/
def linearProfiles (N : Type u) (X : Type v) : Set (Profile N X) :=
  {P | P.IsPreferenceRelation ∧ P.IsStrict}

open Classical in
/-- The agents who strictly prefer `x` to `y` at the profile `P`. -/
noncomputable def supporters [Fintype N] (P : Profile N X) (x y : X) : Finset N :=
  Finset.univ.filter fun i => StrictPart (P i) x y

/-- From `P` to `Q`, `x` rises against `y`: no agent moves towards `y` and some towards `x`. -/
def RisesAgainst (P Q : Profile N X) (x y : X) : Prop :=
  (∀ i, StrictPart (P i) x y → StrictPart (Q i) x y) ∧
    (∀ i, StrictPart (Q i) y x → StrictPart (P i) y x) ∧
    ∃ i, (StrictPart (Q i) x y ∧ ¬ StrictPart (P i) x y) ∨
      (StrictPart (P i) y x ∧ ¬ StrictPart (Q i) y x)

/-- The Pareto property on `D` (Definition 20.6): unanimous strict preferences are social. -/
def IsParetoOn (F : SocialWelfareFunction N X) (D : Set (Profile N X)) : Prop :=
  ∀ ⦃P⦄, P ∈ D → ∀ x y, (∀ i, StrictPart (P i) x y) → StrictPart (F P) x y

/-- IIA on `D` (Arrow's form): the agents' comparisons of `x` and `y` fix society's. -/
def IsIIAOn (F : SocialWelfareFunction N X) (D : Set (Profile N X)) : Prop :=
  ∀ ⦃P⦄, P ∈ D → ∀ ⦃Q⦄, Q ∈ D → ∀ x y,
    (∀ i, (P i x y ↔ Q i x y) ∧ (P i y x ↔ Q i y x)) → (F P x y ↔ F Q x y)

/-- Anonymity on `D`: permuting the agents does not change the social relation. -/
def IsAnonymousOn (F : SocialWelfareFunction N X) (D : Set (Profile N X)) : Prop :=
  ∀ (σ : N ≃ N) ⦃P⦄, P ∈ D → Profile.permuteAgents σ P ∈ D →
    F (Profile.permuteAgents σ P) = F P

/-- Neutrality on `D`: relabelling the alternatives by `τ` relabels the social relation by `τ`. -/
def IsNeutralOn (F : SocialWelfareFunction N X) (D : Set (Profile N X)) : Prop :=
  ∀ (τ : X ≃ X) ⦃P⦄, P ∈ D → Profile.relabel τ P ∈ D →
    ∀ x y, F (Profile.relabel τ P) x y ↔ F P (τ.symm x) (τ.symm y)

/-- Positive responsiveness on `D` (May's, not Osborne and Rubinstein's Definition 20.5). -/
def IsPositivelyResponsiveOn (F : SocialWelfareFunction N X) (D : Set (Profile N X)) : Prop :=
  ∀ ⦃P⦄, P ∈ D → ∀ ⦃Q⦄, Q ∈ D → ∀ x y, RisesAgainst P Q x y → F P x y → StrictPart (F Q) x y

/-- Agent `i` is a dictator for `F` on `D`: the social relation is always `i`'s relation. -/
def IsDictatorOn (F : SocialWelfareFunction N X) (D : Set (Profile N X)) (i : N) : Prop :=
  ∀ ⦃P⦄, P ∈ D → F P = P i

/-- `F` is dictatorial on `D`: some agent is a dictator. -/
def IsDictatorialOn (F : SocialWelfareFunction N X) (D : Set (Profile N X)) : Prop :=
  ∃ i, IsDictatorOn F D i

/-- Majority rule: `x ≿ y` unless more agents strictly prefer `y` to `x` than `x` to `y`. -/
noncomputable def majority [Fintype N] : SocialWelfareFunction N X := fun P x y =>
  (supporters P y x).card ≤ (supporters P x y).card

variable {F : SocialWelfareFunction N X} {D : Set (Profile N X)} {P Q : Profile N X} {x y : X}

@[simp] theorem mem_supporters [Fintype N] {i : N} :
    i ∈ supporters P x y ↔ StrictPart (P i) x y := by
  classical
  simp [supporters]

theorem majority_apply [Fintype N] (P : Profile N X) (x y : X) :
    majority P x y ↔ (supporters P y x).card ≤ (supporters P x y).card :=
  Iff.rfl

end MathEconLib.SocialChoice

section Examples

open MathEconLib.Preferences MathEconLib.SocialChoice

example : supporters (fun (_ : Fin 2) (a b : Bool) => b ≤ a) true false = Finset.univ := by
  ext i
  simp [StrictPart]

example : RisesAgainst (fun (i : Fin 2) (a b : Bool) => i = 1 ∨ b ≤ a)
    (fun (_ : Fin 2) (a b : Bool) => b ≤ a) true false := by
  unfold RisesAgainst StrictPart
  decide

end Examples
