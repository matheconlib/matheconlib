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

Social welfare functions and their axioms, each on an explicit domain `D` of profiles. A profile
gives each agent a complete preference on the alternatives `X`, and a social welfare function
gives society a complete preference. Majority rule need not be transitive (the Condorcet paradox),
so it is a relation `majority P` on the alternatives rather than a social welfare function.

## Main definitions

* `SocialWelfareFunction N X`: a complete preference of society for each profile.
* `linearProfiles N X`: the profiles in which every agent's preference is antisymmetric.
* `supporters P x y`: the agents who strictly prefer `x` to `y`.
* `IsParetoOn`, `IsIIAOn`, `IsAnonymousOn`, `IsNeutralOn`, `IsPositivelyResponsiveOn`: the axioms.
* `IsDictatorOn`, `IsDictatorialOn`: dictatorship.
* `majority P x y`: `y` is at least as good as `x` by majority: no more agents strictly prefer `x`
  to `y` than `y` to `x`.

## References

* M. J. Osborne, A. Rubinstein, *Models in Microeconomic Theory* (2023), Chapter 20
* K. O. May, Econometrica **20** (1952), 680–684
-/

@[expose] public section

namespace MathEconLib.SocialChoice

open MathEconLib.Preferences

universe u v

/-- A social welfare function (Definition 20.2): society's complete preference at each profile. -/
abbrev SocialWelfareFunction (N : Type u) (X : Type v) : Type (max u v) :=
  Profile N (fun _ => X) → CompletePreference X

variable {N : Type u} {X : Type v}

/-- The profiles in which every agent's preference is a linear order. -/
def linearProfiles (N : Type u) (X : Type v) : Set (Profile N fun _ => X) :=
  {P | ∀ i, Std.Antisymm (P i).le}

open Classical in
/-- The agents who strictly prefer `x` to `y` at the profile `P`. -/
noncomputable def supporters [Fintype N] (P : Profile N fun _ => X) (x y : X) : Finset N :=
  Finset.univ.filter fun i => y ≺[P i] x

/-- From `P` to `Q`, `x` rises against `y`: no agent moves towards `y` and some towards `x`. -/
def RisesAgainst (P Q : Profile N fun _ => X) (x y : X) : Prop :=
  (∀ i, y ≺[P i] x → y ≺[Q i] x) ∧
    (∀ i, x ≺[Q i] y → x ≺[P i] y) ∧
    ∃ i, (y ≺[Q i] x ∧ ¬ y ≺[P i] x) ∨ (x ≺[P i] y ∧ ¬ x ≺[Q i] y)

/-- The Pareto property on `D` (Definition 20.6): unanimous strict preferences are social. -/
def IsParetoOn (F : SocialWelfareFunction N X) (D : Set (Profile N fun _ => X)) : Prop :=
  ∀ ⦃P⦄, P ∈ D → ∀ x y : X, (∀ i, y ≺[P i] x) → y ≺[F P] x

/-- IIA on `D` (Arrow's form): the agents' comparisons of `x` and `y` fix society's. -/
def IsIIAOn (F : SocialWelfareFunction N X) (D : Set (Profile N fun _ => X)) : Prop :=
  ∀ ⦃P⦄, P ∈ D → ∀ ⦃Q⦄, Q ∈ D → ∀ x y : X,
    (∀ i, (y ≼[P i] x ↔ y ≼[Q i] x) ∧ (x ≼[P i] y ↔ x ≼[Q i] y)) → (y ≼[F P] x ↔ y ≼[F Q] x)

/-- Anonymity on `D`: permuting the agents does not change society's preference. -/
def IsAnonymousOn (F : SocialWelfareFunction N X) (D : Set (Profile N fun _ => X)) : Prop :=
  ∀ (σ : N ≃ N) ⦃P⦄, P ∈ D → P.reindexAgents σ ∈ D → F (P.reindexAgents σ) = F P

/-- Neutrality on `D`: relabelling the alternatives by `τ` relabels society's preference by `τ`. -/
def IsNeutralOn (F : SocialWelfareFunction N X) (D : Set (Profile N fun _ => X)) : Prop :=
  ∀ (τ : X ≃ X) ⦃P⦄, P ∈ D → (P.comap fun _ => τ.symm) ∈ D →
    ∀ x y : X, y ≼[F (P.comap fun _ => τ.symm)] x ↔ τ.symm y ≼[F P] τ.symm x

/-- Positive responsiveness on `D` (May's, not Osborne and Rubinstein's Definition 20.5). -/
def IsPositivelyResponsiveOn (F : SocialWelfareFunction N X) (D : Set (Profile N fun _ => X)) :
    Prop :=
  ∀ ⦃P⦄, P ∈ D → ∀ ⦃Q⦄, Q ∈ D → ∀ x y : X, RisesAgainst P Q x y → y ≼[F P] x → y ≺[F Q] x

/-- Agent `i` is a dictator for `F` on `D`: society's preference is always `i`'s preference. -/
def IsDictatorOn (F : SocialWelfareFunction N X) (D : Set (Profile N fun _ => X)) (i : N) : Prop :=
  ∀ ⦃P⦄, P ∈ D → F P = P i

/-- `F` is dictatorial on `D`: some agent is a dictator. -/
def IsDictatorialOn (F : SocialWelfareFunction N X) (D : Set (Profile N fun _ => X)) : Prop :=
  ∃ i, IsDictatorOn F D i

/-- Majority rule's comparison: `y` is at least as good as `x` unless more agents strictly prefer
`x` to `y` than `y` to `x`. It is complete but need not be transitive, so it is a relation rather
than a `CompletePreference`. -/
noncomputable def majority [Fintype N] (P : Profile N fun _ => X) (x y : X) : Prop :=
  (supporters P x y).card ≤ (supporters P y x).card

variable {P : Profile N fun _ => X} {x y : X}

@[simp] theorem mem_supporters [Fintype N] {i : N} : i ∈ supporters P x y ↔ y ≺[P i] x := by
  classical
  simp [supporters]

theorem majority_apply [Fintype N] (P : Profile N fun _ => X) (x y : X) :
    majority P x y ↔ (supporters P x y).card ≤ (supporters P y x).card :=
  Iff.rfl

end MathEconLib.SocialChoice

section Examples

open MathEconLib.Preferences MathEconLib.SocialChoice

example :
    supporters (fun (_ : Fin 2) => CompletePreference.ofUtility fun b : Bool => b) true false =
      Finset.univ := by
  ext i
  simp

example : RisesAgainst
    (fun (i : Fin 2) => CompletePreference.ofUtility fun b : Bool => if i = 1 then 0 else b.toNat)
    (fun (_ : Fin 2) => CompletePreference.ofUtility fun b : Bool => b.toNat) true false := by
  refine ⟨fun i _ => by simp, fun i h => by simp at h, 1, Or.inl ⟨by simp, by simp⟩⟩

end Examples
