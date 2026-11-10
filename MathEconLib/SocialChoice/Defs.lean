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

Social welfare functions and their axioms. A profile gives each agent a complete preference on the
alternatives `X`. A social welfare function on a domain `D` of profiles gives society a complete
preference at each profile in `D`; Arrow's and May's theorems take `D = linearProfiles N X`, the
profiles of strict individual rankings. The axioms compare alternatives pair by pair. Majority rule
need not be transitive (the Condorcet paradox), so it is a relation `majority P` on the
alternatives rather than a social welfare function.

## Main definitions

* `SocialWelfareFunction D`: society's complete preference at each profile in `D`.
* `linearProfiles N X`: the profiles in which every agent's preference is antisymmetric.
* `supporters P x y`: the agents who strictly prefer `x` to `y`, that is, with `y ≺[P i] x`.
* `IsPareto`, `IsIIA`, `IsAnonymous`, `IsNeutral`, `IsPositivelyResponsive`: the axioms.
* `IsDictator`, `IsDictatorial`: dictatorship.
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

variable {N : Type u} {X : Type v}

/-- A social welfare function on the domain `D` (Definition 20.2): society's complete preference
at each admissible profile. -/
abbrev SocialWelfareFunction (D : Set (Profile N fun _ => X)) : Type (max u v) :=
  {P // P ∈ D} → CompletePreference X

/-- The profiles in which every agent's preference is a linear order: strict individual
rankings. -/
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

variable {D : Set (Profile N fun _ => X)}

/-- The Pareto property (Definition 20.6): unanimous strict preferences are social. -/
def IsPareto (F : SocialWelfareFunction D) : Prop :=
  ∀ (P : {P // P ∈ D}) (x y : X), (∀ i, y ≺[P.1 i] x) → y ≺[F P] x

/-- IIA (Arrow's form): the agents' comparisons of `x` and `y` fix society's. -/
def IsIIA (F : SocialWelfareFunction D) : Prop :=
  ∀ (P Q : {P // P ∈ D}) (x y : X),
    (∀ i, (y ≼[P.1 i] x ↔ y ≼[Q.1 i] x) ∧ (x ≼[P.1 i] y ↔ x ≼[Q.1 i] y)) →
      (y ≼[F P] x ↔ y ≼[F Q] x)

/-- Anonymity: permuting the agents does not change society's preference. -/
def IsAnonymous (F : SocialWelfareFunction D) : Prop :=
  ∀ (σ : N ≃ N) (P : {P // P ∈ D}) (hσ : P.1.reindexAgents σ ∈ D), F ⟨_, hσ⟩ = F P

/-- Neutrality: relabelling the alternatives by `τ` relabels society's preference by `τ`. -/
def IsNeutral (F : SocialWelfareFunction D) : Prop :=
  ∀ (τ : X ≃ X) (P : {P // P ∈ D}) (hτ : (P.1.comap fun _ => τ.symm) ∈ D) (x y : X),
    y ≼[F ⟨_, hτ⟩] x ↔ τ.symm y ≼[F P] τ.symm x

/-- Positive responsiveness (May's, not Osborne and Rubinstein's Definition 20.5). -/
def IsPositivelyResponsive (F : SocialWelfareFunction D) : Prop :=
  ∀ (P Q : {P // P ∈ D}) (x y : X), RisesAgainst P.1 Q.1 x y → y ≼[F P] x → y ≺[F Q] x

/-- Agent `i` is a dictator for `F`: society's preference is always `i`'s preference. -/
def IsDictator (F : SocialWelfareFunction D) (i : N) : Prop :=
  ∀ P : {P // P ∈ D}, F P = P.1 i

/-- `F` is dictatorial: some agent is a dictator. -/
def IsDictatorial (F : SocialWelfareFunction D) : Prop :=
  ∃ i, IsDictator F i

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
