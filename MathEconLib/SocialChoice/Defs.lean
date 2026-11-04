/-
Copyright (c) 2026 Ritik Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ritik Jain
-/
module

public import MathEconLib.Preference.Profile
public import Mathlib.Data.Fintype.Card

/-!
# Aggregating preferences: definitions

A social welfare function assigns a social relation over the alternatives `X` to every profile of
relations of the agents `N`. It is defined on all profiles; the domain on which it is studied is a
set `D` of profiles, an explicit argument of every axiom (as in Mathlib's `MonotoneOn f s`), so
that restricted domains need no new definitions. Osborne and Rubinstein's domain, all profiles of
strict preference relations, is `linearProfiles N X`.

## Main definitions

* `SocialWelfareFunction N X`: a social relation `X → X → Prop` for every `Profile N X`
  (Osborne and Rubinstein's preference aggregation function).
* `linearProfiles N X`: the profiles in which every agent's relation is complete, transitive and
  antisymmetric.
* `supporters P x y`: the agents who strictly prefer `x` to `y` at `P`.
* `RisesAgainst P Q x y`: from `P` to `Q`, `x` gains against `y`: no agent moves towards `y`, and
  some agent moves towards `x`.
* The axioms on a domain `D`: `IsParetoOn`, `IsIIAOn` (independence of irrelevant alternatives),
  `IsAnonymousOn`, `IsNeutralOn`, `IsPositivelyResponsiveOn`,
  `IsDictatorOn`, `IsDictatorialOn`.
* `majority`: simple majority, `x ≿ y` when at least as many agents strictly prefer `x` to `y` as
  `y` to `x`.

## Implementation notes

* The value of a social welfare function off the domain is never used: every axiom quantifies over
  `P ∈ D` only. That the social relation is a preference relation (Arrow's collective rationality)
  is not part of the data; theorems that need it take `∀ P ∈ D, IsPreferenceRelation (F P)` as a
  hypothesis.
* Independence of irrelevant alternatives compares the agents' relations on `x` and `y` in both
  directions (Arrow's form). On `linearProfiles` it is equivalent to Osborne and Rubinstein's
  Definition 20.7, which compares only the strict preferences `x ≻ᵢ y`; the direction used,
  Arrow's form implies theirs, is `IsIIAOn.iff_of_strictPart_iff`.
* Anonymity and neutrality are invariance under every permutation of the agents
  (`Profile.permuteAgents`) and every relabelling of the alternatives (`Profile.relabel`).
  Osborne and Rubinstein's Definitions 20.4 and 20.3 state them for transpositions only, which
  generate all permutations of a finite set.
* Positive responsiveness is May's pairwise condition, with several agents allowed to move at
  once: if `x ≿ y`, and `x` then rises against `y`, then `x ≻ y`. Osborne and Rubinstein's
  Definition 20.5 is a different condition: `x` rises one step in one agent's ranking, and
  `x ≻ z` follows for every `z` with `x ≿ z`.
* `majority` counts with `Finset.univ.filter` and classical decidability, so `[Fintype N]` is
  the only instance a theorem about it needs.

## References

Martin J. Osborne and Ariel Rubinstein (2023), *Models in Microeconomic Theory*, expanded second
edition, Open Book Publishers, Chapter 20 (Definitions 20.2–20.7, Proposition 20.1).
[DOI: 10.11647/OBP.0361](https://doi.org/10.11647/OBP.0361).

Kenneth J. Arrow (1951), *Social Choice and Individual Values*, Wiley.

Kenneth O. May (1952), *A set of independent necessary and sufficient conditions for simple
majority decision*, Econometrica **20**(4), 680–684.
[DOI: 10.2307/1907651](https://doi.org/10.2307/1907651).

## Tags

anonymity, neutrality, positive responsiveness, majority rule,
social welfare function, preference aggregation, Pareto, independence of irrelevant
alternatives, dictator
-/

@[expose] public section

namespace MathEconLib.SocialChoice

open MathEconLib.Preference

universe u v

/-- A social welfare function (Osborne and Rubinstein's preference aggregation function,
Definition 20.2): a social relation over `X` for every profile of relations of the agents `N`;
`F P x y` reads "at the profile `P`, society finds `x` at least as good as `y`". -/
abbrev SocialWelfareFunction (N : Type u) (X : Type v) : Type (max u v) :=
  Profile N X → X → X → Prop

variable {N : Type u} {X : Type v}

/-- The profiles of linear preferences: every agent's relation is complete, transitive and
antisymmetric. Osborne and Rubinstein's domain of profiles of strict preference relations
(Section 20.2). -/
def linearProfiles (N : Type u) (X : Type v) : Set (Profile N X) :=
  {P | P.IsPreferenceRelation ∧ P.IsStrict}

open Classical in
/-- The agents who strictly prefer `x` to `y` at the profile `P`. -/
noncomputable def supporters [Fintype N] (P : Profile N X) (x y : X) : Finset N :=
  Finset.univ.filter fun i => StrictPart (P i) x y

/-- From `P` to `Q`, `x` rises against `y`: every agent who strictly prefers `x` to `y` at `P`
still does at `Q`, every agent who strictly prefers `y` to `x` at `Q` already did at `P`, and some
agent changes in favour of `x` (she comes to prefer `x` strictly, or stops preferring `y`
strictly). -/
def RisesAgainst (P Q : Profile N X) (x y : X) : Prop :=
  (∀ i, StrictPart (P i) x y → StrictPart (Q i) x y) ∧
    (∀ i, StrictPart (Q i) y x → StrictPart (P i) y x) ∧
    ∃ i, (StrictPart (Q i) x y ∧ ¬ StrictPart (P i) x y) ∨
      (StrictPart (P i) y x ∧ ¬ StrictPart (Q i) y x)

/-! ### Axioms on a domain -/

/-- The Pareto property on `D` (Definition 20.6): at every profile of `D`, if every agent strictly
prefers `x` to `y`, so does society. -/
def IsParetoOn (F : SocialWelfareFunction N X) (D : Set (Profile N X)) : Prop :=
  ∀ ⦃P⦄, P ∈ D → ∀ x y, (∀ i, StrictPart (P i) x y) → StrictPart (F P) x y

/-- Independence of irrelevant alternatives on `D`, in Arrow's form: if at two profiles of `D`
every agent compares `x` with `y` the same way, in both directions, society compares `x` with `y`
the same way. -/
def IsIIAOn (F : SocialWelfareFunction N X) (D : Set (Profile N X)) : Prop :=
  ∀ ⦃P⦄, P ∈ D → ∀ ⦃Q⦄, Q ∈ D → ∀ x y,
    (∀ i, (P i x y ↔ Q i x y) ∧ (P i y x ↔ Q i y x)) → (F P x y ↔ F Q x y)

/-- Anonymity on `D`: permuting the agents' relations, by any permutation, does not change the
social relation. -/
def IsAnonymousOn (F : SocialWelfareFunction N X) (D : Set (Profile N X)) : Prop :=
  ∀ (σ : N ≃ N) ⦃P⦄, P ∈ D → Profile.permuteAgents σ P ∈ D →
    F (Profile.permuteAgents σ P) = F P

/-- Neutrality on `D`: relabelling the alternatives in every agent's relation by any permutation
`τ` relabels them in the social relation by `τ`. -/
def IsNeutralOn (F : SocialWelfareFunction N X) (D : Set (Profile N X)) : Prop :=
  ∀ (τ : X ≃ X) ⦃P⦄, P ∈ D → Profile.relabel τ P ∈ D →
    ∀ x y, F (Profile.relabel τ P) x y ↔ F P (τ.symm x) (τ.symm y)

/-- Positive responsiveness on `D` (May's condition, several agents moving at once): if society
finds `x` at least as good as `y` at `P`, and `x` rises against `y` from `P` to `Q`, then society
strictly prefers `x` to `y` at `Q`. -/
def IsPositivelyResponsiveOn (F : SocialWelfareFunction N X) (D : Set (Profile N X)) : Prop :=
  ∀ ⦃P⦄, P ∈ D → ∀ ⦃Q⦄, Q ∈ D → ∀ x y, RisesAgainst P Q x y → F P x y → StrictPart (F Q) x y

/-- Agent `i` is a dictator for `F` on `D`: at every profile of `D` the social relation is `i`'s
relation. -/
def IsDictatorOn (F : SocialWelfareFunction N X) (D : Set (Profile N X)) (i : N) : Prop :=
  ∀ ⦃P⦄, P ∈ D → F P = P i

/-- `F` is dictatorial on `D`: some agent is a dictator. -/
def IsDictatorialOn (F : SocialWelfareFunction N X) (D : Set (Profile N X)) : Prop :=
  ∃ i, IsDictatorOn F D i

/-! ### Majority rule -/

/-- Majority rule (simple majority): `x` is socially at least as good as `y` when at least as many
agents strictly prefer `x` to `y` as strictly prefer `y` to `x`. -/
noncomputable def majority [Fintype N] : SocialWelfareFunction N X := fun P x y =>
  (supporters P y x).card ≤ (supporters P x y).card

/-! ### Unfolding lemmas -/

variable {F : SocialWelfareFunction N X} {D : Set (Profile N X)} {P Q : Profile N X} {x y : X}

@[simp] theorem mem_supporters [Fintype N] {i : N} :
    i ∈ supporters P x y ↔ StrictPart (P i) x y := by
  classical
  simp [supporters]

theorem majority_apply [Fintype N] (P : Profile N X) (x y : X) :
    majority P x y ↔ (supporters P y x).card ≤ (supporters P x y).card :=
  Iff.rfl

end MathEconLib.SocialChoice

/-! ### Worked examples -/

section Examples

open MathEconLib.Preference MathEconLib.SocialChoice

/-- When both agents rank `true` above `false`, both support `true` against `false`. -/
example : supporters (fun (_ : Fin 2) (a b : Bool) => b ≤ a) true false = Finset.univ := by
  ext i
  simp [StrictPart]

/-- Agent `0` prefers `true` and agent `1` is indifferent; when agent `1` comes to prefer `true`,
`true` rises against `false`. -/
example : RisesAgainst (fun (i : Fin 2) (a b : Bool) => i = 1 ∨ b ≤ a)
    (fun (_ : Fin 2) (a b : Bool) => b ≤ a) true false := by
  unfold RisesAgainst StrictPart
  decide

end Examples
