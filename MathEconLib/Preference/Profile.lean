/-
Copyright (c) 2026 Ritik Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ritik Jain
-/
module

public import MathEconLib.Preference.Utility
public import Mathlib.Logic.Equiv.Defs

/-!
# Profiles of preference relations

A profile assigns a relation over the alternatives `X` to each agent in `N`. It is data only: that
every agent's relation is a preference relation, or is antisymmetric, is a separate predicate.

## Main definitions

* `MathEconLib.Preference.Profile N X`: a relation `X → X → Prop` for each agent `i : N`.
* `Profile.IsPreferenceRelation P`: every agent's relation is a preference relation.
* `Profile.IsStrict P`: every agent's relation is antisymmetric, so no agent is indifferent between
  two distinct alternatives.
* `Profile.permuteAgents σ P`: agent `i` gets the relation of agent `σ i`.
* `Profile.relabel τ P`: the alternatives relabelled by `τ`; every agent ranks `x` where she ranked
  `τ.symm x`.
* `Profile.ofUtilities u`: agent `i`'s relation is the one defined by the function `u i`.

## Main statements

* Identity and composition laws of `permuteAgents` and `relabel`.
* `IsPreferenceRelation` and `IsStrict` are preserved by `permuteAgents` and by `relabel`.
* `isPreferenceRelation_ofUtilities`: functions into a linear order define a profile of preference
  relations; `isStrict_ofUtilities`: injective functions into a partial order define a strict
  profile.

## Implementation notes

A profile is a plain function type (an `abbrev`) with the agents and alternatives as explicit
parameters, so that structures built on the same society share them without casts.

## References

Martin J. Osborne and Ariel Rubinstein (2023), *Models in Microeconomic Theory*, expanded second
edition, Open Book Publishers, Section 20.2 (profiles) and Definitions 20.3–20.4 (neutrality and
anonymity, which `relabel` and `permuteAgents` serve).
[DOI: 10.11647/OBP.0361](https://doi.org/10.11647/OBP.0361).

## Tags

preference profile, permutation of agents, relabelling of alternatives
-/

@[expose] public section

namespace MathEconLib.Preference

universe u v w

/-- A profile: one relation over the alternatives `X` for each agent `i : N`; `P i x y` reads
"agent `i` finds `x` at least as good as `y`". -/
abbrev Profile (N : Type u) (X : Type v) : Type (max u v) := N → X → X → Prop

namespace Profile

variable {N : Type u} {X : Type v} {α : Type w} {P : Profile N X}

/-! ### Properties -/

/-- Every agent's relation is a preference relation (complete and transitive). -/
def IsPreferenceRelation (P : Profile N X) : Prop := ∀ i, Preference.IsPreferenceRelation (P i)

/-- Every agent's relation is antisymmetric: no agent is indifferent between two distinct
alternatives. -/
def IsStrict (P : Profile N X) : Prop := ∀ i, IsAntisymmetric (P i)

theorem isPreferenceRelation_iff :
    P.IsPreferenceRelation ↔ ∀ i, Preference.IsPreferenceRelation (P i) := Iff.rfl

theorem isStrict_iff : P.IsStrict ↔ ∀ i, IsAntisymmetric (P i) := Iff.rfl

/-- In a strict profile of preference relations every agent's relation is a linear preference. -/
theorem IsStrict.isLinearPreference (hS : P.IsStrict) (hP : P.IsPreferenceRelation) (i : N) :
    IsLinearPreference (P i) :=
  ⟨hP i, hS i⟩

/-! ### Permuting the agents -/

/-- The profile in which agent `i` holds the relation of agent `σ i`. -/
def permuteAgents (σ : N ≃ N) (P : Profile N X) : Profile N X := fun i => P (σ i)

@[simp]
theorem permuteAgents_apply (σ : N ≃ N) (P : Profile N X) (i : N) :
    permuteAgents σ P i = P (σ i) := rfl

@[simp]
theorem permuteAgents_refl (P : Profile N X) : permuteAgents (Equiv.refl N) P = P := rfl

theorem permuteAgents_permuteAgents (σ τ : N ≃ N) (P : Profile N X) :
    permuteAgents σ (permuteAgents τ P) = permuteAgents (σ.trans τ) P := rfl

theorem IsPreferenceRelation.permuteAgents (h : P.IsPreferenceRelation) (σ : N ≃ N) :
    (permuteAgents σ P).IsPreferenceRelation := fun i => h (σ i)

theorem IsStrict.permuteAgents (h : P.IsStrict) (σ : N ≃ N) : (permuteAgents σ P).IsStrict :=
  fun i => h (σ i)

/-! ### Relabelling the alternatives -/

/-- The profile with the alternatives relabelled by `τ`: every agent ranks `x` where she ranked
`τ.symm x`. -/
def relabel (τ : X ≃ X) (P : Profile N X) : Profile N X := fun i x y => P i (τ.symm x) (τ.symm y)

@[simp]
theorem relabel_apply (τ : X ≃ X) (P : Profile N X) (i : N) (x y : X) :
    relabel τ P i x y ↔ P i (τ.symm x) (τ.symm y) := Iff.rfl

@[simp]
theorem relabel_refl (P : Profile N X) : relabel (Equiv.refl X) P = P := rfl

theorem relabel_relabel (τ τ' : X ≃ X) (P : Profile N X) :
    relabel τ (relabel τ' P) = relabel (τ'.trans τ) P := rfl

theorem IsPreferenceRelation.relabel (h : P.IsPreferenceRelation) (τ : X ≃ X) :
    (relabel τ P).IsPreferenceRelation := fun i =>
  ⟨isComplete_iff.2 fun _ _ => (h i).total _ _,
    isTransitive_iff.2 fun _ _ _ h₁ h₂ => (h i).trans h₁ h₂⟩

theorem IsStrict.relabel (h : P.IsStrict) (τ : X ≃ X) : (relabel τ P).IsStrict := fun i =>
  isAntisymmetric_iff.2 fun _ _ h₁ h₂ => τ.symm.injective ((h i).antisymm h₁ h₂)

/-! ### Profiles defined by utility functions -/

/-- The profile in which agent `i`'s relation is defined by the function `u i`: `x ≿ᵢ y` iff
`u i x ≥ u i y`. -/
def ofUtilities [LE α] (u : N → X → α) : Profile N X := fun i => UtilityRel (u i)

instance [LE α] [DecidableLE α] (u : N → X → α) (i : N) : DecidableRel (ofUtilities u i) :=
  inferInstanceAs (DecidableRel (UtilityRel (u i)))

@[simp]
theorem ofUtilities_apply [LE α] (u : N → X → α) (i : N) : ofUtilities u i = UtilityRel (u i) :=
  rfl

theorem represents_ofUtilities [LE α] (u : N → X → α) (i : N) :
    Represents (u i) (ofUtilities u i) :=
  represents_utilityRel (u i)

theorem isPreferenceRelation_ofUtilities [LinearOrder α] (u : N → X → α) :
    (ofUtilities u).IsPreferenceRelation := fun i => isPreferenceRelation_utilityRel (u i)

/-- Injective utility functions define a strict profile. -/
theorem isStrict_ofUtilities [PartialOrder α] {u : N → X → α}
    (hu : ∀ i, Function.Injective (u i)) : (ofUtilities u).IsStrict := fun i =>
  isAntisymmetric_utilityRel_iff.2 (hu i)

end Profile

end MathEconLib.Preference

/-! ### Worked examples -/

section Examples

open MathEconLib.Preference

/-- The Condorcet profile on `Fin 3`, in which voter `i` ranks `i ≻ i + 1 ≻ i + 2`, is a strict
profile of preference relations. -/
example : (Profile.ofUtilities fun i x : Fin 3 => (2 - ((x.val + 3 - i.val) % 3) : ℕ)).IsStrict ∧
    (Profile.ofUtilities fun i x : Fin 3 =>
      (2 - ((x.val + 3 - i.val) % 3) : ℕ)).IsPreferenceRelation
    := by
  refine ⟨Profile.isStrict_ofUtilities fun i => ?_, Profile.isPreferenceRelation_ofUtilities _⟩
  revert i; decide

/-- In it, voter `0` prefers `0` to `1`, voter `1` prefers `1` to `2`, and voter `2` prefers `2`
to `0`. -/
example : StrictPart
      (Profile.ofUtilities (fun i x : Fin 3 => (2 - ((x.val + 3 - i.val) % 3) : ℕ)) 0)
      0 1 ∧
    StrictPart (Profile.ofUtilities (fun i x : Fin 3 => (2 - ((x.val + 3 - i.val) % 3) : ℕ)) 1)
      1 2 ∧
    StrictPart (Profile.ofUtilities (fun i x : Fin 3 => (2 - ((x.val + 3 - i.val) % 3) : ℕ)) 2)
      2 0 := by
  decide

/-- Relabelling by a swap exchanges the two alternatives in every agent's ranking. -/
example (P : Profile (Fin 2) (Fin 2)) (i : Fin 2) :
    Profile.relabel (Equiv.swap 0 1) P i 0 1 ↔ P i 1 0 := by
  simp

end Examples
