/-
Copyright (c) 2026 Ritik Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ritik Jain
-/
module

public import MathEconLib.Preferences.Representation.Relation
public import MathEconLib.Mechanism.Core.Profile
public import Mathlib.Logic.Equiv.Defs

/-!
# Profiles of preference relations

A profile assigns to each agent in `N` a relation on the alternatives `X`, read from the better
alternative; it is a `Mechanism.Profile` with every agent reporting a relation.

## Main definitions

* `Profile N X`: a relation on `X` for each agent in `N`.
* `Profile.IsPreferenceRelation`, `Profile.IsStrict`: conditions on every agent's relation.
* `Profile.permuteAgents`, `Profile.relabel`: permute the agents, or relabel the alternatives.
* `Profile.ofUtilities`: the profile defined by a utility for each agent.

## References

* Martin J. Osborne and Ariel Rubinstein (2023), *Models in Microeconomic Theory*, Section 20.2.
-/

@[expose] public section

namespace MathEconLib.Preferences

/-- A profile: `P i x y` reads "agent `i` finds `x` at least as good as `y`". -/
abbrev Profile (N : Type*) (X : Type*) := Mechanism.Profile fun _ : N => X → X → Prop

namespace Profile

variable {N X α : Type*} {P : Profile N X}

/-- Every agent's relation is a preference relation (complete and transitive). -/
def IsPreferenceRelation (P : Profile N X) : Prop := ∀ i, Preferences.IsPreferenceRelation (P i)

/-- Every agent's relation is antisymmetric. -/
def IsStrict (P : Profile N X) : Prop := ∀ i, IsAntisymmetric (P i)

theorem isPreferenceRelation_iff :
    P.IsPreferenceRelation ↔ ∀ i, Preferences.IsPreferenceRelation (P i) := Iff.rfl

theorem isStrict_iff : P.IsStrict ↔ ∀ i, IsAntisymmetric (P i) := Iff.rfl

theorem IsStrict.isLinearPreference (hS : P.IsStrict) (hP : P.IsPreferenceRelation) (i : N) :
    IsLinearPreference (P i) :=
  ⟨hP i, hS i⟩

/-- Agent `i`'s complete preference in a profile of preference relations. -/
def IsPreferenceRelation.toCompletePreference (h : P.IsPreferenceRelation) (i : N) :
    CompletePreference X :=
  .ofGE (P i) (h i)

@[simp]
theorem IsPreferenceRelation.ge_toCompletePreference (h : P.IsPreferenceRelation) (i : N) :
    (h.toCompletePreference i).ge = P i := rfl

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

/-- The alternatives relabelled by `τ`: every agent ranks `x` where she ranked `τ.symm x`. -/
def relabel (τ : X ≃ X) (P : Profile N X) : Profile N X := fun i x y => P i (τ.symm x) (τ.symm y)

@[simp]
theorem relabel_apply (τ : X ≃ X) (P : Profile N X) (i : N) (x y : X) :
    relabel τ P i x y ↔ P i (τ.symm x) (τ.symm y) := Iff.rfl

@[simp]
theorem relabel_refl (P : Profile N X) : relabel (Equiv.refl X) P = P := rfl

theorem relabel_relabel (τ τ' : X ≃ X) (P : Profile N X) :
    relabel τ (relabel τ' P) = relabel (τ'.trans τ) P := rfl

/-- Relabelling is `CompletePreference.comap` along `τ.symm`, agent by agent. -/
theorem IsPreferenceRelation.relabel (h : P.IsPreferenceRelation) (τ : X ≃ X) :
    (relabel τ P).IsPreferenceRelation := fun i =>
  ((h.toCompletePreference i).comap τ.symm).isPreferenceRelation_ge

theorem IsStrict.relabel (h : P.IsStrict) (τ : X ≃ X) : (relabel τ P).IsStrict := fun i =>
  isAntisymmetric_iff.2 fun _ _ h₁ h₂ => τ.symm.injective ((h i).antisymm h₁ h₂)

/-- The profile in which `x ≿ᵢ y` iff `u i y ≤ u i x`. -/
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

theorem isStrict_ofUtilities [PartialOrder α] {u : N → X → α}
    (hu : ∀ i, Function.Injective (u i)) : (ofUtilities u).IsStrict := fun i =>
  isAntisymmetric_utilityRel_iff.2 (hu i)

end Profile

end MathEconLib.Preferences

end
