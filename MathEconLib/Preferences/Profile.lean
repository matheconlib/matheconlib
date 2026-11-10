/-
Copyright (c) 2026 Ritik Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ritik Jain
-/
module

public import MathEconLib.Preferences.Representation.Basic

/-!
# Preference Profiles

A profile assigns a complete preference to each agent. Agent `i` ranks its own type of
alternatives `X i`, as when each seller ranks its own contracts and an outside option. When every
agent ranks the same alternatives `X`, a profile is a function `N → CompletePreference X`, as in
social choice.

## Main Definitions

* `Profile` — a complete preference on `X i` for each agent `i : N`.
* `Profile.ofUtility` — the profile in which each agent ranks its alternatives by its own utility.
* `Profile.comap` — each agent compares alternatives by their images under its own map.
* `Profile.reindexAgents` — along `g : M → N`, agent `j : M` holds the preference of agent `g j`.

## Main Statements

* `Profile.isRepresentedBy_ofUtility` — each agent's utility represents its preference in the
  profile defined by the utilities.
* `Profile.comap_id`, `Profile.comap_comp` — agentwise changes of alternatives respect identities
  and composition.
* `Profile.reindexAgents_id`, `Profile.reindexAgents_comp` — reindexing agents respects identities
  and composition.
* `Profile.comap_reindexAgents` — reindexing agents commutes with agentwise changes of
  alternatives.

## Implementation Notes

`Profile N X` unfolds to the dependent function type `(i : N) → CompletePreference (X i)`, as
`MathEconLib.Mechanism.Profile` does for inputs. It is stated here so that the preference layer
does not depend on the mechanism layer. The map `g` in `Profile.reindexAgents` need not be a
permutation: several agents may receive the preference of one agent.

## Tags

preference profile, complete preference, agents, utility, reindexing
-/

@[expose] public section

namespace MathEconLib

namespace Preferences

/-- A preference profile: each agent `i : N` holds a complete preference on its alternatives
`X i`. -/
abbrev Profile (N : Type*) (X : N → Type*) := (i : N) → CompletePreference (X i)

namespace Profile

variable {L M N U : Type*} {X Y Z : N → Type*}

/-- The profile in which agent `i` ranks its alternatives by the utility `u i`. -/
def ofUtility [Preorder U] [Std.Total (α := U) (· ≤ ·)] (u : (i : N) → X i → U) : Profile N X :=
  fun i => CompletePreference.ofUtility (u i)

@[simp]
theorem ofUtility_apply [Preorder U] [Std.Total (α := U) (· ≤ ·)] (u : (i : N) → X i → U)
    (i : N) : ofUtility u i = CompletePreference.ofUtility (u i) := rfl

/-- Each agent's utility represents its preference in the profile defined by the utilities. -/
theorem isRepresentedBy_ofUtility [Preorder U] [Std.Total (α := U) (· ≤ ·)]
    (u : (i : N) → X i → U) (i : N) : (ofUtility u i).IsRepresentedBy (u i) :=
  Preference.isRepresentedBy_ofUtility (u i)

/-- Agent `i` compares alternatives by their images under its own map `f i`. -/
def comap (P : Profile N Y) (f : (i : N) → X i → Y i) : Profile N X :=
  fun i => (P i).comap (f i)

@[simp]
theorem comap_apply (P : Profile N Y) (f : (i : N) → X i → Y i) (i : N) :
    P.comap f i = (P i).comap (f i) := rfl

@[simp]
theorem comap_id (P : Profile N X) : P.comap (fun _ => id) = P := rfl

theorem comap_comp (P : Profile N Z) (f : (i : N) → Y i → Z i) (g : (i : N) → X i → Y i) :
    (P.comap f).comap g = P.comap fun i => f i ∘ g i := rfl

/-- The profile in which agent `j : M` holds the preference of agent `g j`. -/
def reindexAgents (P : Profile N X) (g : M → N) : Profile M (X ∘ g) :=
  fun j => P (g j)

@[simp]
theorem reindexAgents_apply (P : Profile N X) (g : M → N) (j : M) :
    P.reindexAgents g j = P (g j) := rfl

@[simp]
theorem reindexAgents_id (P : Profile N X) : P.reindexAgents id = P := rfl

theorem reindexAgents_comp (P : Profile N X) (g : M → N) (h : L → M) :
    (P.reindexAgents g).reindexAgents h = P.reindexAgents (g ∘ h) := rfl

theorem comap_reindexAgents (P : Profile N Y) (f : (i : N) → X i → Y i) (g : M → N) :
    (P.comap f).reindexAgents g = (P.reindexAgents g).comap fun j => f (g j) := rfl

end Profile

end Preferences

end MathEconLib

end
