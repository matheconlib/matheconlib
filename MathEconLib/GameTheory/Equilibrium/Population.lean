/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import MathEconLib.GameTheory.Equilibrium.Problem
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.NNReal.Basic

/-!
# Nonatomic population games

A population game has populations `I`, each with a finite set of actions `A i` and a total mass.
A state splits each population's mass among its actions, and each action earns a payoff depending
on the state. Individuals are infinitesimal: One individual switching actions does not change the
state. So an individual's choice at a state is the problem of picking a best action with the state
held fixed.

## Main definitions

* `PopulationProfile`: Masses of each population on each of its actions.
* `PopulationProfile.IsFeasible`: Nonnegative masses adding up to each population's mass.
* `PopulationGame`: Population masses and action payoffs at feasible states.
* `PopulationGame.choiceProblem`: An individual's choice of action with the state held fixed.
* `PopulationGame.IsSubpopulationEquilibrium`: Every occupied action of one population is a best
  choice.
* `PopulationGame.IsPopulationEquilibrium`: Every population is in equilibrium.

## Main statements

* `PopulationGame.isSubpopulationEquilibrium_iff`: Occupied actions have maximal payoff.

## Tags

population games, nonatomic games, equilibrium
-/

@[expose] public section

namespace MathEconLib.GameTheory

/-- Raw action masses, indexed by population. -/
abbrev PopulationProfile {I : Type*} (A : I → Type*) :=
  ∀ i, A i → ℝ

namespace PopulationProfile

variable {I : Type*} {A : I → Type*}
variable [∀ i, Fintype (A i)]

/-- Nonnegative allocations preserving each population's mass. -/
def IsFeasible (mass : I → NNReal) (x : PopulationProfile A) : Prop :=
  ∀ i, (∀ a, 0 ≤ x i a) ∧
    ∑ a, x i a = (mass i : ℝ)

end PopulationProfile

/-- A nonatomic population game with finite action sets. -/
structure PopulationGame
    (I : Type*) (A : I → Type*) [∀ i, Fintype (A i)] where
  /-- The total mass of each population. -/
  mass : I → NNReal
  /-- The payoff of each action at each feasible state. -/
  payoff :
    {x : PopulationProfile A // x.IsFeasible mass} →
      ∀ i, A i → ℝ

namespace PopulationGame

variable {I : Type*} {A : I → Type*}
variable [∀ i, Fintype (A i)]

/-- A feasible aggregate allocation. -/
abbrev State (G : PopulationGame I A) :=
  {x : PopulationProfile A // x.IsFeasible G.mass}

/-- An individual's choice problem at a fixed aggregate state. -/
def choiceProblem
    (G : PopulationGame I A) (x : G.State) (i : I) :
    EquilibriumProblem (A i) Unit ℝ where
  deviation _ _ _ := True
  value _ a := G.payoff x i a

/-- Every occupied action of population `i` solves its choice problem. -/
def IsSubpopulationEquilibrium
    (G : PopulationGame I A) (x : G.State) (i : I) : Prop :=
  ∀ a, 0 < x.val i a → (G.choiceProblem x i).IsEquilibrium a

/-- Every population is in equilibrium. -/
def IsPopulationEquilibrium
    (G : PopulationGame I A) (x : G.State) : Prop :=
  ∀ i, G.IsSubpopulationEquilibrium x i

/-- A population is in equilibrium when its occupied actions have maximal payoff. -/
lemma isSubpopulationEquilibrium_iff (G : PopulationGame I A) (x : G.State) (i : I) :
    G.IsSubpopulationEquilibrium x i ↔
      ∀ a b, 0 < x.val i a → G.payoff x i b ≤ G.payoff x i a :=
  ⟨fun h a b ha ↦ h a ha () b trivial, fun h a ha _ b _ ↦ h a b ha⟩

end PopulationGame
end MathEconLib.GameTheory
