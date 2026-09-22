/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

import Mathlib.Tactic.Lemma

/-!
# Bayesian games and pure strategies

A Bayesian game specifies each player's payoff as a function of the actions and the true type
profile. Players may have different type and action spaces, and their values may depend on other
players' types. A pure strategy assigns an action to each of a player's types.

## Main definitions

* `BayesianGame`: Type-dependent payoffs with explicit player, type, action, and payoff carriers.
* `BayesianGame.PureStrategy`: A profile of type-contingent actions.
* `BayesianGame.actionProfile`: The actions prescribed at a realized type profile.
* `BayesianGame.comapActions`: A game whose actions are translated into another game's actions.
* `BayesianGame.mapPureStrategy`: Translation of the actions prescribed by a strategy profile.

## Main statements

* `BayesianGame.comapActions_id`: Identity translation preserves the game.
* `BayesianGame.comapActions_comp`: Successive action translations compose.

## Tags

bayesian game, pure strategy, action profile
-/

@[expose] public section

namespace MathEconLib.GameTheory

universe uI uT uA uB uC uV

/-- Players `I` choose actions in `A i` and have private types in `Θ i`. Payoffs depend on the
chosen actions and the entire true type profile, allowing interdependent values in `V`. -/
@[ext] structure BayesianGame (I : Type uI) (Θ : I → Type uT) (A : I → Type uA) (V : Type uV) where
  /-- Player `i`'s payoff at the action profile and true type profile. -/
  payoff : I → (∀ i, A i) → (∀ i, Θ i) → V

namespace BayesianGame

variable {I : Type uI} {Θ : I → Type uT} {A : I → Type uA}
  {B : I → Type uB} {C : I → Type uC} {V : Type uV}

-- The game argument identifies the type and action carriers of the strategy.
/-- A pure strategy profile prescribes each player's action as a function of their own type. -/
abbrev PureStrategy (_G : BayesianGame I Θ A V) := ∀ i, Θ i → A i

/-- The actions prescribed by a pure strategy profile at the realized types. -/
def actionProfile (G : BayesianGame I Θ A V) (s : G.PureStrategy) (θ : ∀ i, Θ i) :
    ∀ i, A i := fun i ↦ s i (θ i)

/-- Evaluation of a player's prescribed action. -/
@[simp] lemma actionProfile_apply (G : BayesianGame I Θ A V) (s : G.PureStrategy)
    (θ : ∀ i, Θ i) (i : I) : G.actionProfile s θ i = s i (θ i) := rfl

/-- Translate each player's action before evaluating the original game's payoffs. -/
def comapActions (G : BayesianGame I Θ A V) (κ : ∀ i, B i → A i) : BayesianGame I Θ B V where
  payoff i b θ := G.payoff i (fun j ↦ κ j (b j)) θ

/-- Payoffs in the translated game are the original payoffs at translated actions. -/
@[simp] lemma comapActions_payoff (G : BayesianGame I Θ A V) (κ : ∀ i, B i → A i)
    (i : I) (b : ∀ i, B i) (θ : ∀ i, Θ i) :
    (G.comapActions κ).payoff i b θ = G.payoff i (fun j ↦ κ j (b j)) θ := rfl

/-- Translating actions by the identity preserves the game. -/
@[simp] lemma comapActions_id (G : BayesianGame I Θ A V) :
    G.comapActions (fun _ ↦ id) = G := rfl

/-- Successive action translations agree with their composition. -/
lemma comapActions_comp (G : BayesianGame I Θ A V) (κ : ∀ i, B i → A i)
    (τ : ∀ i, C i → B i) :
    (G.comapActions κ).comapActions τ = G.comapActions (fun i ↦ κ i ∘ τ i) := rfl

/-- Translate the actions prescribed by a pure strategy profile. -/
def mapPureStrategy (G : BayesianGame I Θ A V) (κ : ∀ i, B i → A i)
    (s : (G.comapActions κ).PureStrategy) : G.PureStrategy :=
  fun i ↦ κ i ∘ s i

/-- At each type, mapping a pure strategy applies the action translation to the prescribed
action. -/
@[simp] lemma mapPureStrategy_apply (G : BayesianGame I Θ A V) (κ : ∀ i, B i → A i)
    (s : (G.comapActions κ).PureStrategy) (i : I) (t : Θ i) :
    G.mapPureStrategy κ s i t = κ i (s i t) := rfl

end BayesianGame

end MathEconLib.GameTheory

end
