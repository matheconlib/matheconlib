/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import MathEconLib.GameTheory.Strategic.Bayesian.Game

/-!
# Action translation and fixed-type games

Action translations evaluate strategic-game payoffs at the translated profile. Identity
translations preserve the game, and successive translations compose. Fixing the full true type
profile of a Bayesian game gives a strategic game and commutes with action translation. Nash
equilibrium pulls back along action translations, which preserve unilateral deviations and payoffs.

The player, type, action, and payoff spaces may occupy independent universes. These constructions
and equalities apply to arbitrary payoff carriers and arbitrary action maps.

## Main statements

* Strategic action translation has the stated payoff, identity, and composition laws.
* Nash equilibrium pulls back along arbitrary action maps.
* Fixing true types preserves Bayesian payoffs and commutes with action translation.

## Tags

strategic games, bayesian games, action translation, type profiles
-/

@[expose] public section

open MathEconLib.GameTheory

universe uI uΘ uA uB uC uV

namespace MathEconLibTest.GameTheory.ActionMaps

/-- Action translation gives a game on the translated action spaces with the same payoff carrier. -/
example : ∀ {I : Type uI} {A : I → Type uA} {V : Type uV} {B : I → Type uB},
    StrategicGame I A V → (∀ i, B i → A i) → StrategicGame I B V :=
  @StrategicGame.comapActions

/-- Translated-game payoffs evaluate the original payoff at the translated action profile. -/
example : ∀ {I : Type uI} {A : I → Type uA} {V : Type uV} {B : I → Type uB}
    (G : StrategicGame I A V) (κ : ∀ i, B i → A i) (i : I) (b : ∀ i, B i),
    (G.comapActions κ).payoff i b = G.payoff i (fun j ↦ κ j (b j)) :=
  @StrategicGame.comapActions_payoff

/-- Translating each action by the identity gives the original strategic game. -/
example : ∀ {I : Type uI} {A : I → Type uA} {V : Type uV}
    (G : StrategicGame I A V), G.comapActions (fun _ ↦ id) = G :=
  @StrategicGame.comapActions_id

/-- Successive strategic-game action translations compose pointwise. -/
example : ∀ {I : Type uI} {A : I → Type uA} {V : Type uV} {B : I → Type uB}
    {C : I → Type uC} (G : StrategicGame I A V) (κ : ∀ i, B i → A i)
    (τ : ∀ i, C i → B i),
    (G.comapActions κ).comapActions τ = G.comapActions (fun i ↦ κ i ∘ τ i) :=
  @StrategicGame.comapActions_comp

/-- Action translation preserves unilateral deviations and payoffs without an order on payoffs. -/
example : ∀ {I : Type uI} {A : I → Type uA} {V : Type uV} [DecidableEq I]
    {B : I → Type uB} (G : StrategicGame I A V) (κ : ∀ i, B i → A i),
    GameComorphism (G.comapActions κ).nashProblem G.nashProblem :=
  @StrategicGame.comapActionsComorphism

/-- Nash equilibrium pulls back with only a payoff comparison and decidable equality of players. -/
example : ∀ {I : Type uI} {A : I → Type uA} {V : Type uV} [LE V] [DecidableEq I]
    {B : I → Type uB} {G : StrategicGame I A V} (κ : ∀ i, B i → A i) {b : ∀ i, B i},
    G.IsNash (fun i ↦ κ i (b i)) → (G.comapActions κ).IsNash b :=
  @StrategicGame.IsNash.comapActions

/-- Fixing true types gives a strategic game in the same actions and payoff carrier. -/
example : ∀ {I : Type uI} {Θ : I → Type uΘ} {A : I → Type uA} {V : Type uV},
    BayesianGame I Θ A V → (∀ i, Θ i) → StrategicGame I A V :=
  @BayesianGame.toStrategicGame

/-- Fixed-type strategic payoffs agree with the Bayesian payoff at those true types. -/
example : ∀ {I : Type uI} {Θ : I → Type uΘ} {A : I → Type uA} {V : Type uV}
    (G : BayesianGame I Θ A V) (θ : ∀ i, Θ i) (i : I) (a : ∀ i, A i),
    (G.toStrategicGame θ).payoff i a = G.payoff i a θ :=
  @BayesianGame.toStrategicGame_payoff

/-- Fixing true types commutes with arbitrary Bayesian action translation. -/
example : ∀ {I : Type uI} {Θ : I → Type uΘ} {A : I → Type uA} {B : I → Type uB}
    {V : Type uV} (G : BayesianGame I Θ A V) (κ : ∀ i, B i → A i) (θ : ∀ i, Θ i),
    (G.comapActions κ).toStrategicGame θ = (G.toStrategicGame θ).comapActions κ :=
  @BayesianGame.toStrategicGame_comapActions

end MathEconLibTest.GameTheory.ActionMaps

end
