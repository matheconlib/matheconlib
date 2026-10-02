/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Auctionlib.GameTheory.Strategic.Bayesian.Game
public import Auctionlib.Mechanism.Core.Comap
public import Auctionlib.Mechanism.Core.Strategic

/-!
# Bayesian games induced by mechanisms

A mechanism and quasilinear valuation environment determine a Bayesian game: agents choose
mechanism actions and receive their utility at the full true type profile. Outcomes and signed
transfers depend on the chosen actions, while valuations use the true types, including other
agents' true types when values are interdependent.

Fixing the true type profile gives the mechanism's utility game. Translating each agent's actions
before applying the mechanism gives the same Bayesian and strategic games as translating the
actions of the corresponding induced games.

## Main definitions

* `Mechanism.inducedBayesianGame`: The Bayesian game with the mechanism's quasilinear utilities.

## Main statements

* `Mechanism.inducedBayesianGame_toStrategicGame`: The strategic game at fixed true types is
  `QuasilinearEnvironment.utilityGame`.
* `Mechanism.inducedBayesianGame_comap`: Mechanism action translation commutes with inducing a
  Bayesian game.
* `QuasilinearEnvironment.utilityGame_comap`: Mechanism action translation commutes with inducing
  the utility game at fixed true types.

## Tags

mechanism design, bayesian games, strategic games, quasilinear utility, action maps
-/

@[expose] public section

universe uI uΘ uA uB uO

namespace Auctionlib.Mechanism

variable {I : Type uI} {Θ : I → Type uΘ} {A : I → Type uA} {B : I → Type uB}
  {O : Type uO}

section InducedBayesianGame

variable (M : Mechanism I A O) (E : QuasilinearEnvironment I Θ O)

/-- The game in which agents choose actions in mechanism `M` and receive their quasilinear
utilities at the full true type profile. Each agent's signed transfer is added to its value. -/
def inducedBayesianGame : GameTheory.BayesianGame I Θ A ℝ where
  payoff i a θ := E.utility M i θ a

/-- The induced Bayesian payoff equals mechanism utility evaluated at the true types. -/
@[simp] lemma inducedBayesianGame_payoff (i : I) (a : Profile A) (θ : Profile Θ) :
    (M.inducedBayesianGame E).payoff i a θ = E.utility M i θ a := rfl

/-- At fixed true types, the induced Bayesian game is the mechanism's utility game. -/
@[simp] lemma inducedBayesianGame_toStrategicGame (θ : Profile Θ) :
    (M.inducedBayesianGame E).toStrategicGame θ = E.utilityGame M θ := rfl

/-- Translating mechanism actions commutes with inducing its Bayesian game. -/
@[simp] lemma inducedBayesianGame_comap (κ : ∀ i, B i → A i) :
    (M.comap κ).inducedBayesianGame E = (M.inducedBayesianGame E).comapActions κ := rfl

end InducedBayesianGame

namespace QuasilinearEnvironment

/-- Translating mechanism actions commutes with inducing its game at fixed true types. -/
@[simp] lemma utilityGame_comap (E : QuasilinearEnvironment I Θ O) (M : Mechanism I A O)
    (κ : ∀ i, B i → A i) (θ : Profile Θ) :
    E.utilityGame (M.comap κ) θ = (E.utilityGame M θ).comapActions κ := rfl

end QuasilinearEnvironment

end Auctionlib.Mechanism

end
