/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import MathEconLib.GameTheory.Strategic.Bayesian.Game
public import MathEconLib.Mechanism.Core.Comap
public import MathEconLib.Mechanism.Core.Strategic

/-!
# Bayesian games induced by mechanisms

A mechanism and quasilinear valuation environment determine a Bayesian game. Agents choose
mechanism actions and receive their utility at the full true type profile. Outcomes and signed
transfers depend on the chosen actions, while valuations use the true types, including other
agents' true types when values are interdependent.

Fixing the true type profile gives the mechanism's utility game. Translating each agent's actions
before applying the mechanism gives the same Bayesian and strategic games as translating the
actions of the corresponding induced games.

## Main definitions

* `Mechanism.inducedBayesianGame`: The Bayesian game with the mechanism's quasilinear utilities.

## Main statements

* `Mechanism.inducedBayesianGame_strategicGameAt`: The strategic game at fixed true types is
  `QuasilinearEnvironment.utilityGame`.
* `Mechanism.inducedBayesianGame_comap`: Mechanism action translation commutes with inducing a
  Bayesian game.
* `QuasilinearEnvironment.utilityGame_comap`: Mechanism action translation commutes with inducing
  the utility game at fixed true types.

## Tags

mechanism design, bayesian games, strategic games, quasilinear utility, action maps
-/

@[expose] public section

open MathEconLib.GameTheory

universe uI uT uA uB uO

namespace MathEconLib.Mechanism

variable {I : Type uI} {T : I → Type uT} {A : I → Type uA} {B : I → Type uB}
  {O : Type uO}

section InducedBayesianGame

variable (M : Mechanism I A O) (E : QuasilinearEnvironment I T O)

/-- The game in which agents choose actions in mechanism `M` and receive their quasilinear
utilities at the full true type profile. Each agent's signed transfer is added to its value. -/
@[simps] def inducedBayesianGame : BayesianGame I T A ℝ where
  payoff i a θ := E.utility M i θ a

/-- At fixed true types, the induced Bayesian game is the mechanism's utility game. -/
@[simp] lemma inducedBayesianGame_strategicGameAt (θ : Profile T) :
    (M.inducedBayesianGame E).strategicGameAt θ = E.utilityGame M θ := rfl

/-- Translating mechanism actions commutes with inducing its Bayesian game. -/
@[simp] lemma inducedBayesianGame_comap (κ : ∀ i, B i → A i) :
    (M.comap κ).inducedBayesianGame E = (M.inducedBayesianGame E).comapActions κ := rfl

end InducedBayesianGame

namespace QuasilinearEnvironment

/-- Translating mechanism actions commutes with inducing its game at fixed true types. -/
@[simp] lemma utilityGame_comap (E : QuasilinearEnvironment I T O) (M : Mechanism I A O)
    (κ : ∀ i, B i → A i) (θ : Profile T) :
    E.utilityGame (M.comap κ) θ = (E.utilityGame M θ).comapActions κ := rfl

end QuasilinearEnvironment

end MathEconLib.Mechanism

end
