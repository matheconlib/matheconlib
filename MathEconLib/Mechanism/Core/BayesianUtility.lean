/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.GameTheory.Strategic.Bayesian.Outcome
public import MathEconLib.Mechanism.Core.Utility

/-!
# Bayesian mechanism views with supplied utility

The mechanism determines the consequence, and supplied utility evaluates it at the full true
type profile using shared outcome evaluation. Fixing that profile recovers `toStrategicGame`.
Priors, beliefs, strategies, and analytic assumptions remain inputs to later game-layer consumers.
-/

@[expose] public section

open MathEconLib.GameTheory

namespace MathEconLib.Mechanism

universe uI uT uA uB uO uV

variable {I : Type uI} {T : I → Type uT} {A : I → Type uA} {B : I → Type uB}
  {O : Type uO} {V : Type uV}

/-- Form the Bayesian view through the shared outcome and state-dependent payoff constructors. -/
def toBayesianGame (M : Mechanism I A O)
    (u : I → Profile T → (O × (I → ℝ)) → V) : BayesianGame I T A V :=
  M.toOutcomeGame.toBayesianGame { payoff := fun i x ↦ u i x.1 x.2 }

/-- Bayesian evaluation keeps true types fixed while the action profile selects consequences. -/
@[simp] theorem toBayesianGame_payoff (M : Mechanism I A O)
    (u : I → Profile T → (O × (I → ℝ)) → V) (i : I) (a : Profile A) (θ : Profile T) :
    (M.toBayesianGame u).payoff i a θ = u i θ (M.outcome a, fun j ↦ M.transfer j a) :=
  rfl

/-- The two mechanism views agree by the shared outcome-game fixed-state law. -/
@[simp] theorem toBayesianGame_strategicGameAt (M : Mechanism I A O)
    (u : I → Profile T → (O × (I → ℝ)) → V) (θ : Profile T) :
    (M.toBayesianGame u).strategicGameAt θ = M.toStrategicGame u θ :=
  M.toOutcomeGame.toBayesianGame_strategicGameAt { payoff := fun i x ↦ u i x.1 x.2 } θ

/-- Converting reports commutes with the Bayesian mechanism constructor. -/
@[simp] theorem toBayesianGame_comap (M : Mechanism I A O)
    (κ : (i : I) → B i → A i) (u : I → Profile T → (O × (I → ℝ)) → V) :
    (M.comap κ).toBayesianGame u = (M.toBayesianGame u).comapActions κ :=
  rfl

end MathEconLib.Mechanism

end
