/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.GameTheory.Strategic.Bayesian.Game
public import MathEconLib.GameTheory.Strategic.Outcome

/-!
# State-dependent evaluation of outcome rules

An outcome rule and utilities evaluated at the full true type profile determine a Bayesian game.
Fixing that profile recovers the strategic game formed by state fixing and outcome evaluation.
Reports and actions change the outcome while leaving the true state fixed.

These are evaluation constructors for an arbitrary payoff carrier. Priors, selected conditional
beliefs, measurability, and integrability are supplied by expected-payoff consumers. A fixed-state
slice does not assert that players observe the full state.
-/

@[expose] public section

namespace MathEconLib.GameTheory.OutcomeGame

universe uI uT uA uX uV

variable {I : Type uI} {T : I → Type uT} {A : I → Type uA} {X : Type uX} {V : Type uV}

/-- Evaluate an outcome rule at the full true type profile to obtain a Bayesian game. -/
def toBayesianGame (g : OutcomeGame I A X)
    (P : PayoffStructure I (((i : I) → T i) × X) V) : BayesianGame I T A V where
  payoff i a θ := P.payoff i (θ, g.outcome a)

/-- The Bayesian payoff evaluates the supplied utility at the true profile and chosen outcome. -/
@[simp] theorem toBayesianGame_payoff (g : OutcomeGame I A X)
    (P : PayoffStructure I (((i : I) → T i) × X) V)
    (i : I) (a : (i : I) → A i) (θ : (i : I) → T i) :
    (g.toBayesianGame P).payoff i a θ = P.payoff i (θ, g.outcome a) :=
  rfl

/-- Fixing true types agrees exactly with state fixing followed by strategic outcome evaluation. -/
@[simp] theorem toBayesianGame_strategicGameAt (g : OutcomeGame I A X)
    (P : PayoffStructure I (((i : I) → T i) × X) V) (θ : (i : I) → T i) :
    (g.toBayesianGame P).strategicGameAt θ = StrategicGame.ofOutcome g (P.atState θ) :=
  rfl

end MathEconLib.GameTheory.OutcomeGame

end
