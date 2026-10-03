/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import MathEconLib.Mechanism

/-!
# Strategic and Bayesian games induced by mechanisms

Dominant-strategy incentives agree with dominance in the strategic game at each true type profile
and give a truthful Nash equilibrium. The induced Bayesian game evaluates the same utility at each
realized type profile. Fixing the true types gives the utility game. Action translation commutes
with both induced-game constructions.

## Main statements

* Dominant-strategy incentives agree with strategic-game dominance and imply truthful Nash
  equilibrium.
* Induced Bayesian payoffs agree with mechanism utility and their fixed-type strategic view.
* Arbitrary action translations commute with both induced-game constructions.

## Tags

mechanism design, dominance, nash equilibrium, bayesian games, action translation
-/

@[expose] public section

open MathEconLib.Mechanism

universe uI uΘ uA uB uO

namespace MathEconLib.Tests.MechanismGames

/-! ## Strategic utility games and truthful dominance -/

/-- A quasilinear mechanism determines a strategic game at any full true type profile. -/
example : ∀ {I : Type uI} {Θ : I → Type uΘ} {A : I → Type uA} {O : Type uO},
    QuasilinearEnvironment I Θ O → Mechanism I A O → Profile Θ →
      GameTheory.StrategicGame I A ℝ :=
  @QuasilinearEnvironment.utilityGame

/-- Utility-game payoffs agree with utility evaluated at fixed true types and chosen actions. -/
example : ∀ {I : Type uI} {Θ : I → Type uΘ} {A : I → Type uA} {O : Type uO}
    (E : QuasilinearEnvironment I Θ O) (M : Mechanism I A O) (θ : Profile Θ)
    (i : I) (a : Profile A),
    (E.utilityGame M θ).payoff i a = E.utility M i θ a :=
  @QuasilinearEnvironment.utilityGame_payoff

/-- Dominant-strategy incentives agree with dominance in the game at every true profile. -/
example : ∀ {I : Type uI} {Θ : I → Type uΘ} {O : Type uO} [DecidableEq I]
    (E : QuasilinearEnvironment I Θ O) (M : DirectMechanism I Θ O),
    DirectMechanism.IsDSIC E M ↔ ∀ θ i,
      GameTheory.StrategicGame.Strategy.IsDominant (G := E.utilityGame M θ) (i := i) (θ i) :=
  @DirectMechanism.isDSIC_iff_isDominant

/-- A DSIC direct mechanism gives truthful Nash equilibrium at every true profile. -/
example : ∀ {I : Type uI} {Θ : I → Type uΘ} {O : Type uO} [DecidableEq I]
    (E : QuasilinearEnvironment I Θ O) (M : DirectMechanism I Θ O),
    DirectMechanism.IsDSIC E M → ∀ θ, (E.utilityGame M θ).IsNash θ :=
  @DirectMechanism.IsDSIC.isNash

/-! ## Induced Bayesian games and action translation -/

/-- A mechanism and quasilinear environment determine a Bayesian game with real utility payoffs. -/
example : ∀ {I : Type uI} {Θ : I → Type uΘ} {A : I → Type uA} {O : Type uO},
    Mechanism I A O → QuasilinearEnvironment I Θ O → GameTheory.BayesianGame I Θ A ℝ :=
  @Mechanism.inducedBayesianGame

/-- Induced payoffs use the full true profile and the mechanism's signed transfers. -/
example : ∀ {I : Type uI} {Θ : I → Type uΘ} {A : I → Type uA} {O : Type uO}
    (M : Mechanism I A O) (E : QuasilinearEnvironment I Θ O) (i : I)
    (a : Profile A) (θ : Profile Θ),
    (M.inducedBayesianGame E).payoff i a θ = E.utility M i θ a :=
  @Mechanism.inducedBayesianGame_payoff

/-- Fixing true types gives the mechanism's strategic utility game. -/
example : ∀ {I : Type uI} {Θ : I → Type uΘ} {A : I → Type uA} {O : Type uO}
    (M : Mechanism I A O) (E : QuasilinearEnvironment I Θ O) (θ : Profile Θ),
    (M.inducedBayesianGame E).toStrategicGame θ = E.utilityGame M θ :=
  @Mechanism.inducedBayesianGame_toStrategicGame

/-- Translating mechanism actions translates the induced Bayesian game. -/
example : ∀ {I : Type uI} {Θ : I → Type uΘ} {A : I → Type uA} {B : I → Type uB}
    {O : Type uO} (M : Mechanism I A O) (E : QuasilinearEnvironment I Θ O)
    (κ : ∀ i, B i → A i),
    (M.comap κ).inducedBayesianGame E = (M.inducedBayesianGame E).comapActions κ :=
  @Mechanism.inducedBayesianGame_comap

/-- Translating mechanism actions also translates each fixed-type strategic utility game. -/
example : ∀ {I : Type uI} {Θ : I → Type uΘ} {A : I → Type uA} {B : I → Type uB}
    {O : Type uO} (E : QuasilinearEnvironment I Θ O) (M : Mechanism I A O)
    (κ : ∀ i, B i → A i) (θ : Profile Θ),
    E.utilityGame (M.comap κ) θ = (E.utilityGame M θ).comapActions κ :=
  @QuasilinearEnvironment.utilityGame_comap

end MathEconLib.Tests.MechanismGames

end
