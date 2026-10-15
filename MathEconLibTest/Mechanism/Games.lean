/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import MathEconLib.Mechanism

/-!
# Mechanism games under action translation

Translating a mechanism's actions and then fixing the types in its induced Bayesian game gives
utilities at the translated actions. For a direct mechanism satisfying dominant-strategy incentive
compatibility, every action profile translating to truthful reports is a Nash equilibrium of this
game.

## Main statements

* Fixed-type payoffs after action translation agree with the original mechanism's utilities.
* Dominant-strategy incentives give Nash equilibrium after translating mechanism actions and fixing
  the true types.

## Tags

mechanism design, nash equilibrium, bayesian games, action translation
-/

@[expose] public section

open MathEconLib.GameTheory MathEconLib.Mechanism

universe uI uT uA uB uO

namespace MathEconLib.Tests.MechanismGames

variable {I : Type uI} {T : I → Type uT} {A : I → Type uA} {B : I → Type uB}
  {O : Type uO}

-- The umbrella import must expose the simp lemmas across all three constructions, with the
-- player, type, action, and outcome carriers in independent universes.
/-- Fixed-type payoffs after action translation are the original mechanism's utilities. -/
example (E : QuasilinearEnvironment I T O) (M : Mechanism I A O)
    (κ : ∀ i, B i → A i) (θ : Profile T) (i : I) (b : Profile B) :
    (((M.comap κ).inducedBayesianGame E).strategicGameAt θ).payoff i b =
      E.utility M i θ (fun j ↦ κ j (b j)) := by
  simp

-- This combines DSIC, mechanism action translation, fixed-type agreement, and strategic Nash
-- pullback. Neither injectivity nor surjectivity of the action maps is required.
/-- A profile translating to truthful reports is Nash under dominant-strategy incentives. -/
example [DecidableEq I] (E : QuasilinearEnvironment I T O) (M : DirectMechanism I T O)
    (h : DirectMechanism.IsDSIC E M) (κ : ∀ i, B i → T i) (θ : Profile T)
    (b : Profile B) (hb : ∀ i, κ i (b i) = θ i) :
    (((M.comap κ).inducedBayesianGame E).strategicGameAt θ).IsNash b := by
  rw [Mechanism.inducedBayesianGame_strategicGameAt, QuasilinearEnvironment.utilityGame_comap]
  apply StrategicGame.IsNash.comapActions
  simpa only [hb] using h.isNash E M θ

end MathEconLib.Tests.MechanismGames

end
