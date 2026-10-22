/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import MathEconLib.GameTheory.Strategic.Bayesian.Game

/-!
# Action translation and fixed-type games

Successive action translations and fixing a Bayesian game's true type profile give strategic
payoffs at the composite action map. Nash equilibrium pulls back through both translations.

The player, type, action, and payoff spaces may occupy independent universes. These constructions
and equalities apply to arbitrary payoff carriers and arbitrary action maps.

## Main statements

* Fixed-type payoffs after two action translations agree with the original Bayesian payoffs.
* Nash equilibrium pulls back through successive Bayesian action translations at fixed types.

## Tags

strategic games, bayesian games, action translation, type profiles
-/

@[expose] public section

open MathEconLib.GameTheory

universe uI uT uA uB uC uV

namespace MathEconLibTest.GameTheory.ActionMaps

variable {I : Type uI} {T : I → Type uT} {A : I → Type uA} {B : I → Type uB}
  {C : I → Type uC} {V : Type uV}

-- Independent universes and the absence of order assumptions are intentional. This checks that
-- simplification composes across Bayesian action translation and the fixed-type strategic view.
/-- Payoffs after two translations are evaluated at the composite action profile. -/
example (G : BayesianGame I T A V) (κ : (i : I) → B i → A i) (τ : (i : I) → C i → B i)
    (θ : (i : I) → T i) (i : I) (c : (i : I) → C i) :
    (((G.comapActions κ).comapActions τ).strategicGameAt θ).payoff i c =
      G.payoff i (fun j ↦ κ j (τ j (c j))) θ := by
  simp

-- Requiring only LE guards against accidentally strengthening the payoff assumptions. The proof
-- also checks inference when chaining Nash pullbacks across the fixed-type agreement lemma.
/-- Nash equilibrium pulls back through both action translations at fixed true types. -/
example [LE V] [DecidableEq I] (G : BayesianGame I T A V)
    (κ : (i : I) → B i → A i) (τ : (i : I) → C i → B i) (θ : (i : I) → T i)
    (c : (i : I) → C i)
    (h : (G.strategicGameAt θ).IsNash (fun i ↦ κ i (τ i (c i)))) :
    (((G.comapActions κ).comapActions τ).strategicGameAt θ).IsNash c := by
  simpa only [BayesianGame.strategicGameAt_comapActions] using
    (h.comapActions κ).comapActions τ

end MathEconLibTest.GameTheory.ActionMaps

end
