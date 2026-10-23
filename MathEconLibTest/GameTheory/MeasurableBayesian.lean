/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import MathEconLib.GameTheory.Strategic.Bayesian.Measurable.InterimConverse
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Continuous-type Bayesian equilibrium examples

A player with a real-valued Gaussian type chooses a real action. Utility is the negative squared
action error, capped at one. Truthful action has zero utility and every deviation has nonpositive
utility. Interim optimality and ex-ante equilibrium are equivalent for this game with a non-atomic
prior and continuous action space.

## Main definitions

* `ContinuousBayesianExample.game`: utility given by negative capped squared error.
* `ContinuousBayesianExample.prior`: a standard Gaussian type distribution.
* `ContinuousBayesianExample.truthful`: the strategy that chooses the player's own type.

## Main statements

* `ContinuousBayesianExample.truthful_isBNE`: truthful action is an ex-ante equilibrium.
* `ContinuousBayesianExample.truthful_interim_from_isBNE`: truthful action is an interim best
  response simultaneously against all actions on a set of full marginal measure.

## Tags

bayesian game, continuous types, gaussian prior, interim equilibrium
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace MathEconLibTest.GameTheory.ContinuousBayesianExample

open MathEconLib.GameTheory BayesianPrior

/-- Utility is the negative squared distance between action and type, capped in magnitude at one. -/
def game : BayesianGame Unit (fun _ => ℝ) (fun _ => ℝ) ℝ where
  payoff i a θ := -min 1 ((a i - θ i) ^ 2)

/-- A standard Gaussian law on the single player's real type. -/
def prior : Measure (Unit → ℝ) := (gaussianReal 0 1).map (fun x _ => x)

/-- The Gaussian type prior has total mass one. -/
instance : IsProbabilityMeasure prior :=
  inferInstanceAs (IsProbabilityMeasure ((gaussianReal 0 1).map fun x (_ : Unit) => x))

/-- A selected version of conditional opponent beliefs for the Gaussian prior. -/
def beliefs : ConditionalBeliefs prior := canonicalBeliefs prior

/-- The player chooses their own type. -/
def truthful : game.Strategy := fun _ => ⟨id, measurable_id⟩

/-- Capped squared-error utility is jointly measurable. -/
lemma measurable_payoff :
    ∀ i, Measurable (fun p : (Unit → ℝ) × (Unit → ℝ) => game.payoff i p.1 p.2) := by
  intro i
  unfold game
  fun_prop

/-- Utility has absolute value at most one, uniformly over types and actions. -/
lemma payoff_bounded : ∀ i, ∃ C : ℝ, ∀ a θ, |game.payoff i a θ| ≤ C := by
  intro i
  refine ⟨1, fun a θ => ?_⟩
  change |-min 1 ((a i - θ i) ^ 2)| ≤ 1
  rw [abs_neg, abs_of_nonneg (le_min zero_le_one (sq_nonneg _))]
  exact min_le_left _ _

/-- In this game opponent beliefs have no effect on the conditional utility formula. -/
lemma interimPayoffAction_truthful (i : Unit) (θ a : ℝ) :
    game.interimPayoffAction prior beliefs i θ a truthful = -min 1 ((a - θ) ^ 2) := by
  simp [BayesianGame.interimPayoffAction, BayesianGame.interimPayoffActionIntegrand, game]

/-- Truthful utility is integrable for every player. -/
lemma truthful_integrable : game.IncumbentPayoffsIntegrable prior truthful := by
  intro i
  simp [game, BayesianGame.measurableActionProfile, truthful]

/-- Every action's conditional payoff is integrable on the same conull set. -/
lemma deviations_integrable : game.HasIntegrableInterimDeviations prior beliefs truthful :=
  game.hasIntegrableInterimDeviations_of_bdd prior beliefs measurable_payoff truthful payoff_bounded

/-- Truthful action maximizes utility at every own type. -/
lemma truthful_interim : game.IsAEInterimBestResponse prior beliefs truthful := by
  intro i
  apply Filter.Eventually.of_forall
  intro θ a
  rw [interimPayoffAction_truthful]
  change -min 1 ((a - θ) ^ 2) ≤ game.interimPayoffAction prior beliefs i θ θ truthful
  rw [interimPayoffAction_truthful]
  simp only [sub_self, zero_pow (by decide : 2 ≠ 0), min_eq_right zero_le_one, neg_zero]
  exact neg_nonpos.mpr (le_min zero_le_one (sq_nonneg _))

/-- Almost-everywhere interim optimality yields an ex-ante equilibrium. -/
theorem truthful_isBNE : game.IsBNE prior truthful :=
  game.isBNE_of_ae_interim prior beliefs measurable_payoff truthful truthful_integrable
    truthful_interim

/-- Truthful action is an interim best response simultaneously against all actions on a set of full
marginal measure. -/
theorem truthful_interim_from_isBNE : game.IsAEInterimBestResponse prior beliefs truthful :=
  game.ae_interim_of_isBNE prior beliefs measurable_payoff truthful truthful_isBNE
    deviations_integrable

/-- Ex-ante equilibrium is equivalent to integrable incumbent payoffs and almost-everywhere interim
optimality. -/
example : game.IsBNE prior truthful ↔
    game.IncumbentPayoffsIntegrable prior truthful ∧
      game.IsAEInterimBestResponse prior beliefs truthful :=
  game.isBNE_iff_ae_interim prior beliefs measurable_payoff truthful deviations_integrable

end MathEconLibTest.GameTheory.ContinuousBayesianExample

end
