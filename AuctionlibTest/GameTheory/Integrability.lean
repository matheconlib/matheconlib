/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Auctionlib.GameTheory.Strategic.Bayesian.Measurable.PureBNE
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.NonIntegrable

/-!
# Nonintegrable incumbent payoffs

A player's type is uniform on `(0, 1]`, their action has no effect, and their payoff is the
reciprocal of their type. This payoff is nonintegrable. Its Bochner integral is zero and the
constant strategy satisfies the bare no-profitable-deviation inequalities. The strategy is not a
Bayesian Nash equilibrium because the incumbent payoff is not integrable.

## Main definitions

* `uniform`, `prior`: the uniform type distribution and induced one-player profile distribution.
* `game`: action-independent reciprocal-type utility.
* `strategy`: the constant zero action.

## Main statements

* `not_integrable_payoff`: the realized payoff is not integrable under the uniform prior.
* `exAntePayoff_eq_zero`: the nonintegrable payoff has zero Bochner integral.
* `strategy_isEquilibrium`: the constant strategy satisfies the admissible-deviation inequalities.
* `not_isBNE`: the constant strategy is not a Bayesian Nash equilibrium.

## Tags

bayesian nash equilibrium, integrability, counterexample
-/

@[expose] public noncomputable section

open MeasureTheory Auctionlib.GameTheory Set

namespace AuctionlibTest.GameTheory.Integrability

/-- Uniform probability on the unit interval, with the left endpoint omitted. -/
def uniform : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)

/-- The interval has unit Lebesgue measure. -/
instance : IsProbabilityMeasure uniform where
  measure_univ := by simp [uniform]

/-- Embed a type into the one-player type profile. -/
def profile (t : ℝ) : Unit → ℝ := fun _ => t

/-- The one-player profile map is measurable. -/
lemma measurable_profile : Measurable profile := measurable_pi_lambda _ fun _ => measurable_id

/-- The common prior induced by the uniform individual type. -/
def prior : Measure (Unit → ℝ) := uniform.map profile

/-- The profile law is a probability measure. -/
instance : IsProbabilityMeasure prior :=
  Measure.isProbabilityMeasure_map measurable_profile.aemeasurable

/-- The player receives reciprocal-type utility independently of their action. -/
def game : BayesianGame Unit (fun _ => ℝ) (fun _ => ℝ) where
  payoff _ _ θ := (θ ())⁻¹

/-- The measurable strategy that chooses zero at every type. -/
def strategy : game.Strategy := fun _ => ⟨fun _ => 0, measurable_const⟩

/-- Reciprocal-type utility is nonintegrable under the uniform common prior. -/
theorem not_integrable_payoff :
    ¬ Integrable (fun θ => game.payoff () (game.measurableActionProfile strategy θ) θ) prior := by
  intro h
  have hint : Integrable (fun t : ℝ => t⁻¹) uniform := by
    have hpayoff_measurable : Measurable (fun θ : Unit → ℝ => (θ ())⁻¹) :=
      (measurable_pi_apply ()).inv
    exact (integrable_map_measure hpayoff_measurable.aestronglyMeasurable
      measurable_profile.aemeasurable).mp h
  have hinterval : IntervalIntegrable (fun t : ℝ => t⁻¹) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr hint
  norm_num at hinterval

/-- The totalized Bochner integral of the incumbent payoff is zero. -/
theorem exAntePayoff_eq_zero : game.exAntePayoff prior () strategy = 0 :=
  integral_undef not_integrable_payoff

/-- Equal action-independent payoffs satisfy the bare equilibrium inequalities. -/
theorem strategy_isEquilibrium : (game.bneProblem prior).IsEquilibrium strategy := by
  intro i s' _hs'
  exact le_rfl

/-- The nonintegrable incumbent is excluded from Bayesian Nash equilibrium. -/
theorem not_isBNE : ¬ game.IsBNE prior strategy :=
  fun h => not_integrable_payoff (h.integrable ())

end AuctionlibTest.GameTheory.Integrability

end
