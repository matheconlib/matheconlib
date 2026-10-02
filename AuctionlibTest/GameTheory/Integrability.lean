/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Auctionlib.GameTheory.Strategic.Bayesian.Measurable.PureBNE
public import Auctionlib.GameTheory.Strategic.Mixed
import Mathlib.Analysis.SpecialFunctions.NonIntegrable

/-!
# Nonintegrable incumbent payoffs

A player's type is uniform on `(0, 1]`, their action has no effect, and their payoff is the
reciprocal of their type. This payoff is nonintegrable. Its Bochner integral is zero and the
constant strategy satisfies the bare no-profitable-deviation inequalities. The strategy is not a
Bayesian Nash equilibrium because the incumbent payoff is not integrable.

A second one-player game has action payoff `-|a⁻¹|`. Uniform randomization on `(0, 1]` is Nash for
the raw integral-valued mixed extension, but ceases to be Nash when one is added to all payoffs.
Mixed Nash equilibrium excludes this nonintegrable incumbent in both games.

After subtracting one from the action payoff, pure zero is a mixed Nash equilibrium: Every
integrable deviation has utility at most negative one. The raw integral extension instead prefers
the nonintegrable uniform deviation, whose totalized utility is zero.

## Main definitions

* `uniform`, `prior`: the uniform type distribution and induced one-player profile distribution.
* `game`: action-independent reciprocal-type utility.
* `strategy`: the constant zero action.
* `Mixed.game`, `Mixed.shiftedGame`, `Mixed.loweredGame`: negative reciprocal utility and its
  constant shifts.
* `Mixed.strategy`: uniform action randomization.

## Main statements

* `not_integrable_payoff`: the realized payoff is not integrable under the uniform prior.
* `exAntePayoff_eq_zero`: the nonintegrable payoff has zero Bochner integral.
* `strategy_isEquilibrium`: the constant strategy satisfies the admissible-deviation inequalities.
* `not_isBNE`: the constant strategy is not a Bayesian Nash equilibrium.
* `Mixed.strategy_isNash`, `Mixed.strategy_not_isNash_shifted`: raw integral Nash is sensitive to a
  preference-preserving constant shift.
* `Mixed.not_isMixedNash`, `Mixed.not_isMixedNash_shifted`: nonintegrable uniform randomization is
  excluded from both games' mixed equilibria.
* `Mixed.dirac_zero_isMixedNash_lowered`, `Mixed.dirac_zero_not_isNash_lowered`: pure zero is a
  mixed equilibrium when nonintegrable deviations are excluded from comparison.

## Tags

bayesian nash equilibrium, mixed nash equilibrium, integrability, counterexample
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
def game : BayesianGame Unit (fun _ => ℝ) (fun _ => ℝ) ℝ where
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

namespace Mixed

/-- A single player receives negative absolute reciprocal utility from their action. -/
def game : StrategicGame Unit (fun _ => ℝ) ℝ where
  payoff _ a := -|(a ())⁻¹|

/-- Adding one to every action's utility preserves the player's preferences. -/
def shiftedGame : StrategicGame Unit (fun _ => ℝ) ℝ where
  payoff i a := game.payoff i a + 1

/-- Subtracting one from every action's utility preserves the player's preferences. -/
def loweredGame : StrategicGame Unit (fun _ => ℝ) ℝ where
  payoff i a := game.payoff i a - 1

/-- The player randomizes uniformly on `(0, 1]`. -/
def strategy : StrategicGame.MixedStrategy (fun _ : Unit => ℝ) :=
  fun _ => ⟨uniform, inferInstance⟩

/-- A pure action law concentrated at zero. -/
def zeroAction : ProbabilityMeasure ℝ := ⟨Measure.dirac 0, inferInstance⟩

/-- The one-player independent action law is the uniform profile law. -/
lemma strategy_law : Measure.pi (fun i => (strategy i : Measure ℝ)) = prior := by
  have h := (measurePreserving_piUnique (fun _ : Unit => uniform)).map_eq
  exact (MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq
    (MeasurableEquiv.piUnique (fun _ : Unit => ℝ))).mp h

/-- Independent pure zero action laws concentrate on the zero profile. -/
lemma zeroStrategy_law : Measure.pi (fun _ : Unit => (zeroAction : Measure ℝ)) =
    Measure.dirac (profile 0) := by
  have hlaw := (MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq
    (MeasurableEquiv.piUnique (fun _ : Unit => ℝ))).mp
      (measurePreserving_piUnique (fun _ : Unit => (zeroAction : Measure ℝ))).map_eq
  rw [hlaw]
  change (Measure.dirac (0 : ℝ)).map
    (MeasurableEquiv.piUnique (fun _ : Unit => ℝ)).symm = _
  rw [Measure.map_dirac (MeasurableEquiv.piUnique (fun _ : Unit => ℝ)).symm.measurable]
  rfl

/-- Negative absolute reciprocal utility is nonintegrable under uniform randomization. -/
theorem not_integrable_payoff :
    ¬ Integrable (game.payoff ()) (Measure.pi (fun i => (strategy i : Measure ℝ))) := by
  rw [strategy_law]
  intro h
  apply AuctionlibTest.GameTheory.Integrability.not_integrable_payoff
  have hmeas : AEStronglyMeasurable (fun θ : Unit → ℝ => (θ ())⁻¹) prior :=
    ((measurable_pi_apply ()).inv).aestronglyMeasurable
  change Integrable (fun θ : Unit → ℝ => -|(θ ())⁻¹|) prior at h
  have habs := h.neg
  change Integrable (fun θ : Unit → ℝ => - -|(θ ())⁻¹|) prior at habs
  exact (integrable_norm_iff hmeas).mp (by simpa only [neg_neg, Real.norm_eq_abs] using habs)

/-- A constant shift does not repair the nonintegrable payoff. -/
theorem not_integrable_shiftedPayoff :
    ¬ Integrable (shiftedGame.payoff ())
      (Measure.pi (fun i => (strategy i : Measure ℝ))) := by
  intro h
  apply not_integrable_payoff
  have hsub := h.sub (integrable_const (1 : ℝ))
  change Integrable (fun a => game.payoff () a + 1 - 1)
    (Measure.pi (fun i => (strategy i : Measure ℝ))) at hsub
  simpa only [add_sub_cancel_right] using hsub

/-- Uniform randomization has zero raw integral utility. -/
theorem payoff_eq_zero : game.mixedExtension.payoff () strategy = 0 :=
  integral_undef not_integrable_payoff

/-- Uniform randomization has zero raw integral utility after the constant shift as well. -/
theorem shiftedPayoff_eq_zero : shiftedGame.mixedExtension.payoff () strategy = 0 :=
  integral_undef not_integrable_shiftedPayoff

/-- Totalized integral utility makes the nonintegrable uniform action law a raw Nash equilibrium. -/
theorem strategy_isNash : game.mixedExtension.IsNash strategy := by
  rw [StrategicGame.isNash_iff]
  intro i τ
  cases i
  rw [payoff_eq_zero]
  exact integral_nonpos (fun a => neg_nonpos.mpr (abs_nonneg _))

/-- The pure zero action receives shifted utility one. -/
lemma shiftedPayoff_dirac_zero :
    shiftedGame.mixedExtension.payoff () (fun _ => zeroAction) = 1 := by
  simp [StrategicGame.mixedExtension, zeroStrategy_law, shiftedGame, game, profile]

/-- Adding a constant destroys raw Nash equilibrium despite leaving preferences unchanged. -/
theorem strategy_not_isNash_shifted : ¬ shiftedGame.mixedExtension.IsNash strategy := by
  intro h
  have hle := (StrategicGame.isNash_iff _ _).mp h () zeroAction
  have hupdate : Function.update strategy () zeroAction = (fun _ => zeroAction) := by
    funext i
    cases i
    simp
  rw [hupdate, shiftedPayoff_dirac_zero, shiftedPayoff_eq_zero] at hle
  norm_num at hle

/-- Nonintegrable uniform randomization is excluded from mixed Nash equilibrium. -/
theorem not_isMixedNash : ¬ game.IsMixedNash strategy :=
  fun h => not_integrable_payoff (h.integrable ())

/-- The same incumbent remains excluded after the preference-preserving constant shift. -/
theorem not_isMixedNash_shifted : ¬ shiftedGame.IsMixedNash strategy :=
  fun h => not_integrable_shiftedPayoff (h.integrable ())

/-- Subtracting one also leaves uniform randomization nonintegrable. -/
theorem not_integrable_loweredPayoff :
    ¬ Integrable (loweredGame.payoff ())
      (Measure.pi (fun i => (strategy i : Measure ℝ))) := by
  intro h
  apply not_integrable_payoff
  have hadd := h.add (integrable_const (1 : ℝ))
  change Integrable (fun a => game.payoff () a - 1 + 1)
    (Measure.pi (fun i => (strategy i : Measure ℝ))) at hadd
  simpa only [sub_add_cancel] using hadd

/-- Uniform randomization still has totalized utility zero after subtracting one. -/
theorem loweredPayoff_eq_zero : loweredGame.mixedExtension.payoff () strategy = 0 :=
  integral_undef not_integrable_loweredPayoff

/-- The pure zero action receives utility negative one in the lowered game. -/
lemma loweredPayoff_dirac_zero :
    loweredGame.mixedExtension.payoff () (fun _ => zeroAction) = -1 := by
  simp [StrategicGame.mixedExtension, zeroStrategy_law, loweredGame, game, profile]

/-- Pure zero maximizes expected utility among integrable deviations in the lowered game. -/
theorem dirac_zero_isMixedNash_lowered : loweredGame.IsMixedNash (fun _ => zeroAction) := by
  rw [StrategicGame.isMixedNash_iff]
  constructor
  · intro i
    rw [zeroStrategy_law]
    exact integrable_dirac (by simp)
  · intro i τ hint
    cases i
    rw [loweredPayoff_dirac_zero]
    change (∫ a, loweredGame.payoff () a ∂Measure.pi (fun j =>
      (Function.update (fun _ => zeroAction) () τ j : Measure ℝ))) ≤ -1
    calc
      _ ≤ ∫ _, (-1 : ℝ) ∂Measure.pi (fun j =>
          (Function.update (fun _ => zeroAction) () τ j : Measure ℝ)) :=
        integral_mono hint (integrable_const _) (by
          intro a
          dsimp [loweredGame, game]
          linarith [abs_nonneg ((a ())⁻¹)])
      _ = -1 := by simp

/-- The lowered raw mixed extension ranks uniform randomization above the pure zero action. -/
theorem dirac_zero_not_isNash_lowered :
    ¬ loweredGame.mixedExtension.IsNash (fun _ => zeroAction) := by
  intro h
  have hle := (StrategicGame.isNash_iff _ _).mp h () (strategy ())
  have hupdate : Function.update (fun _ => zeroAction) () (strategy ()) = strategy := by
    funext i
    cases i
    simp
  rw [hupdate, loweredPayoff_eq_zero, loweredPayoff_dirac_zero] at hle
  norm_num at hle

end Mixed

end AuctionlibTest.GameTheory.Integrability

end
