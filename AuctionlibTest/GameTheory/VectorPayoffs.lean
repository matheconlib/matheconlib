/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Auctionlib.GameTheory.Strategic.Bayesian.FiniteMeasurable
public import Auctionlib.GameTheory.Strategic.Mixed.Finite
public import Auctionlib.Probability.FinDist.Measure
public import Mathlib.Algebra.Order.Monoid.Prod

/-!
# Mixed strategies with vector payoffs

A player evaluates actions by two coordinatewise ordered objectives. The examples define a
strategic game in which one action improves both objectives and a game in which each action favors
a different objective. They also compare finite mixed strategies with probability-measure
strategies, and give a Bayesian game with vector-valued interim payoffs and a finite prior.

## Main definitions

* `game`: A strategic game where choosing `true` improves both payoff coordinates.
* `pure`: The mixed strategy that places probability one on a selected Boolean action.
* `conflicting`: A strategic game where the two Boolean actions favor different coordinates.
* `bayesian`: A Bayesian game where matching the action to the privately observed type improves
  both payoff coordinates.
* `prior`: A finite prior concentrated on the `true` type.
* `truthful`: The pure strategy that matches each type.

## Main statements

* `expectedPayoff_eq` and `conflicting_expectedPayoff`: Formulas for the vector expected payoffs.
* `game_isFiniteMixedNash`: Choosing `true` is a mixed Nash equilibrium when it improves both
  coordinates.
* `conflicting_not_isFiniteMixedNash`: Conflicting coordinate objectives need not admit a mixed
  Nash equilibrium.
* `bayesian_isBNEFin`: Truthful play is a finite Bayesian equilibrium under the coordinatewise
  partial order.

## Tags

mixed strategies, bayesian games, vector payoffs, partial order, expected utility
-/

@[expose] public noncomputable section

open Auctionlib.GameTheory Auctionlib.Probability MeasureTheory

namespace AuctionlibTest.GameTheory.VectorPayoffs

/-- Choosing `true` improves both objectives. -/
def game : StrategicGame Unit (fun _ ↦ Bool) (ℝ × ℝ) where
  payoff _ a := if a () then (1, 2) else (0, 0)

/-- A pure mixed action puts probability one on the selected action. -/
def pure (b : Bool) : FinDist Bool := stdSimplex.vertex (S := ℝ) b

/-- Both expected objectives are proportional to the probability of choosing `true`. -/
lemma expectedPayoff_eq (σ : StrategicGame.FiniteMixedStrategy (fun _ : Unit ↦ Bool)) :
    game.finiteExpectedPayoff () σ = (σ () true, 2 * σ () true) := by
  rw [StrategicGame.finiteExpectedPayoff_eq_sum]
  rw [← (Equiv.funUnique Unit Bool).symm.sum_comp]
  simp [game, Equiv.funUnique, Equiv.piUnique, smul_eq_mul, mul_comm]

/-- Maximizing both objectives rules out every unilateral mixed deviation. -/
theorem game_isFiniteMixedNash : game.IsFiniteMixedNash (fun _ ↦ pure true) := by
  rw [StrategicGame.isFiniteMixedNash_iff]
  intro i τ
  cases i
  rw [expectedPayoff_eq, expectedPayoff_eq]
  have hle : τ true ≤ 1 := stdSimplex.le_one τ true
  simp only [Function.update_self, pure, stdSimplex.vertex_coe, Pi.single_eq_same, mul_one]
  exact ⟨hle, by linarith⟩

/-- The same equilibrium withstands arbitrary probability-measure deviations. -/
example : game.IsMixedNash
    (StrategicGame.toProbability (fun _ ↦ pure true)) :=
  (game.isFiniteMixedNash_iff_isMixedNash _).mp game_isFiniteMixedNash

/-- Vector expected payoffs agree under both representations. -/
example (σ : StrategicGame.FiniteMixedStrategy (fun _ : Unit ↦ Bool)) :
    game.mixedExtension.payoff () (StrategicGame.toProbability σ) =
      (σ () true, 2 * σ () true) := by
  rw [← game.finiteMixedExtension_payoff_eq_mixedExtension]
  exact expectedPayoff_eq σ

/-- A fair lottery averages both payoff coordinates. -/
example : (FinDist.mixture ⟨1 / 2, by constructor <;> norm_num⟩
    (FinDist.pure false) (FinDist.pure true)).expect
    (fun b ↦ if b then (2, 4) else (0, 0) : Bool → ℝ × ℝ) = (1, 2) := by
  rw [FinDist.expect_mixture, FinDist.expect_pure, FinDist.expect_pure]
  norm_num

/-- Finite expected vectors equal their Bochner integral without scalarizing either objective. -/
example (d : FinDist Bool) (f : Bool → ℝ × ℝ) :
    d.expect f = ∫ b, f b ∂d.toMeasure := d.expect_eq_integral f

/-- Each action benefits one objective at the expense of the other. -/
def conflicting : StrategicGame Unit (fun _ ↦ Bool) (ℝ × ℝ) where
  payoff _ a := if a () then (1, 0) else (0, 1)

/-- The two expected objectives are the probabilities of the respective actions. -/
lemma conflicting_expectedPayoff (σ : StrategicGame.FiniteMixedStrategy (fun _ : Unit ↦ Bool)) :
    conflicting.finiteExpectedPayoff () σ = (σ () true, σ () false) := by
  rw [StrategicGame.finiteExpectedPayoff_eq_sum]
  rw [← (Equiv.funUnique Unit Bool).symm.sum_comp]
  simp [conflicting, Equiv.funUnique, Equiv.piUnique, smul_eq_mul]

/-- No mixture can weakly dominate both pure actions in both objectives. -/
theorem conflicting_not_isFiniteMixedNash
    (σ : StrategicGame.FiniteMixedStrategy (fun _ : Unit ↦ Bool)) :
    ¬ conflicting.IsFiniteMixedNash σ := by
  rw [StrategicGame.isFiniteMixedNash_iff]
  intro h
  have ht := h () (pure true)
  have hf := h () (pure false)
  rw [conflicting_expectedPayoff, conflicting_expectedPayoff] at ht hf
  simp [pure, stdSimplex.vertex, Function.update] at ht hf
  have hsum := (σ ()).prop.2
  simp only [Fintype.sum_bool] at hsum
  change σ () true + σ () false = 1 at hsum
  linarith only [ht, hf, hsum]

/-- Probability-measure mixtures also cannot weakly dominate both conflicting pure actions. -/
example (σ : StrategicGame.MixedStrategy (fun _ : Unit ↦ Bool)) : ¬ conflicting.IsMixedNash σ := by
  intro h
  apply conflicting_not_isFiniteMixedNash (StrategicGame.toSimplex σ)
  apply (conflicting.isFiniteMixedNash_iff_isMixedNash _).mpr
  simpa only [StrategicGame.toProbability_toSimplex] using h

/-- Matching the privately observed type maximizes both payoff coordinates. -/
def bayesian : BayesianGame Unit (fun _ ↦ Bool) (fun _ ↦ Bool) (ℝ × ℝ) where
  payoff _ a θ := if a () = θ () then (1, 2) else (0, 0)

/-- Only the `true` type has positive prior probability. -/
def prior : FinDist (Unit → Bool) := FinDist.pure (fun _ ↦ true)

/-- Each type chooses its matching action. -/
def truthful : bayesian.PureStrategy := fun _ t ↦ t

/-- Truthful play is a finite Bayesian equilibrium under the coordinatewise partial order. -/
theorem bayesian_isBNEFin : bayesian.IsBNEFin prior truthful := by
  rw [bayesian.isBNEFin_iff]
  intro i t hp a
  cases i
  have ht : t = true := by
    cases t
    · simp [prior] at hp
    · rfl
  subst t
  rw [show prior = FinDist.pure (fun _ : Unit ↦ true) from rfl]
  rw [bayesian.interimPayoffActionFin_pure, bayesian.interimPayoffActionFin_pure]
  cases a <;> norm_num [bayesian, truthful]

/-- The expanded strategic game uses the same vector-valued interim incentives. -/
example : (bayesian.expandedGame prior).IsNash (bayesian.toExpandedProfile truthful) :=
  (bayesian.isBNEFin_iff_isNash_expandedGame prior truthful).mp bayesian_isBNEFin

/-- The same strategy is an integrable measurable BNE against arbitrary measurable deviations. -/
example : bayesian.IsBNE prior.toMeasure (bayesian.toMeasurableStrategy truthful) :=
  (bayesian.isBNEFin_iff_isBNE prior truthful).mp bayesian_isBNEFin

/-- A null type's interim vector payoff imposes no additional finite incentive constraint. -/
example (a : Bool) : bayesian.interimPayoffActionFin prior () false a truthful = 0 := by
  apply bayesian.interimPayoffActionFin_eq_zero_of_marginal_not_pos
  simp [prior]

end AuctionlibTest.GameTheory.VectorPayoffs

end
