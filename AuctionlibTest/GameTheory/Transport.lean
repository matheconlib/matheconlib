/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Auctionlib.GameTheory.Strategic.Bayesian.Measurable.Comap

/-!
# Measurable action translations with real actions

A single player chooses a real action and receives the negative squared distance from one. The
action one is optimal under every probability distribution of its real type. Constant action
translations identify distinct actions, and restricting the available image can create an
equilibrium whose translated action is not optimal in the original game.

## Main definitions

* `game`: a one-player game with real types and real actions.
* `optimal`: the constant strategy choosing action one.
* `optimalMap` and `restrictedMap`: constant measurable action translations.

## Main statements

* `optimal_isBNE`: the optimal constant action is an equilibrium.
* `translated_isBNE`: equilibrium pulls back through a noninjective measurable action map.
* `restricted_isBNE` and `translated_restricted_not_isBNE`: an equilibrium created by restricting
  actions need not translate to an equilibrium in the original game.

## Tags

bayesian nash equilibrium, action translation, counterexample, real actions
-/

@[expose] public noncomputable section

open MeasureTheory Auctionlib.GameTheory

namespace AuctionlibTest.GameTheory.Transport

/-- One player's utility is maximized at the real action one. -/
def game : BayesianGame Unit (fun _ ↦ ℝ) (fun _ ↦ ℝ) where
  payoff _ a _ := -(a () - 1) ^ 2

/-- Every type chooses the optimal action. -/
def optimal : game.Strategy := fun _ ↦ ⟨fun _ ↦ 1, measurable_const⟩

/-- Every type chooses the real action zero. -/
def zeroStrategy : game.Strategy := fun _ ↦ ⟨fun _ ↦ 0, measurable_const⟩

variable (μ : Measure (Unit → ℝ))

/-- The optimal action gives zero expected payoff. -/
@[simp] lemma exAntePayoff_optimal : game.exAntePayoff μ () optimal = 0 := by
  simp [BayesianGame.exAntePayoff, game, BayesianGame.measurableActionProfile, optimal]

/-- The action zero gives expected payoff negative one. -/
@[simp] lemma exAntePayoff_zeroStrategy [IsProbabilityMeasure μ] :
    game.exAntePayoff μ () zeroStrategy = -1 := by
  simp [BayesianGame.exAntePayoff, game, BayesianGame.measurableActionProfile, zeroStrategy]

variable [IsProbabilityMeasure μ]

/-- Every probability prior admits the constant optimal strategy as a Bayesian Nash equilibrium. -/
theorem optimal_isBNE : game.IsBNE μ optimal := by
  constructor
  · intro i s' _hs'
    cases i
    change game.exAntePayoff μ () s' ≤ game.exAntePayoff μ () optimal
    rw [exAntePayoff_optimal]
    exact integral_nonpos fun θ ↦ neg_nonpos.mpr (sq_nonneg _)
  · intro i
    simp [game, BayesianGame.measurableActionProfile, optimal]

/-- Choosing zero is not a Bayesian Nash equilibrium because choosing one strictly improves it. -/
theorem zero_not_isBNE : ¬ game.IsBNE μ zeroStrategy := by
  intro h
  have hdev := h.isEquilibrium () optimal
    ⟨fun j hj ↦ False.elim (hj (Subsingleton.elim _ _)), (optimal_isBNE μ).integrable ()⟩
  change game.exAntePayoff μ () optimal ≤ game.exAntePayoff μ () zeroStrategy at hdev
  simp only [exAntePayoff_optimal, exAntePayoff_zeroStrategy] at hdev
  norm_num at hdev

/-- The action translation sends every new action to one. -/
def optimalMap : ∀ _ : Unit, {f : ℝ → ℝ // Measurable f} :=
  fun _ ↦ ⟨fun _ ↦ 1, measurable_const⟩

/-- Distinct actions can have the same translated action. -/
lemma optimalMap_not_injective : ¬ Function.Injective (optimalMap ()).1 := by
  intro h
  have hzero_eq_one : (0 : ℝ) = 1 := h (a₁ := 0) (a₂ := 1) rfl
  norm_num at hzero_eq_one

/-- The all-zero profile maps to the original optimal profile. -/
lemma mapActions_optimalMap_zeroStrategy :
    BayesianGame.Strategy.mapActions game optimalMap zeroStrategy = optimal := rfl

/-- Bayesian equilibrium pulls back through a measurable action map that is not injective. -/
theorem translated_isBNE :
    (game.comapActions (fun i ↦ (optimalMap i).1)).IsBNE μ zeroStrategy := by
  apply BayesianGame.IsBNE.comapActions optimalMap
  simpa only [mapActions_optimalMap_zeroStrategy] using optimal_isBNE μ

/-- A restricted action translation sends every action to zero. -/
def restrictedMap : ∀ _ : Unit, {f : ℝ → ℝ // Measurable f} :=
  fun _ ↦ ⟨fun _ ↦ 0, measurable_const⟩

/-- The restricted game gives the same payoff to every strategy, so zero is an equilibrium. -/
theorem restricted_isBNE :
    (game.comapActions (fun i ↦ (restrictedMap i).1)).IsBNE μ zeroStrategy := by
  constructor
  · intro i s' _hs'
    change (game.comapActions (fun i ↦ (restrictedMap i).1)).exAntePayoff μ i s' ≤
      (game.comapActions (fun i ↦ (restrictedMap i).1)).exAntePayoff μ i zeroStrategy
    simp [BayesianGame.exAntePayoff, BayesianGame.comapActions, game, restrictedMap]
  · intro i
    simp [BayesianGame.comapActions, game, restrictedMap]

/-- An equilibrium in a restricted game need not be an equilibrium after translation. -/
theorem translated_restricted_not_isBNE :
    ¬ game.IsBNE μ (BayesianGame.Strategy.mapActions game restrictedMap zeroStrategy) :=
  zero_not_isBNE μ

/-- The constant optimal strategy is an equilibrium when the prior concentrates on type zero. -/
example : game.IsBNE (Measure.dirac (fun _ : Unit ↦ (0 : ℝ))) optimal :=
  optimal_isBNE _

end AuctionlibTest.GameTheory.Transport

end
