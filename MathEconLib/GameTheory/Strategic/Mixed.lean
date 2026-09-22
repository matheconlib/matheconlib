/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import MathEconLib.GameTheory.Strategic.Outcome

/-!
# Independent mixed strategies

Independent randomization assigns each player a probability measure on their action space. The
mixed extension integrates strategic payoffs against the product of those measures. These integrals
represent expected payoffs when the payoff functions are integrable; a nonintegrable function has
Bochner integral zero.

## Main definitions

* `StrategicGame.MixedStrategy` gives profiles of independent action laws.
* `StrategicGame.mixedExtension` integrates payoffs against independent action laws.
* `StrategicGame.IsMixedNash` is Nash equilibrium in the mixed extension.

## Main statements

* `StrategicGame.isMixedNash_iff` characterizes mixed equilibrium by unilateral payoff inequalities.
* `StrategicGame.mixedExtension_eq_ofOutcome` identifies the mixed extension with expected
  utilities on distributions over action profiles.

## Tags

mixed strategies, expected payoffs, nash equilibrium, probability measures
-/

@[expose] public noncomputable section

open MeasureTheory

namespace MathEconLib.GameTheory.StrategicGame

variable {I : Type*} {A : I → Type*}

-- The game parameter identifies the strategic game whose action profiles serve as outcomes.
set_option linter.unusedVariables false in
/-- The action profile itself as the outcome of a game. -/
def outcomeGame (G : StrategicGame I A) : OutcomeGame I A (∀ i, A i) where
  outcome := id

/-- Utilities on action-profile outcomes are the game's strategic payoffs. -/
def payoffStructure (G : StrategicGame I A) : PayoffStructure I (∀ i, A i) where
  payoff := G.payoff

section Measurable

variable [∀ i, MeasurableSpace (A i)]

/-- Each player chooses a probability measure on their action space. -/
abbrev MixedStrategy (A : I → Type*) [∀ i, MeasurableSpace (A i)] :=
  ∀ i, ProbabilityMeasure (A i)

/-- Every player's payoff is measurable on the action-profile space. -/
protected class Measurable (G : StrategicGame I A) : Prop where
  /-- Each payoff function is measurable. -/
  measurable_payoff : ∀ i, Measurable (G.payoff i)

/-- The action-profile outcome map is measurable. -/
instance (G : StrategicGame I A) : G.outcomeGame.Measurable := ⟨measurable_id⟩

/-- Measurable strategic payoffs give measurable utilities on action-profile outcomes. -/
instance (G : StrategicGame I A) [G.Measurable] : G.payoffStructure.Measurable :=
  ⟨Measurable.measurable_payoff⟩

/-- Independent mixed actions yield the Bochner integral of each strategic payoff.

The integral is an expected payoff when the payoff function is integrable against the independent
product law; a nonintegrable function has integral zero. -/
def mixedExtension [Fintype I] (G : StrategicGame I A) :
    StrategicGame I (fun i ↦ ProbabilityMeasure (A i)) where
  payoff i σ := ∫ a, G.payoff i a ∂Measure.pi (fun j ↦ (σ j : Measure (A j)))

/-- Direct expected payoffs agree with the outcome-distribution construction. -/
lemma mixedExtension_eq_ofOutcome [Fintype I] (G : StrategicGame I A) :
    G.mixedExtension = ofOutcome G.outcomeGame.mixed G.payoffStructure.expected := by
  unfold mixedExtension ofOutcome
  congr 1
  funext i σ
  simp [OutcomeGame.mixed, outcomeGame,
    payoffStructure, PayoffStructure.expected]

/-- Every unilateral change of a player's probability law gives at most the incumbent integral
payoff. These are expected-payoff comparisons when the corresponding payoffs are integrable. -/
def IsMixedNash [Fintype I] [DecidableEq I] (G : StrategicGame I A)
    (σ : MixedStrategy A) : Prop :=
  G.mixedExtension.IsNash σ

/-- Mixed Nash compares every unilateral change of a player's probability law with the incumbent
payoff in the mixed extension. -/
@[simp] lemma isMixedNash_iff [Fintype I] [DecidableEq I] (G : StrategicGame I A)
    (σ : MixedStrategy A) :
    G.IsMixedNash σ ↔ ∀ i τ, G.mixedExtension.payoff i (Function.update σ i τ) ≤
      G.mixedExtension.payoff i σ := isNash_iff _ _

end Measurable

section Continuous

variable [∀ i, TopologicalSpace (A i)]

/-- Every player's payoff varies continuously with the full action profile. -/
protected class Continuous (G : StrategicGame I A) : Prop where
  /-- Each payoff function is continuous. -/
  continuous_payoff : ∀ i, Continuous (G.payoff i)

/-- The action-profile outcome map is continuous. -/
instance (G : StrategicGame I A) : G.outcomeGame.Continuous := ⟨continuous_id⟩

/-- Continuous strategic payoffs give continuous utilities on action-profile outcomes. -/
instance (G : StrategicGame I A) [G.Continuous] : G.payoffStructure.Continuous :=
  ⟨Continuous.continuous_payoff⟩

end Continuous

end MathEconLib.GameTheory.StrategicGame
